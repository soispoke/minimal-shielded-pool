/**
 * The command-line parser every CLI uses. An unknown or abbreviated flag stops the run with exit
 * status 2 before any file or RPC is touched (a mistyped --dry-run must not send a transaction),
 * --flag=value equals --flag value, and everything after "--" is positional.
 *
 * Any local user can read a process's arguments, and a parser error repeats what it rejects, so
 * every parser message has each run of 64 or more hex digits redacted: a key pasted anywhere on
 * the command line is refused without being echoed.
 */
import { inspect } from "node:util";

import { parseDec, uintFromText } from "../bytes.ts";
import { InputError, UserError } from "../errors.ts";

/** The text with every run of 64 or more hex digits, which may be a key, redacted. */
export function redact(text: string): string {
  return text.replace(/(0x)?[0-9a-fA-F]{64,}/g, "<redacted>");
}

export interface PositionalSpec {
  readonly name: string;
  readonly choices?: readonly string[];
  readonly help?: string;
}

/**
 * An option: a flag (true when given), one value (the last one given wins), or a repeated value
 * collected in order. "int" reads 0x hex or decimal without leading zeros (010 could mean ten or
 * eight); "decimal" reads decimal digits only. Neither takes a sign.
 */
export interface OptionSpec {
  readonly kind: "flag" | "string" | "int" | "decimal" | "append";
  readonly required?: boolean;
  readonly help?: string;
}

export interface CliSpec {
  readonly prog: string;
  readonly description?: string;
  readonly positionals?: readonly PositionalSpec[];
  readonly options?: { readonly [flag: `--${string}`]: OptionSpec };
  /** Refuses the argument at this index unless it starts with "--", before parsing (exit 1). */
  readonly refuseBeforeParsing?: { readonly index: number; readonly message: string };
}

type Positionals<S extends CliSpec> = S extends { positionals: readonly PositionalSpec[] }
  ? S["positionals"][number]
  : never;
type Options<S extends CliSpec> = S extends { options: infer O } ? O : {};
type OptionValue<O> = O extends { kind: "flag" }
  ? boolean
  : O extends { kind: "append" }
    ? string[]
    : (O extends { kind: "int" | "decimal" } ? bigint : string) | Missing<O>;
type Missing<O> = O extends { required: true } ? never : undefined;

export interface ParsedArgs<S extends CliSpec> {
  readonly positionals: {
    readonly [P in Positionals<S> as P["name"]]: P extends { choices: readonly (infer C)[] }
      ? C
      : string;
  };
  readonly options: { readonly [K in keyof Options<S>]: OptionValue<Options<S>[K]> };
}

/** A malformed command line: exit status 2, with the usage line and the redacted message. */
export class UsageError extends UserError {
  /** Everything to write to stderr. */
  readonly text: string;

  constructor(spec: CliSpec, message: string) {
    super(redact(message));
    this.text = `${usage(spec)}\n${spec.prog}: error: ${this.message}\n`;
  }
}

/** -h or --help: the help goes to stdout and the CLI exits 0. */
export class HelpRequested extends UserError {
  readonly text: string;

  constructor(spec: CliSpec) {
    super(help(spec));
    this.text = this.message;
  }
}

/** Parses argv against spec, or throws UsageError, HelpRequested or InputError. */
export function parseArgs<const S extends CliSpec>(
  spec: S,
  argv: readonly string[],
): ParsedArgs<S> {
  const refusal = spec.refuseBeforeParsing;
  if (refusal && argv.length > refusal.index && !argv[refusal.index].startsWith("--")) {
    throw new InputError(refusal.message);
  }
  const positionalSpecs = spec.positionals ?? [];
  const optionSpecs: { readonly [flag: string]: OptionSpec | undefined } = spec.options ?? {};
  const fail: Fail = (message) => {
    throw new UsageError(spec, message);
  };
  // No CLI takes a negative number, so anything but "-" that starts with "-" is an option.
  const isPositional = (arg: string) => !arg.startsWith("-") || arg === "-";

  const positionals: string[] = [];
  const values = new Map<string, unknown>();
  const unrecognized: string[] = [];
  let onlyPositionals = false;
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === "--" && !onlyPositionals) {
      onlyPositionals = true;
    } else if (onlyPositionals || isPositional(arg)) {
      const target = positionalSpecs[positionals.length];
      if (target === undefined) unrecognized.push(arg);
      else positionals.push(checkChoice(target.name, arg, fail, target.choices));
    } else if (arg === "-h" || arg === "--help") {
      throw new HelpRequested(spec);
    } else {
      const equals = arg.indexOf("=");
      const flag = equals > 0 ? arg.slice(0, equals) : arg;
      const option = Object.hasOwn(optionSpecs, flag) ? optionSpecs[flag] : undefined;
      let value = equals > 0 ? arg.slice(equals + 1) : undefined;
      if (option === undefined) {
        unrecognized.push(arg);
      } else if (option.kind === "flag") {
        if (value !== undefined) {
          fail(`argument ${flag}: ignored explicit argument ${quote(value)}`);
        }
        values.set(flag, true);
      } else {
        if (value === undefined) {
          if (i + 1 === argv.length || !isPositional(argv[i + 1])) {
            fail(`argument ${flag}: expected one argument`);
          }
          value = argv[++i];
        }
        if (option.kind === "append") {
          values.set(flag, [...((values.get(flag) as string[] | undefined) ?? []), value]);
        } else {
          values.set(flag, readValue(flag, option.kind, value, fail));
        }
      }
    }
  }

  const missing = positionalSpecs.slice(positionals.length).map((p) => p.name);
  for (const [flag, option] of Object.entries(optionSpecs)) {
    if (option?.required && !values.has(flag)) missing.push(flag);
  }
  if (missing.length > 0) fail(`the following arguments are required: ${missing.join(", ")}`);
  if (unrecognized.length > 0) fail(`unrecognized arguments: ${unrecognized.join(" ")}`);

  const options: Record<string, unknown> = {};
  for (const [flag, option] of Object.entries(optionSpecs)) {
    const value = values.get(flag);
    options[flag] =
      option?.kind === "flag" ? value === true : option?.kind === "append" ? (value ?? []) : value;
  }
  return {
    positionals: Object.fromEntries(positionalSpecs.map((p, i) => [p.name, positionals[i]])),
    options,
  } as ParsedArgs<S>;
}

type Fail = (message: string) => never;

function checkChoice(name: string, value: string, fail: Fail, choices?: readonly string[]): string {
  if (choices && !choices.includes(value)) {
    const listed = choices.map(quote).join(", ");
    fail(`argument ${name}: invalid choice: ${quote(value)} (choose from ${listed})`);
  }
  return value;
}

// Integers are decimal or 0x hex only: signs, spaces, underscores and 0o/0b forms are refused,
// and a negative epoch, slot or index fails here rather than later.
function readValue(flag: string, kind: OptionSpec["kind"], raw: string, fail: Fail) {
  if (kind === "string") return raw;
  if (kind === "decimal") {
    try {
      return parseDec(raw, flag);
    } catch {
      return fail(`argument ${flag}: invalid int value: ${quote(raw)}`);
    }
  }
  const value = uintFromText(raw);
  if (value !== null) return value;
  if (raw.startsWith("-") && uintFromText(raw.slice(1)) !== null) {
    fail(`argument ${flag}: must be non-negative: ${raw}`);
  }
  return fail(`argument ${flag}: not an integer: ${raw}`);
}

// Quotes a rejected value so that spaces and control characters stay visible.
function quote(text: string): string {
  return JSON.stringify(text);
}

/** How help and usage show an argument: a choice list, the flag, or the flag and its value. */
function invocation(name: string, choices?: readonly string[], option?: OptionSpec): string {
  if (choices) return `{${choices.join(",")}}`;
  if (option === undefined || option.kind === "flag") return name;
  return `${name} ${name.slice(2).replaceAll("-", "_").toUpperCase()}`;
}

/** The usage line: the program, [options], then any required options and the positionals. */
function usage(spec: CliSpec): string {
  const required = Object.entries(spec.options ?? {})
    .filter(([, option]) => option.required)
    .map(([flag, option]) => invocation(flag, undefined, option));
  const positionals = (spec.positionals ?? []).map((p) => invocation(p.name, p.choices));
  return ["usage:", spec.prog, "[options]", ...required, ...positionals].join(" ");
}

type Row = [shown: string, text?: string];

/** The usage line, the description, then one row per argument with its help beside it. */
function help(spec: CliSpec): string {
  const positionals = (spec.positionals ?? []).map((p): Row => {
    return [p.name, p.help ?? (p.choices && `one of ${p.choices.join(", ")}`)];
  });
  const options: Row[] = [
    ["-h, --help", "show this help message and exit"],
    ...Object.entries(spec.options ?? {}).map(([flag, option]): Row => {
      return [invocation(flag, undefined, option), option.help];
    }),
  ];
  const width = Math.max(...[...positionals, ...options].map(([shown]) => shown.length));
  const section = (title: string, rows: Row[]) =>
    rows.length === 0
      ? []
      : [
          "",
          title,
          ...rows.map(([shown, text = ""]) => `  ${shown.padEnd(width)}  ${text}`.trimEnd()),
        ];
  const description = spec.description ? ["", spec.description] : [];
  const sections = [...section("arguments:", positionals), ...section("options:", options)];
  return [usage(spec), ...description, ...sections].join("\n") + "\n";
}

/**
 * Runs a CLI's main and turns its refusals into exit statuses, so that no CLI calls process.exit
 * and piped stdout always flushes: help exits 0 on stdout, a usage error 2, and any other
 * UserError 1 with its message on stderr. A failed system call, such as a file that cannot be
 * read, is reported in the same one line, and is always redacted as parser messages are: its
 * path came from the command line, where a key may have been pasted. Anything else is a bug,
 * printed with its stack trace.
 *
 * With redactErrors, which pool, notes, smoke and nonce-race set, all error output is redacted:
 * a key typed where a path or address belongs passes the parser and would come back in a
 * refusal. disclosure prints refusals as they are, since they name commitments users need.
 * prefix, which notes sets, begins each refusal and system error.
 */
export async function runCli(
  main: () => void | Promise<void>,
  options: { redactErrors?: boolean; prefix?: string } = {},
): Promise<void> {
  const { redactErrors = false, prefix = "" } = options;
  // Exiting through process.exit runs "exit" listeners, which release state locks; Node's
  // default handling of these signals would skip them. SIGHUP comes from a closed terminal.
  process.once("SIGINT", () => process.exit(130));
  process.once("SIGTERM", () => process.exit(143));
  process.once("SIGHUP", () => process.exit(129));
  try {
    await main();
  } catch (error) {
    if (error instanceof HelpRequested) {
      process.stdout.write(error.text);
    } else if (error instanceof UsageError) {
      process.stderr.write(error.text);
      process.exitCode = 2;
    } else {
      const system = error instanceof Error && "syscall" in error;
      const refusal = error instanceof UserError || system;
      const text = refusal ? prefix + (error as Error).message : inspect(error);
      process.stderr.write((redactErrors || system ? redact(text) : text) + "\n");
      process.exitCode = 1;
    }
  }
}
