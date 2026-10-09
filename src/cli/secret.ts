/**
 * Reading a key or seed. Any local user can read a process's arguments, so secrets never come
 * from the command line: on a terminal they are typed at a prompt that does not echo them,
 * otherwise they are the first line of standard input (a pipe from a keystore or `printf`).
 */
import { StringDecoder } from "node:string_decoder";
import type { ReadStream } from "node:tty";

/**
 * One line of secret input, without its line ending. On a terminal the prompt goes to stderr,
 * so stdout stays parseable, and nothing typed is echoed; Ctrl-C aborts with exit status 130.
 * Otherwise the first line of stdin, or "" when stdin is empty.
 */
export function readSecretLine(prompt: string): Promise<string> {
  const stdin = process.stdin;
  return stdin.isTTY ? readHidden(stdin, prompt) : readFirstLine(stdin);
}

function readFirstLine(stdin: NodeJS.ReadStream): Promise<string> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    const finish = (bytes: Buffer) => {
      stdin.off("data", onData).off("end", onEnd).off("error", onError);
      // Nothing else reads stdin, and a writer that keeps the pipe open must not keep the
      // process alive.
      stdin.destroy();
      // A byte order mark is kept, not stripped: the caller sees the line exactly as sent.
      resolve(new TextDecoder("utf-8", { ignoreBOM: true }).decode(bytes));
    };
    const onData = (chunk: Buffer) => {
      chunks.push(chunk);
      const all = Buffer.concat(chunks);
      const end = all.indexOf(0x0a);
      if (end >= 0) finish(all.subarray(0, end));
    };
    const onEnd = () => finish(Buffer.concat(chunks));
    const onError = (error: Error) => {
      stdin.off("data", onData).off("end", onEnd);
      reject(error);
    };
    stdin.on("data", onData).once("end", onEnd).once("error", onError);
  });
}

function readHidden(stdin: ReadStream, prompt: string): Promise<string> {
  process.stderr.write(prompt);
  const wasRaw = stdin.isRaw;
  // Raw mode turns echo off and delivers each key as typed, Ctrl-C included.
  stdin.setRawMode(true);
  return new Promise((resolve, reject) => {
    const decoder = new StringDecoder("utf8");
    let line = "";
    const restore = () => {
      stdin.off("data", onData).off("end", onEnd).off("error", onError);
      stdin.setRawMode(wasRaw);
      stdin.pause();
      // The Enter key was not echoed either.
      process.stderr.write("\n");
    };
    const onData = (chunk: Buffer) => {
      for (const key of decoder.write(chunk)) {
        if (key === "\r" || key === "\n" || key === "\u0004") {
          restore();
          resolve(line);
          return;
        }
        if (key === "\u0003") {
          restore();
          process.exit(130);
        }
        if (key === "\u007f" || key === "\b") line = Array.from(line).slice(0, -1).join("");
        else if (key === "\u0015") line = "";
        else if (key >= " ") line += key;
      }
    };
    const onEnd = () => {
      restore();
      resolve(line);
    };
    const onError = (error: Error) => {
      restore();
      reject(error);
    };
    stdin.on("data", onData).once("end", onEnd).once("error", onError);
    stdin.resume();
  });
}
