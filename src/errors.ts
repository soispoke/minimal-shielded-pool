/**
 * Errors a user can act on: bad input, a refusal, a node that disagrees. Every
 * CLI prints a UserError's message and exits 1. Any other error is a bug and
 * keeps its stack trace.
 */
export class UserError extends Error {
  constructor(message: string, options?: ErrorOptions) {
    super(message, options);
    this.name = new.target.name;
  }
}

/** Malformed or refused external input: a hex string, number, address, argument or file. */
export class InputError extends UserError {}

/** The pool client refuses to build or send a transaction. */
export class PoolError extends UserError {}

/** A fixture generator refuses its inputs or its output path. */
export class GeneratorError extends UserError {}

/** A note-delivery command fails: bad seed, state file or address. */
export class NotesError extends UserError {}

/** A disclosure receipt cannot be exported or does not verify. */
export class ReceiptError extends UserError {}

/** A repository check (activation, compiler settings, gas profile) fails. */
export class CheckError extends UserError {}
