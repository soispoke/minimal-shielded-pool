# Dispatcher rejection pilot

This is a bounded proof of the committed dispatcher's sender-mismatch path.
The interpreter executes concrete bytes with a stack, byte memory, jump checks,
execution gas and carried persistent state. It refuses opcodes outside its
implemented subset. It does not define any opaque declaration in `Spec/Evm.lean`.

The checked `MSP.Chain.Dispatcher.sender_mismatch_pinned` theorem starts at PC0
with an empty stack and memory, 288
calldata bytes, a frame-transaction context, and a sender different from the
executing address. It follows 24 actual instructions through `TXPARAM(2)` at
PC52 and returns the four error bytes `e6d22e28` through `REVERT` at PC638.
Its execution cost is 78 plus the TXPARAM charge, 80 for the pinned client.
It preserves persistent state, approvals and state gas. Transaction intrinsic
gas and frame-entry account access are outside the interpreter.

`DispatcherData.lean` contains the exact 1624 initcode bytes. Ordinary kernel
evaluation checks the 1565-byte slice at offset 59, the constructor's matching
length/offset PUSH operands, every instruction and immediate on the path, and
its three jump destinations. These facts hold with any appended immutable
tail, including D12's 64-byte pair of linked address words. The slice fact does
not prove execution of the complete constructor or creation transaction.

`Pilot.lean` adapts the opcode equations, stack order and memory/gas equations
from Nethermind's EVMYulLean, commit
`047f63070309f436b66c61e276ab3b6d1169265a`. The relevant upstream files are
`EvmYul/UInt256.lean`, `Data/Stack.lean`, `MachineStateOps.lean`,
`Semantics.lean` and `EVM/{Instr,Gas,GasConstants,PrimOps,Semantics}.lean`.
The original copyright is 2024 Demerzel Solutions Limited (t/a Nethermind);
the Apache-2.0 license from that commit is preserved as `UPSTREAM-LICENSE.txt`.
The port uses modular integers for 256-bit words and pure functional byte
memory. Its terminating jump scan advances over unknown bytes and skips PUSH
data. Its decoder distinguishes missing code from unsupported in-code bytes.
These changes remove upstream opaque FFI memory operations and the upstream
default-to-STOP behavior on failed instruction decoding.

The TXPARAM extension follows ethrex commit
`247e2dd2c4d4c526dcc64ac1c025bd2319e7a10e`,
`crates/vm/levm/src/opcode_handlers/frame_tx.rs:336` and `:734`: a frame context
is required and selector 2 returns its transaction sender. The charge is 2 in
`crates/vm/levm/src/gas_cost.rs:69`; that file's SHA256 is
`60b26621dff788b2303ef347860f32c8b3d728be52e01d76b3a364a1e9f01d72`.
The frame handler SHA256 is
`dc5c51544d687e61b16400541e48cade210e2c7d89bcd28318cf1650953719b9`.
The present context is an explicit execution input, not a proof that an entire
signed transaction satisfies EIP-8141's validation rules.

Run from `formal/`:

```sh
python3 tools/dispatcher_pilot.py --check
lake build Chain
```

Both commands pass. The `Chain` target builds all four modules on Lean 4.35.0-rc3.
`sender_mismatch` leaves the TXPARAM charge as a parameter;
`sender_mismatch_pinned` substitutes the pinned charge 2. The public theorem
explicitly returns the same persistent state, approvals and state-gas balance,
with exactly 80 fewer execution gas. The step lemmas certify each intermediate
PC, stack, memory and gas balance.

The generator checks the activation-pinned initcode text SHA256 before exporting
any byte declarations. `PilotChecks.lean` checks unknown-op rejection, missing
code STOP, PUSH-payload jump rejection, scanning beyond unknown bytes, truncated
PUSH padding, memory gas and missing-frame rejection. No `native_decide`, FFI,
new axioms or assumed execution results are used.

The complete EVM/FrameTx semantics, constructor/deployment execution, successful
approval path, state-gas charging for effectful instructions, and the chain
refinement remain separate obligations.
