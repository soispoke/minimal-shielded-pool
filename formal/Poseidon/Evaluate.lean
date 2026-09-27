import Poseidon.Hash

/-! Executable differential-test driver. Evaluation results are tests, not
kernel-checked theorems about constants or the circuit. -/

open MSP

private def evaluate (inputs : List Nat) : Except String Nat :=
  match inputs with
  | [a, b] => .ok (Poseidon.hash2 a b).val
  | [a, b, c] => .ok (Poseidon.hash3 a b c).val
  | _ =>
      if inputs.length = 10 then
        .ok (Poseidon.hash10 fun i => (inputs[i.val]?.getD 0 : F)).val
      else .error "expected 2, 3 or 10 inputs"

/-- Read one space-separated input vector, or `zero <depth>`, per line and emit
one decimal output per line. Malformed input or an unsupported arity is an error. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: Evaluate.lean <input-vectors.txt>")
  let contents ← IO.FS.readFile path
  for line in contents.splitOn "\n" do
    if !line.isEmpty then
      match line.splitOn " " with
      | ["zero", depth] =>
          let some n := depth.toNat? | throw (IO.userError "invalid zero-hash depth")
          IO.println (Poseidon.zeroHash n).val
      | tokens =>
          let mut values := []
          for token in tokens do
            let some n := token.toNat? | throw (IO.userError s!"invalid natural number: {token}")
            values := values ++ [n]
          match evaluate values with
          | .ok out => IO.println out
          | .error message => throw (IO.userError message)
