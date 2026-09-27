import Chain.DispatcherData

/-! A bounded concrete-bytecode rejection proof. Every step is computed from
`Pilot.step`; the trace is a proof certificate, not the interpreter. -/
namespace MSP.Chain.Dispatcher
open Pilot
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- P8: ethrex 247e2dd2c4d4c526dcc64ac1c025bd2319e7a10e,
crates/vm/levm/src/gas_cost.rs, TXPARAM. -/
def pinnedTxparamGas : ℕ := 2

def environment (tail data : List UInt8) (address sender : Word) (txGas : ℕ) : Env :=
  ⟨linkedCode tail, address, data, some ⟨sender⟩, txGas⟩

def errorWord : Word := (0x1cda45c5 : Word) * (2 ^ 227 : ℕ)
def errorMemory : Memory := writeWord (fun _ => 0) 0 errorWord

def machine (persistent : P) (approvals : List ℕ) (stateGas : ℕ)
    (pc : ℕ) (stack : List Word) (executionGas : ℕ) (written : Bool := false) : Machine P :=
  ⟨pc, stack, if written then errorMemory else fun _ => 0,
    if written then 1 else 0, executionGas, stateGas, persistent, approvals⟩

private theorem error_bytes : memorySlice errorMemory 0 4 = [0xe6, 0xd2, 0x2e, 0x28] := by decide
private theorem val_0 : (0 : Word).val = 0 := by decide
private theorem val_4 : (4 : Word).val = 4 := by decide
private theorem val_48 : (48 : Word).val = 48 := by decide
private theorem val_227 : (227 : Word).val = 227 := by decide
private theorem val_607 : (607 : Word).val = 607 := by decide
private theorem val_624 : (624 : Word).val = 624 := by decide

theorem step_0 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 0 [] (extra + txGas + 78) false) =
      .running (machine persistent approvals stateGas 3 [288] (extra + txGas + 75) false) := by
  have hc : 3 ≤ extra + txGas + 78 := by omega
  have hg : (extra + txGas + 78) - 3 = extra + txGas + 75 := by omega
  simp [step, environment, decode_0, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_1 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 3 [288] (extra + txGas + 75) false) =
      .running (machine persistent approvals stateGas 4 [288,288] (extra + txGas + 73) false) := by
  have hc : 2 ≤ extra + txGas + 75 := by omega
  have hg : (extra + txGas + 75) - 2 = extra + txGas + 73 := by omega
  simp [step, environment, decode_3, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_2 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 4 [288,288] (extra + txGas + 73) false) =
      .running (machine persistent approvals stateGas 5 [1] (extra + txGas + 70) false) := by
  have hc : 3 ≤ extra + txGas + 73 := by omega
  have hg : (extra + txGas + 73) - 3 = extra + txGas + 70 := by omega
  simp [step, environment, decode_4, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_3 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 5 [1] (extra + txGas + 70) false) =
      .running (machine persistent approvals stateGas 8 [48,1] (extra + txGas + 67) false) := by
  have hc : 3 ≤ extra + txGas + 70 := by omega
  have hg : (extra + txGas + 70) - 3 = extra + txGas + 67 := by omega
  simp [step, environment, decode_5, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_4 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 8 [48,1] (extra + txGas + 67) false) =
      .running (machine persistent approvals stateGas 48 [] (extra + txGas + 57) false) := by
  have hc : 10 ≤ extra + txGas + 67 := by omega
  have hg : (extra + txGas + 67) - 10 = extra + txGas + 57 := by omega
  simp [step, environment, decode_8, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]
  decide

theorem step_5 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 48 [] (extra + txGas + 57) false) =
      .running (machine persistent approvals stateGas 49 [] (extra + txGas + 56) false) := by
  have hc : 1 ≤ extra + txGas + 57 := by omega
  have hg : (extra + txGas + 57) - 1 = extra + txGas + 56 := by omega
  simp [step, environment, decode_48, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_6 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 49 [] (extra + txGas + 56) false) =
      .running (machine persistent approvals stateGas 50 [address] (extra + txGas + 54) false) := by
  have hc : 2 ≤ extra + txGas + 56 := by omega
  have hg : (extra + txGas + 56) - 2 = extra + txGas + 54 := by omega
  simp [step, environment, decode_49, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_7 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 50 [address] (extra + txGas + 54) false) =
      .running (machine persistent approvals stateGas 52 [2,address] (extra + txGas + 51) false) := by
  have hc : 3 ≤ extra + txGas + 54 := by omega
  have hg : (extra + txGas + 54) - 3 = extra + txGas + 51 := by omega
  simp [step, environment, decode_50, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_8 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 52 [2,address] (extra + txGas + 51) false) =
      .running (machine persistent approvals stateGas 53 [sender,address] (extra + 51) false) := by
  have hc : txGas ≤ extra + txGas + 51 := by omega
  have hg : (extra + txGas + 51) - txGas = extra + 51 := by omega
  simp [step, environment, decode_52, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_9 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 53 [sender,address] (extra + 51) false) =
      .running (machine persistent approvals stateGas 54 [sender-address] (extra + 48) false) := by
  have hc : 3 ≤ extra + 51 := by omega
  have hg : (extra + 51) - 3 = extra + 48 := by omega
  simp [step, environment, decode_53, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_10 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 54 [sender-address] (extra + 48) false) =
      .running (machine persistent approvals stateGas 57 [607,sender-address] (extra + 45) false) := by
  have hc : 3 ≤ extra + 48 := by omega
  have hg : (extra + 48) - 3 = extra + 45 := by omega
  simp [step, environment, decode_54, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_11 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 57 [607,sender-address] (extra + 45) false) =
      .running (machine persistent approvals stateGas 607 [] (extra + 35) false) := by
  have hc : 10 ≤ extra + 45 := by omega
  have hg : (extra + 45) - 10 = extra + 35 := by omega
  simp [step, environment, decode_57, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_12 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 607 [] (extra + 35) false) =
      .running (machine persistent approvals stateGas 608 [] (extra + 34) false) := by
  have hc : 1 ≤ extra + 35 := by omega
  have hg : (extra + 35) - 1 = extra + 34 := by omega
  simp [step, environment, decode_607, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_13 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 608 [] (extra + 34) false) =
      .running (machine persistent approvals stateGas 611 [624] (extra + 31) false) := by
  have hc : 3 ≤ extra + 34 := by omega
  have hg : (extra + 34) - 3 = extra + 31 := by omega
  simp [step, environment, decode_608, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_14 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 611 [624] (extra + 31) false) =
      .running (machine persistent approvals stateGas 624 [] (extra + 23) false) := by
  have hc : 8 ≤ extra + 31 := by omega
  have hg : (extra + 31) - 8 = extra + 23 := by omega
  simp [step, environment, decode_611, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_15 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 624 [] (extra + 23) false) =
      .running (machine persistent approvals stateGas 625 [] (extra + 22) false) := by
  have hc : 1 ≤ extra + 23 := by omega
  have hg : (extra + 23) - 1 = extra + 22 := by omega
  simp [step, environment, decode_624, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_16 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 625 [] (extra + 22) false) =
      .running (machine persistent approvals stateGas 630 [0x1cda45c5] (extra + 19) false) := by
  have hc : 3 ≤ extra + 22 := by omega
  have hg : (extra + 22) - 3 = extra + 19 := by omega
  simp [step, environment, decode_625, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_17 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 630 [0x1cda45c5] (extra + 19) false) =
      .running (machine persistent approvals stateGas 632 [227,0x1cda45c5] (extra + 16) false) := by
  have hc : 3 ≤ extra + 19 := by omega
  have hg : (extra + 19) - 3 = extra + 16 := by omega
  simp [step, environment, decode_630, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_18 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 632 [227,0x1cda45c5] (extra + 16) false) =
      .running (machine persistent approvals stateGas 633 [errorWord] (extra + 13) false) := by
  have hc : 3 ≤ extra + 16 := by omega
  have hg : (extra + 16) - 3 = extra + 13 := by omega
  simp [step, environment, decode_632, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]
  norm_num [errorWord]

theorem step_19 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 633 [errorWord] (extra + 13) false) =
      .running (machine persistent approvals stateGas 634 [0,errorWord] (extra + 11) false) := by
  have hc : 2 ≤ extra + 13 := by omega
  have hg : (extra + 13) - 2 = extra + 11 := by omega
  simp [step, environment, decode_633, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_20 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 634 [0,errorWord] (extra + 11) false) =
      .running (machine persistent approvals stateGas 635 [] (extra + 5) true) := by
  have hc : 6 ≤ extra + 11 := by omega
  have hg : (extra + 11) - 6 = extra + 5 := by omega
  simp [step, environment, decode_634, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]
  rfl

theorem step_21 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 635 [] (extra + 5) true) =
      .running (machine persistent approvals stateGas 637 [4] (extra + 2) true) := by
  have hc : 3 ≤ extra + 5 := by omega
  have hg : (extra + 5) - 3 = extra + 2 := by omega
  simp [step, environment, decode_635, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_22 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 637 [4] (extra + 2) true) =
      .running (machine persistent approvals stateGas 638 [0,4] (extra) true) := by
  have hc : 2 ≤ extra + 2 := by omega
  have hg : (extra + 2) - 2 = extra := by omega
  simp [step, environment, decode_637, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

theorem step_23 (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    step (environment tail data address sender txGas) (machine persistent approvals stateGas 638 [0,4] (extra) true) =
      .reverted (machine persistent approvals stateGas 639 [] (extra) true) [0xe6,0xd2,0x2e,0x28] := by
  have hc : 0 ≤ extra := by omega
  have hg : (extra) - 0 = extra := by omega
  simp [step, environment, decode_638, execute, machine, charged, advance,
    hdata, hc, hg, val_0, val_4, val_48, val_227, val_607, val_624,
    push_0, push_5, push_50, push_54, push_608, push_625, push_630, push_633,
    push_635, push_637, jump_48, jump_607, jump_624, sub_ne_zero.mpr hne,
    expansionCost, wordsFor, memoryCost, error_bytes]

/-- The bytecode executes exactly the certified 24-opcode sender rejection path.
The immutable tail is arbitrary; no bytes in it are executed or inspected. -/
theorem sender_mismatch (tail data : List UInt8) (address sender : Word)
    (txGas extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    run (environment tail data address sender txGas) 24
      (machine persistent approvals stateGas 0 [] (extra + txGas + 78) false) =
    .reverted (machine persistent approvals stateGas 639 [] extra true)
      [0xe6, 0xd2, 0x2e, 0x28] := by
  simp only [run,
    step_0 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_1 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_2 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_3 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_4 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_5 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_6 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_7 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_8 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_9 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_10 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_11 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_12 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_13 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_14 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_15 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_16 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_17 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_18 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_19 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_20 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_21 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_22 tail data address sender txGas extra stateGas persistent approvals hdata hne,
    step_23 tail data address sender txGas extra stateGas persistent approvals hdata hne]

/-- P8's TXPARAM charge is 2: exactly 80 execution gas, no state gas,
persistent writes or new approvals. Entry and intrinsic gas are excluded. -/
theorem sender_mismatch_pinned (tail data : List UInt8) (address sender : Word)
    (extra stateGas : ℕ) (persistent : P) (approvals : List ℕ)
    (hdata : data.length = 288) (hne : sender ≠ address) :
    run (environment tail data address sender pinnedTxparamGas) 24
      (machine persistent approvals stateGas 0 [] (extra + 80) false) =
    .reverted (machine persistent approvals stateGas 639 [] extra true)
      [0xe6, 0xd2, 0x2e, 0x28] := by
  simpa [pinnedTxparamGas, Nat.add_assoc] using
    sender_mismatch tail data address sender 2 extra stateGas persistent approvals hdata hne

end MSP.Chain.Dispatcher
