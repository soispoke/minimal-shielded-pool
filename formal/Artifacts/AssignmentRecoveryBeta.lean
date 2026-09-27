import Artifacts.AssignmentRecoveryBetaCertificates0
import Artifacts.AssignmentRecoveryBetaCertificates1
import Artifacts.AssignmentRecoveryBetaCertificates2
import Artifacts.AssignmentRecoveryBetaCertificates3
import Artifacts.AssignmentRecoveryBetaCertificates4
import Artifacts.AssignmentRecoveryBetaCertificates5
import Artifacts.AssignmentRecoveryBetaCertificates6
import Artifacts.AssignmentRecoveryBetaCertificates7
import Artifacts.AssignmentRecoveryBetaCertificates8
import Artifacts.AssignmentRecoveryBetaCertificates9
import Artifacts.AssignmentRecoveryBetaCertificates10
import Artifacts.AssignmentRecoveryBetaCertificates11
import Artifacts.AssignmentRecoveryBetaCertificates12
import Artifacts.AssignmentRecoveryBetaCertificates13
import Artifacts.AssignmentRecoveryBetaCertificates14
import Artifacts.AssignmentRecoveryBetaCertificates15
import Artifacts.AssignmentRecoveryBetaCertificates16
import Artifacts.AssignmentRecoveryBetaCertificates17
import Artifacts.AssignmentRecoveryBetaCertificates18
import Artifacts.AssignmentRecoveryBetaCertificates19

/-! An explicit assignment realizing all 153 actual beta fifth-output LCs.
Square/fourth wires and semantic optimized traces are separate obligations. -/

namespace MSP.Artifacts.AssignmentRecoveryBeta

open BetaGates AssignmentRecovery AssignmentRecoveryBetaData AssignmentRecoveryBetaCertificates

set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

theorem certificates (t : Fin 153) :
    normalize (substitute (BetaGatesData.output t) plan.replacement) =
      normalize [(t.val + 1, 1)] := by
  fin_cases t
  · exact output0
  · exact output1
  · exact output2
  · exact output3
  · exact output4
  · exact output5
  · exact output6
  · exact output7
  · exact output8
  · exact output9
  · exact output10
  · exact output11
  · exact output12
  · exact output13
  · exact output14
  · exact output15
  · exact output16
  · exact output17
  · exact output18
  · exact output19
  · exact output20
  · exact output21
  · exact output22
  · exact output23
  · exact output24
  · exact output25
  · exact output26
  · exact output27
  · exact output28
  · exact output29
  · exact output30
  · exact output31
  · exact output32
  · exact output33
  · exact output34
  · exact output35
  · exact output36
  · exact output37
  · exact output38
  · exact output39
  · exact output40
  · exact output41
  · exact output42
  · exact output43
  · exact output44
  · exact output45
  · exact output46
  · exact output47
  · exact output48
  · exact output49
  · exact output50
  · exact output51
  · exact output52
  · exact output53
  · exact output54
  · exact output55
  · exact output56
  · exact output57
  · exact output58
  · exact output59
  · exact output60
  · exact output61
  · exact output62
  · exact output63
  · exact output64
  · exact output65
  · exact output66
  · exact output67
  · exact output68
  · exact output69
  · exact output70
  · exact output71
  · exact output72
  · exact output73
  · exact output74
  · exact output75
  · exact output76
  · exact output77
  · exact output78
  · exact output79
  · exact output80
  · exact output81
  · exact output82
  · exact output83
  · exact output84
  · exact output85
  · exact output86
  · exact output87
  · exact output88
  · exact output89
  · exact output90
  · exact output91
  · exact output92
  · exact output93
  · exact output94
  · exact output95
  · exact output96
  · exact output97
  · exact output98
  · exact output99
  · exact output100
  · exact output101
  · exact output102
  · exact output103
  · exact output104
  · exact output105
  · exact output106
  · exact output107
  · exact output108
  · exact output109
  · exact output110
  · exact output111
  · exact output112
  · exact output113
  · exact output114
  · exact output115
  · exact output116
  · exact output117
  · exact output118
  · exact output119
  · exact output120
  · exact output121
  · exact output122
  · exact output123
  · exact output124
  · exact output125
  · exact output126
  · exact output127
  · exact output128
  · exact output129
  · exact output130
  · exact output131
  · exact output132
  · exact output133
  · exact output134
  · exact output135
  · exact output136
  · exact output137
  · exact output138
  · exact output139
  · exact output140
  · exact output141
  · exact output142
  · exact output143
  · exact output144
  · exact output145
  · exact output146
  · exact output147
  · exact output148
  · exact output149
  · exact output150
  · exact output151
  · exact output152

/-- Arbitrary fifth-output values are realized without any satisfaction premise. -/
theorem realizes (ambient : Assignment) (desired : ℕ → F) (t : Fin 153) :
    eval (BetaGatesData.output t) (plan.apply ambient desired) = desired t.val :=
  plan.realizes _ _ t.isLt (certificates t) ambient desired

/-- The 153 affine wires are the complete write set of this construction. -/
theorem preserves (ambient : Assignment) (desired : ℕ → F) (wire : ℕ)
    (h : wire ≠ 1 ∧ (wire < 111 ∨ 263 ≤ wire)) :
    plan.apply ambient desired wire = ambient wire := by
  apply plan.preserves ambient desired wire
  rw [written_eq]
  simp only [List.mem_cons, List.mem_range', not_or]
  constructor
  · exact h.1
  · omega

end MSP.Artifacts.AssignmentRecoveryBeta
