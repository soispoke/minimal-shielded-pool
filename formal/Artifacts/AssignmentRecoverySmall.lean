import Artifacts.AssignmentRecoverySmallCertificates0
import Artifacts.AssignmentRecoverySmallCertificates1
import Artifacts.AssignmentRecoverySmallCertificates2
import Artifacts.AssignmentRecoverySmallCertificates3
import Artifacts.AssignmentRecoverySmallCertificates4
import Artifacts.AssignmentRecoverySmallCertificates5
import Artifacts.AssignmentRecoverySmallCertificates6
import Artifacts.AssignmentRecoverySmallCertificates7
import Artifacts.AssignmentRecoverySmallCertificates8
import Artifacts.AssignmentRecoverySmallCertificates9
import Artifacts.AssignmentRecoverySmallCertificates10
import Artifacts.AssignmentRecoverySmallCertificates11
import Artifacts.AssignmentRecoverySmallCertificates12
import Artifacts.AssignmentRecoverySmallCertificates13
import Artifacts.AssignmentRecoverySmallCertificates14
import Artifacts.AssignmentRecoverySmallCertificates15
import Artifacts.AssignmentRecoverySmallCertificates16
import Artifacts.AssignmentRecoverySmallCertificates17
import Artifacts.AssignmentRecoverySmallCertificates18
import Artifacts.AssignmentRecoverySmallCertificates19
import Artifacts.AssignmentRecoverySmallCertificates20
import Artifacts.AssignmentRecoverySmallCertificates21
import Artifacts.AssignmentRecoverySmallCertificates22
import Artifacts.AssignmentRecoverySmallCertificates23
import Artifacts.AssignmentRecoverySmallCertificates24
import Artifacts.AssignmentRecoverySmallCertificates25
import Artifacts.AssignmentRecoverySmallCertificates26
import Artifacts.AssignmentRecoverySmallCertificates27
import Artifacts.AssignmentRecoverySmallCertificates28
import Artifacts.AssignmentRecoverySmallCertificates29
import Artifacts.AssignmentRecoverySmallCertificates30
import Artifacts.AssignmentRecoverySmallCertificates31
import Artifacts.AssignmentRecoverySmallCertificates32
import Artifacts.AssignmentRecoverySmallCertificates33
import Artifacts.AssignmentRecoverySmallCertificates34
import Artifacts.AssignmentRecoverySmallCertificates35
import Artifacts.AssignmentRecoverySmallCertificates36
import Artifacts.AssignmentRecoverySmallCertificates37
import Artifacts.AssignmentRecoverySmallCertificates38
import Artifacts.AssignmentRecoverySmallCertificates39
import Artifacts.AssignmentRecoverySmallCertificates40
import Artifacts.AssignmentRecoverySmallCertificates41
import Artifacts.AssignmentRecoverySmallCertificates42
import Artifacts.AssignmentRecoverySmallCertificates43
import Artifacts.AssignmentRecoverySmallCertificates44
import Artifacts.AssignmentRecoverySmallCertificates45
import Artifacts.AssignmentRecoverySmallCertificates46
import Artifacts.AssignmentRecoverySmallCertificates47
import Artifacts.AssignmentRecoverySmallCertificates48
import Artifacts.AssignmentRecoverySmallCertificates49
import Artifacts.AssignmentRecoverySmallCertificates50
import Artifacts.AssignmentRecoverySmallCertificates51
import Artifacts.AssignmentRecoverySmallCertificates52
import Artifacts.AssignmentRecoverySmallCertificates53

/-! Explicit complete affine recovery for every actual small-hash output LC.
No satisfaction premise, hash equation or witness-generator behavior is assumed. -/

namespace MSP.Artifacts.AssignmentRecoverySmall

open BetaGates AssignmentRecovery AssignmentRecoverySmallData SmallHashGatesData
open AssignmentRecoverySmallCertificates
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

theorem realizes (i : Fin 54) (ambient : Assignment) (desired : ℕ → F)
    (t : Fin (gate i).tripleCount) :
    eval (SmallHashGates.output (gate i) t) ((plan i).apply ambient desired) = desired t.val := by
  fin_cases i
  · exact realizes0 ambient desired t
  · exact realizes1 ambient desired t
  · exact realizes2 ambient desired t
  · exact realizes3 ambient desired t
  · exact realizes4 ambient desired t
  · exact realizes5 ambient desired t
  · exact realizes6 ambient desired t
  · exact realizes7 ambient desired t
  · exact realizes8 ambient desired t
  · exact realizes9 ambient desired t
  · exact realizes10 ambient desired t
  · exact realizes11 ambient desired t
  · exact realizes12 ambient desired t
  · exact realizes13 ambient desired t
  · exact realizes14 ambient desired t
  · exact realizes15 ambient desired t
  · exact realizes16 ambient desired t
  · exact realizes17 ambient desired t
  · exact realizes18 ambient desired t
  · exact realizes19 ambient desired t
  · exact realizes20 ambient desired t
  · exact realizes21 ambient desired t
  · exact realizes22 ambient desired t
  · exact realizes23 ambient desired t
  · exact realizes24 ambient desired t
  · exact realizes25 ambient desired t
  · exact realizes26 ambient desired t
  · exact realizes27 ambient desired t
  · exact realizes28 ambient desired t
  · exact realizes29 ambient desired t
  · exact realizes30 ambient desired t
  · exact realizes31 ambient desired t
  · exact realizes32 ambient desired t
  · exact realizes33 ambient desired t
  · exact realizes34 ambient desired t
  · exact realizes35 ambient desired t
  · exact realizes36 ambient desired t
  · exact realizes37 ambient desired t
  · exact realizes38 ambient desired t
  · exact realizes39 ambient desired t
  · exact realizes40 ambient desired t
  · exact realizes41 ambient desired t
  · exact realizes42 ambient desired t
  · exact realizes43 ambient desired t
  · exact realizes44 ambient desired t
  · exact realizes45 ambient desired t
  · exact realizes46 ambient desired t
  · exact realizes47 ambient desired t
  · exact realizes48 ambient desired t
  · exact realizes49 ambient desired t
  · exact realizes50 ambient desired t
  · exact realizes51 ambient desired t
  · exact realizes52 ambient desired t
  · exact realizes53 ambient desired t

theorem preserves (i : Fin 54) (ambient : Assignment) (desired : ℕ → F) (wire : ℕ)
    (h : wire ∉ writeSet i) :
    (plan i).apply ambient desired wire = ambient wire := by
  apply (plan i).preserves ambient desired wire
  simpa only [written_eq] using h

end MSP.Artifacts.AssignmentRecoverySmall
