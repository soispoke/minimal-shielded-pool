import Primality.PrattCertificate

/-! A kernel-checked Pratt certificate for the BN254 base modulus.
The explicit large-prime factor chain avoids repeating probabilistic factor
search during elaboration. Every factor, product and modular power is proved.
This certificate establishes primality only, not elliptic-curve cardinality. -/

namespace BN254

def baseFieldSize : ℕ :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem BaseField_is_prime : Nat.Prime baseFieldSize := by
  unfold baseFieldSize
  refine PrattCertificate'.out ⟨3, (by reduce_mod_char), ?_⟩
  refine .split [2, 3 ^ 2, 13, 29, 67, 229, 311, 983, 11003, 405928799, 11465965001, 13427688667394608761327070753331941386769] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 29 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 67 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 229 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 311 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 983 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 11003 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 405928799 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
    refine PrattCertificate'.out ⟨22, (by reduce_mod_char), ?_⟩
    refine .split [2, 11, 4999, 3691] (fun r hr => ?_) (by norm_num)
    simp at hr
    rcases hr with hr | hr | hr | hr <;> rw [hr]
    · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 11 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 4999 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 3691 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 11465965001 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
    refine PrattCertificate'.out ⟨3, (by reduce_mod_char), ?_⟩
    refine .split [2 ^ 3, 5 ^ 4, 7, 327599] (fun r hr => ?_) (by norm_num)
    simp at hr
    rcases hr with hr | hr | hr | hr <;> rw [hr]
    · exact .prime 2 3 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 5 4 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 7 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 327599 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 13427688667394608761327070753331941386769 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
    refine PrattCertificate'.out ⟨17, (by reduce_mod_char), ?_⟩
    refine .split [2 ^ 4, 3, 7, 11, 1853641, 4562087, 173171039, 2480874801745591] (fun r hr => ?_) (by norm_num)
    simp at hr
    rcases hr with hr | hr | hr | hr | hr | hr | hr | hr <;> rw [hr]
    · exact .prime 2 4 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 7 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 11 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 1853641 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 4562087 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · refine .prime 173171039 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
      refine PrattCertificate'.out ⟨13, (by reduce_mod_char), ?_⟩
      refine .split [2, 73, 89, 13327] (fun r hr => ?_) (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr <;> rw [hr]
      · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 73 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 89 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 13327 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · refine .prime 2480874801745591 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
      refine PrattCertificate'.out ⟨6, (by reduce_mod_char), ?_⟩
      refine .split [2, 3 ^ 2, 5, 19, 41, 35385462869] (fun r hr => ?_) (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr | hr | hr <;> rw [hr]
      · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 3 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 5 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 19 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 41 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · refine .prime 35385462869 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
        refine PrattCertificate'.out ⟨2, (by reduce_mod_char), ?_⟩
        refine .split [2 ^ 2, 7, 1263766531] (fun r hr => ?_) (by norm_num)
        simp at hr
        rcases hr with hr | hr | hr <;> rw [hr]
        · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
        · exact .prime 7 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
        · refine .prime 1263766531 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
          refine PrattCertificate'.out ⟨10, (by reduce_mod_char), ?_⟩
          refine .split [2, 3, 5, 13, 911, 3557] (fun r hr => ?_) (by norm_num)
          simp at hr
          rcases hr with hr | hr | hr | hr | hr | hr <;> rw [hr]
          · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
          · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
          · exact .prime 5 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
          · exact .prime 13 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
          · exact .prime 911 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
          · exact .prime 3557 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)

end BN254
