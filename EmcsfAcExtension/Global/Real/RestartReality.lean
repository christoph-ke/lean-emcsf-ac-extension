module

public import EmcsfAcExtension.Global.Real.Conjugation
public import EmcsfAcExtension.Local.Api.EqOn

/-! # Reality of the unique uncharged restart

internal project record R5 uses the full uniqueness clause of the same restart witness.
The competitor is its conjugate on the entire closed restart triangle.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Real

/-- [internal]
A restart with real normalized datum agrees with its conjugate, so all three
scalar fields are real. The uniqueness clause belongs to this witness `N`;
its closed right endpoint allows the competitor on the whole triangle (internal project record R5).
-/
theorem restart_reality_of_unique_real_datum {T : ℝ} {h : ℝ → ℂ} {N : Fields}
    (hT : 0 < T) (hN : IsSolution 0 N (triangle 0 T))
    (hgauge : ∀ t ∈ Icc 0 T, N.A t t = 0)
    (hdata : ∀ v ∈ Icc 0 T, N.r 0 v = v / 2 ∧ N.a 0 v = h v)
    (hreal : ∀ v ∈ Icc 0 T, (h v).im = 0)
    (huniq : ∀ T' ∈ Ioc 0 T, ∀ S' : Fields,
      IsSolution 0 S' (triangle 0 T') →
      (∀ v ∈ Icc 0 T', S'.r 0 v = v / 2 ∧ S'.a 0 v = h v) →
      (∀ t ∈ Icc 0 T', S'.A t t = 0) → S'.EqOn N (triangle 0 T')) :
    N.conj.EqOn N (triangle 0 T) ∧
      ∀ p ∈ triangle 0 T, (N.phi p.1 p.2).im = 0 ∧
        (N.theta p.1 p.2).im = 0 ∧ (N.xi p.1 p.2).im = 0 := by
  have heq : N.conj.EqOn N (triangle 0 T) := by
    apply huniq T ⟨hT, le_rfl⟩ N.conj (isSolution_conj hN)
    · intro v hv
      refine ⟨(hdata v hv).1, ?_⟩
      rw [Fields.conj_a, (hdata v hv).2]
      exact Complex.conj_eq_iff_im.mpr (hreal v hv)
    · exact hgauge
  refine ⟨heq, ?_⟩
  intro p hp
  exact ⟨Complex.conj_eq_iff_im.mp (heq.phi hp),
    Complex.conj_eq_iff_im.mp (heq.theta hp),
    Complex.conj_eq_iff_im.mp (heq.xi hp)⟩

end EmcsfAcExtension.Global.Real
