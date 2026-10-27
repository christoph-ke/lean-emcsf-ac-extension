module

public import EmcsfAcExtension.Global.Api.Domains
public import EmcsfAcExtension.Global.Calculus.Endpoint

/-! # Ordinary Hawking mass and characteristic monotonicity

The frozen mass sources are the ordinary mass equations of
charged_SF_new_version.tex:L954–962. Their signs and the characteristic FTC, including
existing regular-axis endpoints, imply both null monotonicities.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Terminal

/-- [node prop:charged-terminal-equivalence#mass-equations]
The two literal ordinary Hawking mass equations hold in integral form on
every closed characteristic segment in a frozen solution. Existing axis
endpoints are allowed; no terminal endpoint is added. -/
theorem mass_equations {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) :
    (∀ u a b, u ≤ a → a ≤ b → outSeg u a b ⊆ D →
      IntegralForm (S.m u) (fun v =>
        (1 - S.mu u v) * ‖S.theta u v‖ ^ 2 / (2 * S.lam u v) +
        S.Q u v ^ 2 * S.lam u v / (2 * S.r u v ^ 2)) a b) ∧
    (∀ a b v, a ≤ b → b ≤ v → inSeg a b v ⊆ D →
      IntegralForm (fun u => S.m u v) (fun u =>
        (1 - S.mu u v) * ‖S.xi u v‖ ^ 2 / (2 * S.nu u v) +
        S.Q u v ^ 2 * S.nu u v / (2 * S.r u v ^ 2)) a b) := by
  constructor
  · intro u a b hua hab hs
    exact (Calculus.out_integralForm hS hua hab hs).2.2.1
  · intro a b v hab hbv hs
    exact (Calculus.in_integralForm hS hab hbv hs).2.2.1

/-- [internal] Every frozen outgoing mass density is nonnegative, including
at existing axis points with the frozen division convention. -/
theorem massV_nonneg {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (hp : (u, v) ∈ D) : 0 ≤ S.mV u v := by
  exact add_nonneg
    (div_nonneg (mul_nonneg (hS.one_sub_mu_pos (u, v) hp).le (sq_nonneg _))
      (mul_nonneg (by norm_num) (hS.lam_pos (u, v) hp).le))
    (div_nonneg (mul_nonneg (sq_nonneg _) (hS.lam_pos (u, v) hp).le)
      (mul_nonneg (by norm_num) (sq_nonneg _)))

/-- [internal] Every frozen incoming mass density is nonpositive. -/
theorem massU_nonpos {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (hp : (u, v) ∈ D) : S.mU u v ≤ 0 := by
  exact add_nonpos
    (div_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (hS.one_sub_mu_pos (u, v) hp).le (sq_nonneg _))
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hS.nu_neg (u, v) hp).le))
    (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hS.nu_neg (u, v) hp).le)
      (mul_nonneg (by norm_num) (sq_nonneg _)))

/-- [internal] The ordinary mass is nondecreasing along an outgoing section. -/
theorem mass_mono_out {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u ≤ a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) : S.m u a ≤ S.m u b := by
  have he := (Calculus.out_integralForm hS hua hab hs).2.2.1
  have hi : 0 ≤ ∫ v in a..b, S.mV u v :=
    intervalIntegral.integral_nonneg hab
      (fun v hv => massV_nonneg hS (hs ⟨rfl, hv.1, hv.2⟩))
  rw [← he.2] at hi
  exact sub_nonneg.mp hi

/-- [internal] The ordinary mass is nonincreasing along an incoming section. -/
theorem mass_antitone_in {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b ≤ v)
    (hs : inSeg a b v ⊆ D) : S.m b v ≤ S.m a v := by
  have he := (Calculus.in_integralForm hS hab hbv hs).2.2.1
  have hi : (∫ u in a..b, S.mU u v) ≤ 0 := by
    have hn : 0 ≤ ∫ u in a..b, -S.mU u v :=
      intervalIntegral.integral_nonneg hab
        (fun u hu => neg_nonneg.mpr (massU_nonpos hS (hs ⟨hu.1, hu.2, rfl⟩)))
    rw [intervalIntegral.integral_neg] at hn
    exact neg_nonneg.mp hn
  rw [← he.2] at hi
  exact sub_nonpos.mp hi

/-- [node prop:charged-terminal-equivalence#mass-monotonicity]
Throughout the original development, the mass is nonnegative, its outgoing
density is nonnegative, and its incoming density is nonpositive
(charged_SF_new_version.tex:L962). Nonnegativity follows from the existing axis. -/
theorem mass_monotonicity {ui e : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) :
    ∀ p ∈ origDomain ui, 0 ≤ S.m p.1 p.2 ∧ 0 ≤ S.mV p.1 p.2 ∧ S.mU p.1 p.2 ≤ 0 := by
  intro p hp
  have hs : outSeg p.1 p.1 p.2 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hp.2.2.1).2
      ⟨hp.1, hp.2.1, le_rfl, hp.2.2.2⟩
  have hz := (hS.axis p.1 (hs ⟨rfl, le_rfl, hp.2.2.1⟩)).2.1
  have hm := mass_mono_out hS le_rfl hp.2.2.1 hs
  rw [hz] at hm
  exact ⟨hm, massV_nonneg hS hp, massU_nonpos hS hp⟩

end EmcsfAcExtension.Global.Terminal
