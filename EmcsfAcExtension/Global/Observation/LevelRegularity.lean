module

public import EmcsfAcExtension.Global.Observation.LevelSegment
public import EmcsfAcExtension.Global.Observation.RadiusRegularity
import EmcsfAcExtension.Infra.Level.Graph
import Mathlib

/-! # C¹ regularity of an existing inner level segment

The local implicit-function theorem is applied at actual positive-radius
points, with strict source margins. Its local graph is identified with
the existing continuous segment, including the two closed endpoints.
Source: charged_SF_new_version.tex:L2741–2755; approved internal project record (D4).
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
A continuous level segment in the actual source chart is C¹ and strictly
increasing. Its speed is the exact ratio `λ/(-ν)` from the original
radius equations. The hypotheses describe only the existing segment,
the original solution, strict source margins and C¹ increasing labels.
No level-curve derivative, optical estimate or comparison estimate is
assumed. There are no quantitative constants. -/
theorem actual_chart_level_regular_of_continuous_segment
    {e ui s a b vleft vright ρ L : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hs : 0 < s) (hρ : 0 < ρ)
    (χ : ℝ → ℝ) (U V : ℝ ≃o ℝ)
    (hU : ContDiff ℝ 1 (U : ℝ → ℝ)) (hV : ContDiff ℝ 1 (V : ℝ → ℝ))
    (hUp : ∀ x, 0 < deriv (U : ℝ → ℝ) x)
    (hVp : ∀ x, 0 < deriv (V : ℝ → ℝ) x)
    (hi : ui < s * U a) (hv : s * V b < 0)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc vleft vright))
    (hmem : ∀ v ∈ Icc vleft vright,
      (g v, v) ∈ sidewaysTruncation
        (nullPullback (rescaleFields (gaugeFields e S χ) s) U V)
        {p : ℝ × ℝ | (s * U p.1, s * V p.2) ∈ origDomain ui} a b ρ L)
    (hroot : ∀ v ∈ Icc vleft vright,
      (nullPullback (rescaleFields (gaugeFields e S χ) s) U V).r (g v) v = ρ) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
    ContDiffOn ℝ 1 g (Icc vleft vright) ∧
      (∀ v ∈ Icc vleft vright,
        HasDerivWithinAt g (P.lam (g v) v / (-P.nu (g v) v)) (Icc vleft vright) v) ∧
      StrictMonoOn g (Icc vleft vright) := by
  let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
  have hlabels (v : ℝ) (hh : v ∈ Icc vleft vright) :
      ui < s * U (g v) ∧ s * U (g v) < s * V v ∧ s * V v < 0 := by
    have hm := hmem v hh
    have hlow : ui < s * U (g v) := hi.trans_le
      (mul_le_mul_of_nonneg_left (U.monotone (hm.1.2.1.trans hm.1.2.2.1)) hs.le)
    have hhigh : s * V v < 0 :=
      (mul_le_mul_of_nonneg_left (V.monotone (hm.1.2.2.1.trans hm.1.2.2.2)) hs.le).trans_lt hv
    have hstrict : s * U (g v) < s * V v := by
      rcases lt_or_eq_of_le hm.1.1.2.2.1 with hh' | hh'
      · exact hh'
      · change s * U (g v) = s * V v at hh'
        have hmo : (s * U (g v), s * V v) ∈ origDomain ui := hm.1.1
        have hz := (hS.axis (s * U (g v)) (by simpa only [← hh'] using hmo)).1
        have hp : 0 < S.r (s * U (g v)) (s * V v) / s := by
          change 0 < P.r (g v) v
          rw [hroot v hh]
          exact hρ
        rw [← hh', hz, zero_div] at hp
        exact False.elim (lt_irrefl _ hp)
    exact ⟨hlow, hstrict, hhigh⟩
  have hnu (v : ℝ) (hh : v ∈ Icc vleft vright) : P.nu (g v) v < 0 :=
    mul_neg_of_pos_of_neg (hUp (g v)) (hS.nu_neg _ (hmem v hh).1.1)
  have hlam (v : ℝ) (hh : v ∈ Icc vleft vright) : 0 < P.lam (g v) v :=
    mul_pos (hVp v) (hS.lam_pos _ (hmem v hh).1.1)
  have hregular (v : ℝ) (hh : v ∈ Icc vleft vright) :
      ContDiffWithinAt ℝ 1 g (Icc vleft vright) v ∧
      HasDerivWithinAt g (P.lam (g v) v / (-P.nu (g v) v)) (Icc vleft vright) v := by
    have labels := hlabels v hh
    have hr := chart_radius_contDiffAt_and_hasFDerivAt hS hs χ U V hU hV
      labels.1 labels.2.1 labels.2.2
    have hswap : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.2, p.1)) :=
      contDiff_snd.prodMk contDiff_fst
    have hbasec : ContDiffAt ℝ 1 (Function.uncurry P.r) (g v, v) := hr.1
    have hbaseD : HasFDerivAt (Function.uncurry P.r)
        (P.nu (g v) v • ContinuousLinearMap.fst ℝ ℝ ℝ +
          P.lam (g v) v • ContinuousLinearMap.snd ℝ ℝ ℝ) (g v, v) := hr.2
    have hrc : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => P.r p.2 p.1) (v, g v) :=
      hbasec.comp (g := Function.uncurry P.r) (v, g v) hswap.contDiffAt
    have hdswap : HasFDerivAt (fun p : ℝ × ℝ => (p.2, p.1))
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)) (v, g v) :=
      hasFDerivAt_snd.prodMk hasFDerivAt_fst
    have hrd : HasFDerivAt (fun p : ℝ × ℝ => P.r p.2 p.1)
        (P.lam (g v) v • ContinuousLinearMap.fst ℝ ℝ ℝ +
          P.nu (g v) v • ContinuousLinearMap.snd ℝ ℝ ℝ) (v, g v) := by
      change HasFDerivAt ((Function.uncurry P.r) ∘ (fun p : ℝ × ℝ => (p.2, p.1))) _ _
      apply (hbaseD.comp (v, g v) hdswap).congr_fderiv
      ext <;> simp [add_comm]
    have hi' := Level.contDiffWithinAt_levelGraph_of_continuousWithin
      (r := fun x y => P.r y x) hrc hrd (hnu v hh).ne
      (hg v hh) (by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (hroot x hx).trans (hroot v hh).symm)
    convert hi' using 1
    simp only [neg_div, div_neg]
  refine ⟨fun v hh => (hregular v hh).1, fun v hh => (hregular v hh).2, ?_⟩
  apply strictMonoOn_of_hasDerivWithinAt_pos
    (f' := fun v => P.lam (g v) v / (-P.nu (g v) v)) (convex_Icc _ _) hg
  · intro v hh
    rw [interior_Icc] at hh
    exact (hregular v (Ioo_subset_Icc_self hh)).2.mono interior_subset
  · intro v hh
    rw [interior_Icc] at hh
    exact div_pos (hlam v (Ioo_subset_Icc_self hh)) (neg_pos.mpr (hnu v (Ioo_subset_Icc_self hh)))

end EmcsfAcExtension.Global.Observation
