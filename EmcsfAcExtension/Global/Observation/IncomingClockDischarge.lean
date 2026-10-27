module

public import EmcsfAcExtension.Global.Observation.IncomingTrace
import Mathlib

/-! # Incoming L² trace in the constructed inner clock

The inverse incoming inner map is the actual clock on the level curve.
Its density is derived from the normalized incoming expansion, rather
than supplied as a change-of-variables premise.
Source: charged_SF_new_version.tex:L2570–2608; approved internal project record (Z1), (N0).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Discharge the inner clock, curve and Jacobian inputs of the landed L²
trace theorem using the actual normalized inner maps. Both outer
comparison estimates are discharged by that theorem. Only the original
outer normalization record, its measured incoming boundary error and
the constructed geometric inner chart remain. Constants are selected
after `Kstatic,Ct,Bboundary,K`, before all fields, radii and errors.
There is no incoming pointwise smallness premise. -/
theorem incoming_trace_on_inner_maps_of_normalization
    (Kstatic : ℝ) (hKs : 0 ≤ Kstatic) :
    ∃ Lmin > 0, ∀ Ct Bboundary : ℝ, 0 ≤ Ct → 0 ≤ Bboundary →
    ∃ CB CE Cq : ℝ, 0 < CB ∧ 0 < CE ∧ 0 < Cq ∧
    ∀ K : ℝ, 0 ≤ K → ∃ C > 0,
    ∀ (S : Fields) (D : Set (ℝ × ℝ)) (H P : ℂ)
      (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b Lzero L epsilon eta qStar e : ℝ) (U V : ℝ ≃o ℝ),
    OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e →
    Lmin ≤ Lzero → 4 * (CB * epsilon + CE * eta) ≤ 1 / 2 → Cq * eta ≤ 1 →
    ContDiff ℝ 1 (U : ℝ → ℝ) → ContDiff ℝ 1 (U.symm : ℝ → ℝ) →
    (∀ x, 0 < deriv (U : ℝ → ℝ) x) →
    (∀ t ∈ Icc (-K) K,
      (U t, V t) ∈ sidewaysTruncation S D a b Lzero L ∧
      S.r (U t) (V t) = Lzero ∧ (nullPullback S U V).nu t t = -1 / 2) →
    IntervalIntegrable (fun u => ‖S.phi u u - H + S.xi u u / S.nu u u‖ ^ 2) volume a b →
    (∫ u in a..b, ‖S.phi u u - H + S.xi u u / S.nu u u‖ ^ 2) ≤ epsilon ^ 2 / L →
    (∫ t in (-K)..K,
      ‖(nullPullback S U V).xi t t / (nullPullback S U V).nu t t - yStar Lzero‖ ^ 2) ≤
        (C * (epsilon + eta)) ^ 2 := by
  obtain ⟨Lmin, hLmin, htrace⟩ := incoming_l2_inner_trace_of_normalization Kstatic hKs
  refine ⟨Lmin, hLmin, ?_⟩
  intro Ct Bboundary hCt hB
  obtain ⟨CB, CE, Cq, hCB, hCE, hCq, htrace⟩ := htrace Ct Bboundary hCt hB
  refine ⟨CB, CE, Cq, hCB, hCE, hCq, ?_⟩
  intro K hK
  obtain ⟨C, hC, htrace⟩ := htrace (2 * K) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e U V
    h hLzero hsmall hcharge hU hUi hUp hinner hgi hgb
  have hKK : -K ≤ K := by linarith only [hK]
  let Vzero := fun u => V (U.symm u)
  have hmem (u : ℝ) (hu : u ∈ Icc (U (-K)) (U K)) : U.symm u ∈ Icc (-K) K := by
    simpa only [OrderIso.symm_apply_apply] using
      (show U.symm u ∈ Icc (U.symm (U (-K))) (U.symm (U K)) from
        ⟨U.symm.monotone hu.1, U.symm.monotone hu.2⟩)
  have hcurve (u : ℝ) (hu : u ∈ Icc (U (-K)) (U K)) :
      (u, Vzero u) ∈ sidewaysTruncation S D a b Lzero L ∧ S.r u (Vzero u) = Lzero ∧
      deriv (U.symm : ℝ → ℝ) u = 2 * (-S.nu u (Vzero u)) := by
    have hh := hinner (U.symm u) (hmem u hu)
    have hm : (u, Vzero u) ∈ sidewaysTruncation S D a b Lzero L := by
      simpa only [OrderIso.apply_symm_apply, Vzero] using hh.1
    have hr : S.r u (Vzero u) = Lzero := by
      simpa only [OrderIso.apply_symm_apply, Vzero] using hh.2.1
    have hnu : deriv (U : ℝ → ℝ) (U.symm u) * S.nu u (Vzero u) = -1 / 2 := by
      simpa only [nullPullback, OrderIso.apply_symm_apply, Vzero] using hh.2.2
    have hd := (hU.differentiable (by norm_num) (U.symm u)).hasDerivAt
    have hdinv := hd.of_local_left_inverse U.symm.continuous.continuousAt
      (hUp _).ne' (Filter.Eventually.of_forall U.apply_symm_apply)
    refine ⟨hm, hr, ?_⟩
    rw [hdinv.deriv]
    rw [inv_eq_one_div]
    apply (div_eq_iff (hUp _).ne').mpr
    nlinarith only [hnu]
  have hleft : a ≤ U (-K) :=
    (hinner (-K) (left_mem_Icc.mpr hKK)).1.1.2.1.trans
      (hinner (-K) (left_mem_Icc.mpr hKK)).1.1.2.2.1
  have hright : U K ≤ b := (hinner K (right_mem_Icc.mpr hKK)).1.1.2.2.2
  have hraw := htrace S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e
    Vzero U.symm (U (-K)) (U K) h hLzero hsmall hcharge hleft (U.monotone hKK) hright
    (V.continuous.comp U.symm.continuous).continuousOn hUi hcurve
    (by simp only [OrderIso.symm_apply_apply]; linarith) hgi hgb
  simp only [OrderIso.symm_apply_apply] at hraw
  convert hraw using 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hKK] at ht
  have hh := hinner t ht
  have hdu : ((deriv (U : ℝ → ℝ) t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hUp t).ne'
  have hn : (S.nu (U t) (V t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by
    have hb := (h.box (U t, V t) hh.1).1.2
    linarith only [hb])
  have hratio : (nullPullback S U V).xi t t / (nullPullback S U V).nu t t =
      S.xi (U t) (V t) / S.nu (U t) (V t) := by
    simp only [nullPullback, Complex.ofReal_mul]
    field_simp [hdu, hn]
  dsimp only [OrderIso.symm_symm, Vzero]
  simp only [OrderIso.symm_apply_apply]
  rw [hratio, hh.2.1]

end EmcsfAcExtension.Global.Observation
