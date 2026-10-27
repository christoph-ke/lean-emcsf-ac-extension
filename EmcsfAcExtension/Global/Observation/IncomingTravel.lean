module

public import EmcsfAcExtension.Global.Observation.Window
import EmcsfAcExtension.Global.Observation.SourceEquations
import Mathlib

/-! # Incoming travel in the actual source chart

The ray ends at the first of the final available label and its original
axis label. Radius monotonicity and the ordinary radius equation come
from the original solution. Source: charged_SF_new_version.tex:L2741–2755;
approved internal project record (D4).
-/

public section

open Set

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
An incoming ray in the actual source chart reaches its target radius
within the stopped optical travel budget. The endpoint is constructed
from the original axis and the available final label. Continuity,
strict radius decrease and the radius equation are discharged from the
original solution. Only the normalized optical lower bound above the
target remains an input, to be supplied by the source optical theorem.
The constants `c,L,ρ` precede the ray and are independent of its endpoint. -/
theorem actual_chart_incoming_radius_hit_of_optical_bound
    {e ui s a b v c L ρ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hs : 0 < s)
    (χ : ℝ → ℝ) (U V : ℝ ≃o ℝ) (hU : ContDiff ℝ 1 (U : ℝ → ℝ))
    (hUp : ∀ x, 0 < deriv (U : ℝ → ℝ) x)
    (hi : ui ≤ s * U a) (hu : s * U b < 0) (hv : s * V b < 0)
    (hva : a ≤ v) (hvb : v ≤ b) (hc : 0 < c) (hρ : 0 < ρ) (hρL : ρ ≤ L)
    (hstartmem : (s * U v, s * V v) ∈ origDomain ui)
    (hstart : (nullPullback (rescaleFields (gaugeFields e S χ) s) U V).r v v = L)
    (hbudget : L / c ≤ b - v)
    (hspeed : ∀ p ∈ sidewaysTruncation
      (nullPullback (rescaleFields (gaugeFields e S χ) s) U V)
      {p : ℝ × ℝ | (s * U p.1, s * V p.2) ∈ origDomain ui} a b ρ L,
      c ≤ -(nullPullback (rescaleFields (gaugeFields e S χ) s) U V).nu p.1 p.2) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
    let D := {p : ℝ × ℝ | (s * U p.1, s * V p.2) ∈ origDomain ui}
    ∃ u ∈ Icc v b, (u, v) ∈ sidewaysTruncation P D a b ρ L ∧
      P.r u v = ρ ∧ u - v ≤ (L - ρ) / c ∧
      ∀ z ∈ Icc v b, (z, v) ∈ D → P.r z v = ρ → z = u := by
  let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
  let axis := U.symm (V v)
  let endpoint := min b axis
  have hVneg : s * V v < 0 :=
    (mul_le_mul_of_nonneg_left (V.monotone hvb) hs.le).trans_lt hv
  have hvUv : s * U v ≤ s * V v := hstartmem.2.2.1
  have haxis : v ≤ axis := by
    apply U.le_iff_le.mp
    rw [OrderIso.apply_symm_apply]
    exact (mul_le_mul_iff_right₀ hs).mp hvUv
  have hve : v ≤ endpoint := le_min hvb haxis
  have hemem (x : ℝ) (hx : x ∈ Icc v endpoint) :
      (s * U x, s * V v) ∈ origDomain ui := by
    have hxb : x ≤ b := hx.2.trans (min_le_left _ _)
    have hxa : x ≤ axis := hx.2.trans (min_le_right _ _)
    have hxuv : U x ≤ V v := by
      simpa only [axis, OrderIso.apply_symm_apply] using U.monotone hxa
    exact ⟨hi.trans (mul_le_mul_of_nonneg_left (U.monotone (hva.trans hx.1)) hs.le),
      (mul_le_mul_of_nonneg_left (U.monotone hxb) hs.le).trans_lt hu,
      mul_le_mul_of_nonneg_left hxuv hs.le, hVneg.le⟩
  have hcont : ContinuousOn (fun x => P.r x v) (Icc v endpoint) :=
    ((hS.cont_r.comp
      ((continuous_const.mul U.continuous).prodMk continuous_const).continuousOn
      hemem).div_const s)
  have hd (x : ℝ) (hx : x ∈ Ioo v endpoint) :
      HasDerivAt (fun x => P.r x v) (P.nu x v) x := by
    have hxi : ui < s * U x := hi.trans_lt
      (mul_lt_mul_of_pos_left (U.strictMono (hva.trans_lt hx.1)) hs)
    have hxaxis : x < axis := hx.2.trans_le (min_le_right _ _)
    have hxuv : s * U x < s * V v := by
      have hh : U x < V v := by
        simpa only [axis, OrderIso.apply_symm_apply] using U.strictMono hxaxis
      exact mul_lt_mul_of_pos_left hh hs
    have hdS := (original_characteristic_equations hS hxi hxuv hVneg).2.1
    have hdU := ((hU.differentiable (by norm_num) x).hasDerivAt.const_mul s)
    convert (hdS.comp x hdU).div_const s using 1 <;>
      dsimp [P, nullPullback, rescaleFields, gaugeFields]
    field_simp
  have hanti : StrictAntiOn (fun x => P.r x v) (Icc v endpoint) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (f' := fun x => P.nu x v)
      (convex_Icc _ _) hcont
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      change deriv (U : ℝ → ℝ) x * S.nu (s * U x) (s * V v) < 0
      exact mul_neg_of_pos_of_neg (hUp x)
        (hS.nu_neg _ (hemem x (Ioo_subset_Icc_self hx)))
  have hupper (x : ℝ) (hx : x ∈ Icc v endpoint) : P.r x v ≤ L := by
    rw [← hstart]
    exact hanti.antitoneOn (left_mem_Icc.mpr hve) hx hx.1
  have hend : P.r endpoint v ≤ ρ ∨ L / c ≤ endpoint - v := by
    by_cases hba : b ≤ axis
    · exact Or.inr (by simpa only [endpoint, min_eq_left hba] using hbudget)
    · left
      have hea : endpoint = axis := min_eq_right (le_of_not_ge hba)
      have haxiszero : P.r endpoint v = 0 := by
        have hm := hemem endpoint (right_mem_Icc.mpr hve)
        have heq : s * U endpoint = s * V v := by
          rw [hea]
          simp only [axis, OrderIso.apply_symm_apply]
        have hz := (hS.axis _ (by simpa only [← heq] using hm)).1
        change S.r (s * U endpoint) (s * V v) / s = 0
        rw [← heq, hz, zero_div]
      rw [haxiszero]
      exact hρ.le
  obtain ⟨u, hu, hru, htravel, huniq⟩ := radius_hit_of_stopped_travel hve hc hρ hρL
    hcont hanti hstart hend (fun x hx hcut => ⟨hd x hx, by
      have hh := hspeed (x, v) ⟨⟨hemem x (Ioo_subset_Icc_self hx),
        hva, hx.1.le, hx.2.le.trans (min_le_left _ _)⟩,
        hcut, hupper x (Ioo_subset_Icc_self hx)⟩
      linarith only [hh]⟩)
  refine ⟨u, ⟨hu.1, hu.2.trans (min_le_left _ _)⟩,
    ⟨⟨hemem u hu, hva, hu.1, hu.2.trans (min_le_left _ _)⟩,
      hru.ge, hru.le.trans hρL⟩, hru, htravel, ?_⟩
  intro z hz hzmem hzrad
  have hza : z ≤ axis := by
    apply U.le_iff_le.mp
    rw [OrderIso.apply_symm_apply]
    exact (mul_le_mul_iff_right₀ hs).mp hzmem.2.2.1
  exact huniq z ⟨hz.1, le_min hz.2 hza⟩ hzrad

end EmcsfAcExtension.Global.Observation
