module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongCross
import EmcsfAcExtension.Local.Stability.GeomStrongFamily
import EmcsfAcExtension.Local.Stability.GeomStrongSectionC1
import EmcsfAcExtension.Local.Stability.GeometryDifferenceInitialGauge

/-! # Strong cross derivative limits with coupled axis traces

The incoming expansion primitive starts at λ=1/2 on the initial cone.
Its diagonal limit supplies the outgoing ν primitive's initial value.
This gives uniform AC limits on every closed characteristic section.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- [internal]
Smooth sequence form of cross geometric strong convergence, conditional
only on the pending main Lipschitz record. The threshold depends only
on `A` and its uniform main constant `C₀`, before all solution parameters.
Both full-section density limits, AC primitives and the shared axis trace
are obtained; there is no null set of section labels or radius cutoff.
-/
theorem Stab.cross_geometric_strong_ac_of_main_lipschitz_c1
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η : ℝ, 0 < η ∧ ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ),
      (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
      ε ^ 2 + sigma e M T ≤ η →
      (∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, dataDist (hn n) (hn m) T < δ) →
      (∀ n m, jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) +
        geomDist T (Sn n) (Sn m) ≤ ENNReal.ofReal (C₀ * dataDist (hn n) (hn m) T)) →
      ∃ qL qN : Icc (0 : ℝ) T → ℝ → ℝ,
        (∀ v, Integrable (qL v) (volume.restrict (Icc 0 v.val))) ∧
        (∀ u, Integrable (qN u) (volume.restrict (Icc u.val T))) ∧
        (∀ v, AbsolutelyContinuousOnInterval
          (fun u => 1 / 2 + ∫ s in 0..u, qL v s) 0 v.val) ∧
        (∀ u, AbsolutelyContinuousOnInterval
          (fun v => -(1 / 2 + ∫ s in 0..u.val, qL u s) + ∫ s in u.val..v, qN u s)
          u.val T) ∧
        (∀ v, ∀ᵐ u ∂volume.restrict (Icc 0 v.val),
          deriv (fun u => 1 / 2 + ∫ s in 0..u, qL v s) u = qL v u) ∧
        (∀ u, ∀ᵐ v ∂volume.restrict (Icc u.val T),
          deriv (fun v => -(1 / 2 + ∫ s in 0..u.val, qL u s) +
            ∫ s in u.val..v, qN u s) v = qN u v) ∧
        ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
          (∀ v, (∫ s in Icc 0 v.val,
            |pdU (triangle 0 T) (Sn n).lam s v.val - qL v s|) < δ) ∧
          (∀ u, (∫ s in Icc u.val T,
            |pdV (triangle 0 T) (Sn n).nu u.val s - qN u s|) < δ) ∧
          (∀ v, ∀ u ∈ Icc 0 v.val,
            |(Sn n).lam u v.val - (1 / 2 + ∫ s in 0..u, qL v s)| < δ) ∧
          (∀ u, ∀ v ∈ Icc u.val T,
            |(Sn n).nu u.val v - (-(1 / 2 + ∫ s in 0..u.val, qL u s) +
              ∫ s in u.val..v, qN u s)| < δ) := by
  obtain ⟨η, C, hη, hC, hPair⟩ :=
    Stab.cross_geometric_derivatives_difference_of_main_lipschitz_c1 A C₀ hA hC₀
  refine ⟨η, hη, ?_⟩
  intro T e ε M Sn hn hset hsmall hdata hmain
  let I := Icc (0 : ℝ) T
  let FL := fun n (v : I) u => (Sn n).lam u v.val
  let DL := fun n (v : I) u => pdU (triangle 0 T) (Sn n).lam u v.val
  let FN := fun n (u : I) v => (Sn n).nu u.val v
  let DN := fun n (u : I) v => pdV (triangle 0 T) (Sn n).nu u.val v
  have hSecL n (v : I) := stab_in_real_partial_primitive_c1 (hset n).pos
    (hset n).c1.c1_lam v.property
  have hSecN n (u : I) := stab_out_real_partial_primitive_c1 (hset n).pos
    (hset n).c1.c1_nu u.property
  have hpair : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∀ v : I, (∫⁻ s in Icc 0 v.val, ‖DL n v s - DL m v s‖ₑ) < ENNReal.ofReal δ) ∧
      (∀ u : I, (∫⁻ s in Icc u.val T, ‖DN n u s - DN m u s‖ₑ) < ENNReal.ofReal δ) := by
    intro δ hδ
    obtain ⟨N, hN⟩ := hdata (δ / C) (div_pos hδ hC)
    refine ⟨N, fun n hnN m hmN => ?_⟩
    have hb := hPair T e ε M (Sn n) (Sn m) (hn n) (hn m)
      (hset n) (hset m) hsmall (hmain n m)
    have hc : C * dataDist (hn n) (hn m) T < δ := by
      simpa only [mul_comm] using (lt_div_iff₀ hC).mp (hN n hnN m hmN)
    have he := (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hc
    exact ⟨fun v => ((le_iSup₂_of_le v.val v.property le_rfl).trans
      ((le_add_of_nonneg_left bot_le).trans hb)).trans_lt he,
      fun u => ((le_iSup₂_of_le u.val u.property le_rfl).trans
        ((le_add_of_nonneg_right bot_le).trans hb)).trans_lt he⟩
  obtain ⟨qL, hqL, hDL, hACL, hdL, hpL, huL⟩ :=
    stab_real_ac_family_of_density_cauchy (a := fun _ : I => (0 : ℝ))
      (b := fun v : I => v.val) (F := FL) (D := DL) (z := fun _ => (1 / 2 : ℝ))
      (fun v => v.property.1) (fun n v => (hSecL n v).1) (by
        intro δ hδ
        obtain ⟨N, hN⟩ := hpair δ hδ
        exact ⟨N, fun n hn m hm => (hN n hn m hm).1⟩)
      (fun n v u hu => (hSecL n v).2 u hu) (by
        intro δ hδ
        refine ⟨0, fun n _ v => ?_⟩
        dsimp only [FL]
        rw [stab_initial_lam (hset n) v.property, sub_self, abs_zero]
        exact hδ)
  let zN (u : I) := -(1 / 2 + ∫ s in 0..u.val, qL u s)
  have hzN : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u : I,
      |FN n u u.val - zN u| < δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := hDL δ hδ
    refine ⟨N, fun n hnN u => ?_⟩
    have haxis := (hset n).c1.axis u.val ⟨u.property.1, le_rfl, u.property.2⟩
    have hnu : (Sn n).nu u.val u.val = -(Sn n).lam u.val u.val := by
      linarith only [haxis.2.2.2.1]
    have hb := hpL n u u.val ⟨u.property.1, le_rfl⟩
    dsimp only [FL] at hb
    rw [stab_initial_lam (hset n) u.property, sub_self, abs_zero, zero_add] at hb
    dsimp only [FN, zN]
    rw [hnu, neg_sub_neg, abs_sub_comm]
    exact hb.trans_lt (hN n hnN u)
  obtain ⟨qN, hqN, hDN, hACN, hdN, hpN, huN⟩ :=
    stab_real_ac_family_of_density_cauchy (a := fun u : I => u.val)
      (b := fun _ : I => T) (F := FN) (D := DN) (z := zN)
      (fun u => u.property.2) (fun n u => (hSecN n u).1) (by
        intro δ hδ
        obtain ⟨N, hN⟩ := hpair δ hδ
        exact ⟨N, fun n hn m hm => (hN n hn m hm).2⟩)
      (fun n u v hv => (hSecN n u).2 v hv) hzN
  refine ⟨qL, qN, hqL, hqN, hACL, hACN, hdL, hdN, ?_⟩
  intro δ hδ
  obtain ⟨NL, hNL⟩ := hDL δ hδ
  obtain ⟨NN, hNN⟩ := hDN δ hδ
  have hUL := (Metric.tendstoUniformlyOn_iff.1 huL) δ hδ
  have hUN := (Metric.tendstoUniformlyOn_iff.1 huN) δ hδ
  obtain ⟨NU, hNU⟩ := eventually_atTop.1 (hUL.and hUN)
  refine ⟨max (max NL NN) NU, fun n hnN => ?_⟩
  refine ⟨hNL n ((le_max_left _ _).trans ((le_max_left _ _).trans hnN)),
    hNN n ((le_max_right _ _).trans ((le_max_left _ _).trans hnN)), ?_, ?_⟩
  · intro v u hu
    have hh := (hNU n ((le_max_right _ _).trans hnN)).1 (v, u) hu
    simpa only [FL, Real.dist_eq, abs_sub_comm] using hh
  · intro u v hv
    have hh := (hNU n ((le_max_right _ _).trans hnN)).2 (u, v) hv
    simpa only [FN, zN, Real.dist_eq, abs_sub_comm] using hh

end EmcsfAcExtension.Local
