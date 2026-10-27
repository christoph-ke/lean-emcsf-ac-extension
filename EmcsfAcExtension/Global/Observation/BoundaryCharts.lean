module

public import EmcsfAcExtension.Global.Observation.BoundaryData
import EmcsfAcExtension.Global.Observation.Gauge

/-! # Actual C¹ coordinate maps for the cylinder chart

The coordinate maps are extended by integrating a clipped positive
clock density. Their derivatives therefore exist at the window endpoints
as well as in its interior. The chart diagonal is the outer cylinder.
Source: charged_SF_new_version.tex:L1980–2034; internal project record (N), internal project record
N4.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global

/-- [internal]
A positive continuous clock density on a compact interval extends to a
global C¹ increasing coordinate isomorphism, with C¹ inverse. Both its
values and its actual derivatives agree at every point of the closed
interval. No second derivative or uniform optical bound is required. -/
theorem Observation.c1_orderIso_of_positive_clock
    {f w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < w x)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (w x) x) :
    ∃ F : ℝ ≃o ℝ, ContDiff ℝ 1 (F : ℝ → ℝ) ∧
      ContDiff ℝ 1 (F.symm : ℝ → ℝ) ∧
      (∀ x ∈ Icc a b, F x = f x) ∧
      (∀ x ∈ Icc a b, HasDerivAt (F : ℝ → ℝ) (w x) x) ∧
      ∀ x, 0 < deriv (F : ℝ → ℝ) x := by
  let c : ℝ → ℝ := fun x => min (max a x) b
  have hc : Continuous c := (continuous_const.max continuous_id).min continuous_const
  have hcmem (x : ℝ) : c x ∈ Icc a b :=
    ⟨le_min (le_max_left _ _) hab, min_le_right _ _⟩
  have hcfix (x : ℝ) (hx : x ∈ Icc a b) : c x = x := by
    simp only [c, max_eq_right hx.1, min_eq_left hx.2]
  let W : ℝ → ℝ := w ∘ c
  have hW : Continuous W := hw.comp_continuous hc hcmem
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, le_rfl, hab⟩ hw
  have hm : 0 < w x₀ := hpos x₀ hx₀
  have hlow (x : ℝ) : w x₀ ≤ W x := hmin (hcmem x)
  let G : ℝ → ℝ := fun x => f a + ∫ y in a..x, W y
  have hG (x : ℝ) : HasDerivAt G (W x) x := by
    simpa only [G, zero_add] using
      (intervalIntegral.integral_hasDerivAt_right (hW.intervalIntegrable a x)
        hW.stronglyMeasurable.stronglyMeasurableAtFilter hW.continuousAt).const_add (f a)
  have hGderiv : deriv G = W := funext fun x => (hG x).deriv
  have hGc : ContDiff ℝ 1 G := contDiff_one_iff_deriv.mpr
    ⟨fun x => (hG x).differentiableAt, by rwa [hGderiv]⟩
  have hmono : StrictMono G := strictMono_of_hasDerivAt_pos hG
    (fun x => hm.trans_le (hlow x))
  have hgrow {x y : ℝ} (hxy : x ≤ y) : w x₀ * (y - x) ≤ G y - G x := by
    apply mul_sub_le_image_sub_of_le_deriv (fun z => (hG z).differentiableAt)
      (fun z => by rw [(hG z).deriv]; exact hlow z) hxy
  have hsurj : Function.Surjective G := by
    intro z
    let d := (|z - G a| + 1) / w x₀
    have hd0 : 0 ≤ d := by dsimp [d]; positivity
    have hprod : w x₀ * d = |z - G a| + 1 := by dsimp [d]; field_simp
    have hlo := hgrow (show a - d ≤ a by linarith only [hd0])
    have hhi := hgrow (show a ≤ a + d by linarith only [hd0])
    have hzlo : G (a - d) ≤ z := by
      have ha := neg_abs_le (z - G a)
      have hh : w x₀ * (a - (a - d)) = |z - G a| + 1 := by
        convert hprod using 1
        ring
      rw [hh] at hlo
      linarith only [hlo, ha]
    have hzhi : z ≤ G (a + d) := by
      have ha := le_abs_self (z - G a)
      have hh : w x₀ * (a + d - a) = |z - G a| + 1 := by
        convert hprod using 1
        ring
      rw [hh] at hhi
      linarith only [hhi, ha]
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc
      (show a - d ≤ a + d by linarith only [hd0]) hGc.continuous.continuousOn ⟨hzlo, hzhi⟩
    exact ⟨x, hx⟩
  let F := hmono.orderIsoOfSurjective G hsurj
  have hFc : ContDiff ℝ 1 (F : ℝ → ℝ) := hGc
  have hFi : ContDiff ℝ 1 (F.symm : ℝ → ℝ) :=
    F.toHomeomorph.contDiff_symm_deriv
      (fun x => (hm.trans_le (hlow x)).ne') hG hFc
  refine ⟨F, hFc, hFi, ?_, ?_, ?_⟩
  · intro x hx
    have hi := Observation.integralForm_on_of_continuous_tangent hf hw hd
      a ⟨le_rfl, hab⟩ x hx
    change f a + (∫ y in a..x, W y) = f x
    have he : (∫ y in a..x, W y) = ∫ y in a..x, w y := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hx.1] at hy
      exact congrArg w (hcfix y ⟨hy.1, hy.2.trans hx.2⟩)
    rw [he, ← hi.2]
    ring
  · intro x hx
    simpa only [F, StrictMono.coe_orderIsoOfSurjective, W, Function.comp_apply,
      hcfix x hx] using! hG x
  · intro x
    change 0 < deriv G x
    rw [(hG x).deriv]
    exact hm.trans_le (hlow x)

/-- [node prop:charged-observation#boundary-null-normalization]
Every original clock cylinder on a proper compact window has global C¹
coordinate isomorphisms and C¹ inverse labels. They agree with the clock
maps, including their actual clock derivatives at both endpoints. The
only solution is the original one; no chart `IsSolution` is asserted. -/
theorem Observation.boundary_c1_maps_of_clock_cylinder
    {e b a z : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (haz : a ≤ z) (γ : ClockCylinder S D b a z) :
    ∃ U V : ℝ ≃o ℝ,
      ContDiff ℝ 1 (U : ℝ → ℝ) ∧ ContDiff ℝ 1 (V : ℝ → ℝ) ∧
      ContDiff ℝ 1 (U.symm : ℝ → ℝ) ∧ ContDiff ℝ 1 (V.symm : ℝ → ℝ) ∧
      (∀ x, 0 < deriv (U : ℝ → ℝ) x) ∧ (∀ x, 0 < deriv (V : ℝ → ℝ) x) ∧
      (∀ x ∈ Icc a z, U x = γ.U x ∧ V x = γ.V x) ∧
      (∀ x ∈ Icc a z, HasDerivAt (U : ℝ → ℝ)
        ((-S.nu (U x) (V x))⁻¹) x) ∧
      ∀ x ∈ Icc a z, HasDerivAt (V : ℝ → ℝ)
        ((S.lam (U x) (V x))⁻¹) x := by
  have hγ : ContinuousOn (fun x => (γ.U x, γ.V x)) (Icc a z) :=
    γ.c1_U.continuousOn.prodMk γ.c1_V.continuousOn
  have hnu : ContinuousOn (fun x => -S.nu (γ.U x) (γ.V x)) (Icc a z) :=
    (hS.cont_nu.comp hγ γ.mem).neg
  have hlam : ContinuousOn (fun x => S.lam (γ.U x) (γ.V x)) (Icc a z) :=
    hS.cont_lam.comp hγ γ.mem
  have hn (x : ℝ) (hx : x ∈ Icc a z) : 0 < -S.nu (γ.U x) (γ.V x) :=
    neg_pos.mpr (hS.nu_neg _ (γ.mem x hx))
  have hl (x : ℝ) (hx : x ∈ Icc a z) : 0 < S.lam (γ.U x) (γ.V x) :=
    hS.lam_pos _ (γ.mem x hx)
  obtain ⟨U, hU, hUi, hUeq, hUd, hUpos⟩ := Observation.c1_orderIso_of_positive_clock haz
    γ.c1_U.continuousOn (hnu.inv₀ (fun x hx => (hn x hx).ne'))
    (fun x hx => inv_pos.mpr (hn x hx))
    (fun x hx => (γ.rate_U x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
  obtain ⟨V, hV, hVi, hVeq, hVd, hVpos⟩ := Observation.c1_orderIso_of_positive_clock haz
    γ.c1_V.continuousOn (hlam.inv₀ (fun x hx => (hl x hx).ne'))
    (fun x hx => inv_pos.mpr (hl x hx))
    (fun x hx => (γ.rate_V x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
  refine ⟨U, V, hU, hV, hUi, hVi, hUpos, hVpos,
    fun x hx => ⟨hUeq x hx, hVeq x hx⟩, ?_, ?_⟩
  · intro x hx
    simpa only [hUeq x hx, hVeq x hx, Pi.inv_apply] using! hUd x hx
  · intro x hx
    simpa only [hUeq x hx, hVeq x hx, Pi.inv_apply] using! hVd x hx

/-- [internal]
The original incoming-coordinate residual gauge is constructed from the
global clock maps. It kills the potential on the closed cylinder window,
with genuine derivatives at the endpoints and zero initial phase. -/
theorem Observation.boundary_parallel_gauge_of_c1_clock_maps
    {e b a z : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (haz : a ≤ z) (γ : ClockCylinder S D b a z)
    (U V : ℝ ≃o ℝ) (hUi : Continuous (U.symm : ℝ → ℝ))
    (hV : Continuous (V : ℝ → ℝ))
    (heq : ∀ x ∈ Icc a z, U x = γ.U x ∧ V x = γ.V x) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ 1 χ ∧ χ (U a) = 0 ∧
      (∀ x ∈ Icc a z, HasDerivAt χ (S.A (U x) (V x)) (U x)) ∧
      ∀ x ∈ Icc a z, (gaugeFields e S χ).A (U x) (V x) = 0 := by
  let vb : ℝ → ℝ := fun u => V (U.symm u)
  have hmap (u : ℝ) (hu : u ∈ Icc (U a) (U z)) : U.symm u ∈ Icc a z := by
    constructor
    · exact U.le_iff_le.mp (by simpa using hu.1)
    · exact U.le_iff_le.mp (by simpa using hu.2)
  have hmem (u : ℝ) (hu : u ∈ Icc (U a) (U z)) : (u, vb u) ∈ D := by
    have hx := hmap u hu
    have hxy := heq (U.symm u) hx
    have hm := γ.mem (U.symm u) hx
    rw [← hxy.1, ← hxy.2] at hm
    simpa only [U.apply_symm_apply, vb] using hm
  have hc : Continuous (fun u => (u, vb u)) := continuous_id.prodMk (hV.comp hUi)
  have hA := hS.cont_A.comp hc.continuousOn hmem
  obtain ⟨χ, hχ, hχ0, hχd, hkill, _⟩ :=
    Observation.boundary_parallel_gauge e S vb (U.monotone haz) hA
  refine ⟨χ, hχ, hχ0, ?_, ?_⟩
  · intro x hx
    simpa only [vb, U.symm_apply_apply] using!
      hχd (U x) ⟨U.monotone hx.1, U.monotone hx.2⟩
  · intro x hx
    simpa only [vb, U.symm_apply_apply] using!
      hkill (U x) ⟨U.monotone hx.1, U.monotone hx.2⟩

/-- [internal]
Changing the maps outside the closed clock window preserves its covariant
variation. Inside the window values agree, and incoming derivatives agree
in the interior; endpoint derivative values do not affect the integral. -/
theorem Observation.curveCovVar_eq_of_clock_agreement
    (e : ℝ) (S : Fields) (f : ℝ → ℝ → ℂ) (U V : ℝ → ℝ)
    {D : Set (ℝ × ℝ)} {b a z : ℝ} (γ : ClockCylinder S D b a z)
    (heq : ∀ x ∈ Icc a z, U x = γ.U x ∧ V x = γ.V x)
    (hd : ∀ x ∈ Ioo a z, deriv U x = deriv γ.U x) :
    curveCovVar e S f U V a z = curveCovVar e S f γ.U γ.V a z := by
  unfold curveCovVar
  apply eVariationOn.eq_of_eqOn
  intro x hx
  have hi : (∫ y in a..x, S.A (U y) (V y) * deriv U y) =
      ∫ y in a..x, S.A (γ.U y) (γ.V y) * deriv γ.U y := by
    apply intervalIntegral.integral_congr_Ioo_of_le hx.1
    intro y hy
    have hy' : y ∈ Ioo a z := ⟨hy.1, hy.2.trans_le hx.2⟩
    change S.A (U y) (V y) * deriv U y = S.A (γ.U y) (γ.V y) * deriv γ.U y
    rw [(heq y (Ioo_subset_Icc_self hy')).1, (heq y (Ioo_subset_Icc_self hy')).2, hd y hy']
  simp only [curveParallel, hi, (heq x hx).1, (heq x hx).2]

/-- [node prop:charged-observation#boundary-null-normalization]
The complete normalized cylinder chart is constructed from the original
solution and clock cylinder. The actual global C¹ maps and inverses,
positive Jacobians, C¹ parallel gauge and its variation identity are all
witnessed. The outer cylinder is the diagonal; no chart `IsSolution` is
used. The physical scale is arbitrary and positive. -/
theorem Observation.normalized_gauged_chart_of_clock_cylinder
    {e b a z s τ₀ : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (haz : a ≤ z) (γ : ClockCylinder S D b a z) (hs : 0 < s) :
    ∃ U V : ℝ ≃o ℝ, ∃ χ : ℝ → ℝ,
      ContDiff ℝ 1 (U : ℝ → ℝ) ∧ ContDiff ℝ 1 (V : ℝ → ℝ) ∧
      ContDiff ℝ 1 (U.symm : ℝ → ℝ) ∧ ContDiff ℝ 1 (V.symm : ℝ → ℝ) ∧
      ContDiff ℝ 1 χ ∧ χ (U a) = 0 ∧
      (∀ x, 0 < deriv (U : ℝ → ℝ) x) ∧ (∀ x, 0 < deriv (V : ℝ → ℝ) x) ∧
      (∀ x ∈ Icc a z, U x = γ.U x ∧ V x = γ.V x) ∧
      (∀ x ∈ Icc a z, HasDerivAt χ (S.A (U x) (V x)) (U x)) ∧
      eVariationOn (fun x => (gaugeFields e S χ).a (U x) (V x)) (Icc a z) =
        curveCovVar e S S.a γ.U γ.V a z ∧
      ∀ t : ℝ, τ₀ + s * t / 2 ∈ Icc a z →
        let P := nullPullback (rescaleFields (gaugeFields e S χ) s)
          (fun x => U (τ₀ + s * x / 2) / s) (fun x => V (τ₀ + s * x / 2) / s)
        P.r t t = b / s ∧ P.nu t t = -1 / 2 ∧ P.lam t t = 1 / 2 ∧ P.A t t = 0 := by
  obtain ⟨U, V, hU, hV, hUi, hVi, hUp, hVp, heq, hdU, hdV⟩ :=
    Observation.boundary_c1_maps_of_clock_cylinder hS haz γ
  obtain ⟨χ, hχ, hχ0, hχd, hkill⟩ := Observation.boundary_parallel_gauge_of_c1_clock_maps
    hS haz γ U V hUi.continuous hV.continuous heq
  have hA : ContinuousOn (fun x => S.A (U x) (V x)) (Icc a z) := by
    apply hS.cont_A.comp (hU.continuous.prodMk hV.continuous).continuousOn
    intro x hx
    change (U x, V x) ∈ D
    rw [(heq x hx).1, (heq x hx).2]
    exact γ.mem x hx
  have hd (x : ℝ) (hx : x ∈ Ioo a z) : deriv (U : ℝ → ℝ) x = deriv γ.U x := by
    rw [(hdU x (Ioo_subset_Icc_self hx)).deriv,
      ((γ.rate_U x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv,
      (heq x (Ioo_subset_Icc_self hx)).1, (heq x (Ioo_subset_Icc_self hx)).2]
  have hvar := (Observation.gauge_clock_variation_of_derivative e S U V χ hU hA hχd hχ0).trans
    (Observation.curveCovVar_eq_of_clock_agreement e S S.a U V γ heq hd)
  refine ⟨U, V, χ, hU, hV, hUi, hVi, hχ, hχ0, hUp, hVp, heq, hχd, hvar, ?_⟩
  intro t ht
  have hf : HasDerivAt (fun x : ℝ => τ₀ + s * x / 2) (s / 2) t := by
    simpa only [id_eq, mul_one, zero_mul, zero_add] using!
      (((hasDerivAt_id t).const_mul s).div_const 2).const_add τ₀
  have hu : HasDerivAt (fun x => U (τ₀ + s * x / 2))
      (s / (-2 * (gaugeFields e S χ).nu (U (τ₀ + s * t / 2))
        (V (τ₀ + s * t / 2)))) t := by
    convert (hdU _ ht).comp t hf using 1 <;> first | rfl | (simp only [gaugeFields]; ring)
  have hv : HasDerivAt (fun x => V (τ₀ + s * x / 2))
      (s / (2 * (gaugeFields e S χ).lam (U (τ₀ + s * t / 2))
        (V (τ₀ + s * t / 2)))) t := by
    convert (hdV _ ht).comp t hf using 1 <;> first | rfl | (simp only [gaugeFields]; ring)
  apply Observation.boundary_null_normalization_of_clock_rates (gaugeFields e S χ) _ _ hs hu hv
  · change S.nu _ _ < 0
    rw [(heq _ ht).1, (heq _ ht).2]
    exact hS.nu_neg _ (γ.mem _ ht)
  · change 0 < S.lam _ _
    rw [(heq _ ht).1, (heq _ ht).2]
    exact hS.lam_pos _ (γ.mem _ ht)
  · change S.r _ _ = b
    rw [(heq _ ht).1, (heq _ ht).2]
    exact γ.radius _ ht
  · exact hkill _ ht

end EmcsfAcExtension.Global
