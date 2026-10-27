module

public import EmcsfAcExtension.Global.Observation.ClockTransport
public import EmcsfAcExtension.Global.Observation.BoundaryValues
public import EmcsfAcExtension.Global.Observation.Energy
import EmcsfAcExtension.Global.Observation.BoundaryCharts
import EmcsfAcExtension.Global.Observation.Gauge

/-! # Boundary estimates in the original observation setting

The trace profiles below are the actual original solution in its constructed
parallel frame and affine clock. Their continuity and all three clock
identities are derived from the frozen solution. No normalized solution
with a cylinder as its regular axis is introduced.
Source: charged_SF_new_version.tex:L2075–2106; internal project record (B), (C3).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
The normalized Maxwell identity in a chosen parallel frame follows from
the original solution. The derivative of charge is unchanged by the gauge;
its current identity is transported using the checked gauge right sides. -/
theorem boundary_maxwell_of_parallel_gauge
    {e ui b a z s τ₀ t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (γ : ClockCylinder S (origDomain ui) b a z)
    (χ : ℝ → ℝ) (hs : 0 < s) (hb : 0 < b)
    (ht : τ₀ + s * t / 2 ∈ Ioo a z)
    (hχ : HasDerivAt χ (S.A (γ.U (τ₀ + s * t / 2))
      (γ.V (τ₀ + s * t / 2))) (γ.U (τ₀ + s * t / 2))) :
    let G := gaugeFields e S χ
    let τ := τ₀ + s * t / 2
    HasDerivAt (fun x => G.Q (γ.U (τ₀ + s * x / 2))
      (γ.V (τ₀ + s * x / 2)) / s)
      (-((s * e) * (b / s) / 2) * (starRingEnd ℂ (G.phi (γ.U τ) (γ.V τ)) *
        (G.theta (γ.U τ) (γ.V τ) / G.lam (γ.U τ) (γ.V τ) +
          G.xi (γ.U τ) (γ.V τ) / G.nu (γ.U τ) (γ.V τ))).im) t := by
  let G := gaugeFields e S χ
  have hmem := γ.mem _ (Ioo_subset_Icc_self ht)
  have hk := gaugeFields_rhs e S χ (γ.U (τ₀ + s * t / 2))
    (γ.V (τ₀ + s * t / 2)) _ hχ
  have hd := charge_clock_tangent_of_original_solution hS γ hb ht
  have hQg : HasDerivAt (fun x => G.Q (γ.U x) (γ.V x))
      ((-G.nu (γ.U (τ₀ + s * t / 2)) (γ.V (τ₀ + s * t / 2)))⁻¹ *
        G.QU e (γ.U (τ₀ + s * t / 2)) (γ.V (τ₀ + s * t / 2)) +
        (G.lam (γ.U (τ₀ + s * t / 2)) (γ.V (τ₀ + s * t / 2)))⁻¹ *
        G.QV e (γ.U (τ₀ + s * t / 2)) (γ.V (τ₀ + s * t / 2)))
      (τ₀ + s * t / 2) := by
    dsimp only [G]
    rw [hk.2.2.2.1, hk.2.2.2.2.1]
    exact hd
  exact boundary_maxwell_identity_of_original_clock_tangent e G γ.U γ.V hs hb
    (γ.radius _ (Ioo_subset_Icc_self ht)) (hS.nu_neg _ hmem).ne
    (hS.lam_pos _ hmem).ne' hQg

/-- [internal]
Continuity of all six normalized boundary profiles and their scalar, mass
and charge tangent equations in the actual parallel gauge. This discharges
all regularity and tangent premises of the profile boundary estimates.
There are no estimate constants. -/
theorem boundary_profiles_of_solution
    {e ui b a z s τ₀ T : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (γ : ClockCylinder S (origDomain ui) b a z)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (hs : 0 < s) (hb : 0 < b)
    (hwindow : Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) ⊆ Icc a z)
    (hχd : ∀ τ ∈ Icc a z, HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) :
    let G := gaugeFields e S χ
    let f := fun t => τ₀ + s * t / 2
    let J := Icc (-T * (b / s)) (T * (b / s))
    let φ := fun t => G.phi (γ.U (f t)) (γ.V (f t))
    let y := fun t => G.theta (γ.U (f t)) (γ.V (f t)) / G.lam (γ.U (f t)) (γ.V (f t))
    let z := fun t => G.xi (γ.U (f t)) (γ.V (f t)) / G.nu (γ.U (f t)) (γ.V (f t))
    let m := fun t => S.m (γ.U (f t)) (γ.V (f t)) / s
    let g := fun t => 1 - S.mu (γ.U (f t)) (γ.V (f t))
    let Q := fun t => S.Q (γ.U (f t)) (γ.V (f t)) / s
    ContinuousOn φ J ∧ ContinuousOn y J ∧ ContinuousOn z J ∧
      ContinuousOn m J ∧ ContinuousOn g J ∧ ContinuousOn Q J ∧
    ∀ t ∈ Ioo (-T * (b / s)) (T * (b / s)),
      HasDerivAt φ ((y t - z t) / (2 * (b / s) : ℝ)) t ∧
      HasDerivAt m (g t / 4 * (‖y t‖ ^ 2 - ‖z t‖ ^ 2)) t ∧
      HasDerivAt Q (-((s * e) * (b / s) / 2) *
        (starRingEnd ℂ (φ t) * (y t + z t)).im) t := by
  let G := gaugeFields e S χ
  let f := fun t : ℝ => τ₀ + s * t / 2
  let J := Icc (-T * (b / s)) (T * (b / s))
  have hleft : f (-T * (b / s)) = τ₀ - T * b / 2 := by
    dsimp [f]; field_simp; ring
  have hright : f (T * (b / s)) = τ₀ + T * b / 2 := by
    dsimp [f]; field_simp
  have hf : StrictMono f := by
    intro x y hxy
    dsimp [f]
    exact add_lt_add_right (div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hxy hs)
      (by norm_num : (0 : ℝ) < 2)) τ₀
  have hmap (t) (ht : t ∈ J) : f t ∈ Icc a z := hwindow (by
    constructor
    · rw [← hleft]; exact hf.monotone ht.1
    · rw [← hright]; exact hf.monotone ht.2)
  have hmap' (t) (ht : t ∈ Ioo (-T * (b / s)) (T * (b / s))) : f t ∈ Ioo a z := by
    have hends := hwindow ⟨(show τ₀ - T * b / 2 ≤ τ₀ + T * b / 2 from by
      rw [← hleft, ← hright]; exact hf.monotone (ht.1.trans ht.2).le), le_rfl⟩
    have hstart := hwindow ⟨le_rfl, (show τ₀ - T * b / 2 ≤ τ₀ + T * b / 2 from by
      rw [← hleft, ← hright]; exact hf.monotone (ht.1.trans ht.2).le)⟩
    exact ⟨hstart.1.trans_lt (hleft ▸ hf ht.1), (hright ▸ hf ht.2).trans_le hends.2⟩
  have cf : Continuous f := by fun_prop
  have cp := (γ.continuousOn_trace hS.cont_phi).comp cf.continuousOn hmap
  obtain ⟨cy, cz, cmu⟩ := Cylinder.continuousOn_normalized_traces hS γ
  have cphase : ContinuousOn (fun t => Complex.exp (I * e * χ (γ.U (f t)))) J := by
    have cχ := hχ.continuous.comp_continuousOn
      (γ.c1_U.continuousOn.comp cf.continuousOn hmap)
    exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn cχ)).cexp
  have cφ : ContinuousOn (fun t => G.phi (γ.U (f t)) (γ.V (f t))) J := cphase.mul cp
  have cy' : ContinuousOn (fun t => G.theta (γ.U (f t)) (γ.V (f t)) /
      G.lam (γ.U (f t)) (γ.V (f t))) J := by
    simpa only [G, gaugeFields, mul_div_assoc] using! cphase.mul (cy.comp cf.continuousOn hmap)
  have cz' : ContinuousOn (fun t => G.xi (γ.U (f t)) (γ.V (f t)) /
      G.nu (γ.U (f t)) (γ.V (f t))) J := by
    simpa only [G, gaugeFields, mul_div_assoc] using! cphase.mul (cz.comp cf.continuousOn hmap)
  refine ⟨cφ, cy', cz', ((γ.continuousOn_trace hS.cont_m).comp cf.continuousOn hmap).div_const s,
    continuousOn_const.sub (cmu.comp cf.continuousOn hmap),
    ((γ.continuousOn_trace hS.cont_Q).comp cf.continuousOn hmap).div_const s, ?_⟩
  intro t ht
  have ht' := hmap' t ht
  have hmem := γ.mem _ (Ioo_subset_Icc_self ht')
  have hd := boundary_clock_equations_of_parallel_gauge_and_original_tangents
    e S γ.U γ.V χ hs hb (γ.radius _ (Ioo_subset_Icc_self ht'))
    (hS.nu_neg _ hmem).ne (hS.lam_pos _ hmem).ne'
    (γ.hasDerivAt_U ht') (hχd _ (Ioo_subset_Icc_self ht'))
    (Cylinder.hasDerivAt_phi hS γ hb ht') (Cylinder.hasDerivAt_mass hS γ hb ht')
  refine ⟨hd.1, ?_, boundary_maxwell_of_parallel_gauge hS γ χ hs hb ht'
    (hχd _ (Ioo_subset_Icc_self ht'))⟩
  convert hd.2 using 1 <;> first | rfl | (simp only [gaugeFields_mu]; ring)

/-- [internal]
The actual clock traces in the chosen parallel gauge have exactly the
original covariant variation. Global C¹ clock maps are constructed here;
neither their derivatives nor a variation identity is a premise. -/
theorem gauge_clock_variation_on_cylinder
    {e ui b a z : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (γ : ClockCylinder S (origDomain ui) b a z) (haz : a ≤ z)
    (χ : ℝ → ℝ) (hχd : ∀ τ ∈ Icc a z,
      HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ))
    (hχ0 : χ (γ.U a) = 0) :
    eVariationOn (fun τ => (gaugeFields e S χ).a (γ.U τ) (γ.V τ)) (Icc a z) =
      curveCovVar e S S.a γ.U γ.V a z := by
  obtain ⟨U, V, hU, hV, _hUi, _hVi, _hUp, _hVp, heq, hdU, _hdV⟩ :=
    boundary_c1_maps_of_clock_cylinder hS haz γ
  have hA : ContinuousOn (fun τ => S.A (U τ) (V τ)) (Icc a z) := by
    apply hS.cont_A.comp (hU.continuous.prodMk hV.continuous).continuousOn
    intro τ hτ
    change (U τ, V τ) ∈ origDomain ui
    rw [(heq τ hτ).1, (heq τ hτ).2]
    exact γ.mem τ hτ
  have hd (τ) (hτ : τ ∈ Icc a z) :
      HasDerivAt χ (S.A (U τ) (V τ)) (U τ) := by
    simpa only [(heq τ hτ).1, (heq τ hτ).2] using hχd τ hτ
  have hz : χ (U a) = 0 := by simpa only [(heq a ⟨le_rfl, haz⟩).1] using hχ0
  have hv := gauge_clock_variation_of_derivative e S U V χ hU hA hd hz
  have hder (τ) (hτ : τ ∈ Ioo a z) : deriv (U : ℝ → ℝ) τ = deriv γ.U τ := by
    rw [(hdU τ (Ioo_subset_Icc_self hτ)).deriv, (γ.hasDerivAt_U hτ).deriv,
      (heq τ (Ioo_subset_Icc_self hτ)).1, (heq τ (Ioo_subset_Icc_self hτ)).2]
  have hvar := hv.trans (curveCovVar_eq_of_clock_agreement e S S.a U V γ heq hder)
  rw [← hvar]
  apply eVariationOn.eq_of_eqOn
  intro τ hτ
  change (gaugeFields e S χ).a (γ.U τ) (γ.V τ) = (gaugeFields e S χ).a (U τ) (V τ)
  rw [(heq τ hτ).1, (heq τ hτ).2]

/-- [internal]
The parallel gauge preserves both the outgoing scalar ratio norm and the
measured incoming difference norm, with exact coefficient one. -/
theorem gauge_ratio_norms (e : ℝ) (S : Fields) (χ : ℝ → ℝ) (u v : ℝ) :
    let G := gaugeFields e S χ
    ‖G.theta u v / G.lam u v‖ = ‖S.theta u v / S.lam u v‖ ∧
    ‖G.theta u v / G.lam u v - G.xi u v / G.nu u v‖ =
      ‖S.theta u v / S.lam u v - S.xi u v / S.nu u v‖ := by
  simp [gaugeFields, mul_div_assoc, ← mul_sub, norm_gauge_phase]

/-- [internal]
Every positive-radius original-cylinder point has its complete outgoing
section down to the existing regular axis in the original development.
There is no continuation or normalized-axis premise. -/
theorem cylinder_full_section {e ui b a z τ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (γ : ClockCylinder S (origDomain ui) b a z) (hb : 0 < b)
    (hτ : τ ∈ Icc a z) :
    γ.U τ < γ.V τ ∧ outSeg (γ.U τ) (γ.U τ) (γ.V τ) ⊆ origDomain ui := by
  have hp := γ.mem τ hτ
  have huv : γ.U τ < γ.V τ := by
    have hle : γ.U τ ≤ γ.V τ := hp.2.2.1
    rcases lt_or_eq_of_le hle with hh | hh
    · exact hh
    · have hr := (hS.axis (γ.U τ) (by simpa only [← hh] using hp)).1
      have hb' := γ.radius τ hτ
      rw [← hh, hr] at hb'
      exact False.elim (hb.ne' hb'.symm)
  refine ⟨huv, ?_⟩
  rintro ⟨u, v⟩ ⟨rfl, hu, hv⟩
  exact ⟨hp.1, hp.2.1, hu, hv.trans hp.2.2.2⟩

/-- [internal]
A normalized clock value belongs to the original closed clock window.
This is the exact affine time conversion, with no endpoint upgrade. -/
theorem normalized_clock_mem {T b s τ₀ t : ℝ} (hs : 0 < s)
    (ht : t ∈ Icc (-T * (b / s)) (T * (b / s))) :
    τ₀ + s * t / 2 ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
  have hlo : s / 2 * (-T * (b / s)) = -T * b / 2 := by field_simp
  have hhi : s / 2 * (T * (b / s)) = T * b / 2 := by field_simp
  have h1 := mul_le_mul_of_nonneg_left ht.1 (by positivity : 0 ≤ s / 2)
  have h2 := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0 ≤ s / 2)
  rw [hlo] at h1
  rw [hhi] at h2
  constructor <;> linarith only [h1, h2]

/-- [internal]
Each full outgoing section from the original cylinder lies in its
complete original comparison triangle. Thus the source gap restricts to
all its full sections, including the existing regular axis. -/
theorem cylinder_full_section_subset_triangle {e ui b a z τ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (γ : ClockCylinder S (origDomain ui) b a z) (hτ : τ ∈ Icc a z) :
    outSeg (γ.U τ) (γ.U τ) (γ.V τ) ⊆ triangle (γ.U a) (γ.V z) := by
  have haz : a ≤ z := hτ.1.trans hτ.2
  rintro ⟨u, v⟩ ⟨rfl, hu, hv⟩
  exact ⟨(γ.strictMonoOn_U hS).monotoneOn ⟨le_rfl, haz⟩ hτ hτ.1,
    hu, hv.trans ((γ.strictMonoOn_V hS).monotoneOn hτ ⟨haz, le_rfl⟩ hτ.2)⟩

/-- [internal]
The inverse affine clock maps every physical clock value to the same
normalized closed window, with its exact inverse identity. -/
theorem normalized_clock_inverse {T b s τ₀ τ : ℝ} (hs : 0 < s)
    (hτ : τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2)) :
    2 * (τ - τ₀) / s ∈ Icc (-T * (b / s)) (T * (b / s)) ∧
      τ₀ + s * (2 * (τ - τ₀) / s) / 2 = τ := by
  have hlo : (-T * (b / s)) * s = -T * b := by field_simp
  have hhi : (T * (b / s)) * s = T * b := by field_simp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply (le_div_iff₀ hs).mpr
    rw [hlo]
    linarith only [hτ.1]
  · apply (div_le_iff₀ hs).mpr
    rw [hhi]
    linarith only [hτ.2]
  · field_simp
    ring

end EmcsfAcExtension.Global.Observation
