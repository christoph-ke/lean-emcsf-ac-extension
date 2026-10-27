module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Domains
import EmcsfAcExtension.Global.Renormalized.Incoming
import EmcsfAcExtension.Global.Interaction.ConnectorMass
import EmcsfAcExtension.Global.Interaction.Profiles
import EmcsfAcExtension.Global.Interaction.BoundaryCharge
import EmcsfAcExtension.Local.Calculus.Sections

/-! # The incoming connector scalar equation

The original incoming label is retained, with the positive clock rate
`dτ/du = -ν`. The pulled-back connection is explicit and no outgoing
rough derivative is restricted to a fixed label.
Source: `charged_SF_new_version.tex:L3747–L3837`, approved internal project record.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Interaction

/-- [node sec:charged-terminal-interaction#connector-scalar-equation]
The normalized scalar is AC on each proper incoming connector and obeys
the exact covariant equation after division by its clock rate `-ν`.
Constants: none, with arbitrary coupling and data size. -/
theorem connector_scalar_equation {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hs : inSeg a b v ⊆ D) :
    AbsolutelyContinuousOnInterval (fun u => S.theta u v / (S.lam u v : ℂ)) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b),
        (deriv (fun x => S.theta x v / (S.lam x v : ℂ)) u +
          I * e * S.A u v * (S.theta u v / (S.lam u v : ℂ))) /
            ((-S.nu u v : ℝ) : ℂ) =
          (S.xi u v / (S.nu u v : ℂ) +
            (((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
              (1 - S.mu u v)) * (S.theta u v / (S.lam u v : ℂ)) +
            I * e * S.Q u v * S.phi u v / (1 - S.mu u v)) / (S.r u v : ℂ) := by
  have h := Renormalized.incoming_ratio_section hS hab hbv hs
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2, ae_restrict_mem measurableSet_Icc] with u hu hum
  rw [hu.deriv]
  have hp : (u, v) ∈ D := hs ⟨hum.1, hum.2, rfl⟩
  have hn := Complex.ofReal_ne_zero.mpr (hS.nu_neg _ hp).ne
  simp only [sub_add_cancel, Complex.ofReal_neg]
  field_simp [hn]

/-- [internal] Connector charge from a scalar profile, with the profile
premise discharged by `connector_charge` below. The constant depends only
on `δ, ρ`, before the coupling, scalar amplitude, radius and budget. -/
theorem connector_charge_of_scalar_bound (δ ρ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) :
    ∃ C > 0, ∀ (ui e M₀ : ℝ) (S : Fields),
      IsSolution e S (origDomain ui) → 1 ≤ M₀ →
      ∀ (a b v B E : ℝ), a ≤ b → b < v →
      inSeg a b v ⊆ origDomain ui → 0 < B → 0 ≤ E →
      S.r a v = B → S.m a v / B ≤ E →
      (∀ u ∈ Icc a b, ρ * B ≤ S.r u v) →
      (∀ u ∈ Icc a b, ∀ w ∈ Icc u v, δ ≤ 1 - S.mu u w) →
      (∀ u ∈ Icc a b, ‖S.phi u v‖ ≤ M₀) →
      ∀ u ∈ Icc a b,
        |S.Q u v| / S.r u v ^ 2 ≤ C * |e| * M₀ * Real.sqrt E := by
  obtain ⟨A, hA, hcharge⟩ := ct_boundary_charge_of_boundary_bound δ hδ hδ1
  refine ⟨2 * A / Real.sqrt ρ, by positivity, ?_⟩
  intro ui e M₀ S hS hM a b v B E hab hbv hs hB hE hstart hbudget hrange hgap hphi u hu
  have hp : (u, v) ∈ origDomain ui := hs ⟨hu.1, hu.2, rfl⟩
  have huv := hu.2.trans_lt hbv
  have hcore : outSeg u u v ⊆ origDomain ui := by
    rintro ⟨x, w⟩ ⟨rfl, hw⟩
    exact ⟨hp.1, hp.2.1, hw.1, hw.2.trans hp.2.2.2⟩
  have hm := (connector_mass_and_flux hδ hρ hS hab hbv hs hB hE
    hstart hbudget hrange (fun x hx => hgap x hx v ⟨(hx.2.trans_lt hbv).le, le_rfl⟩) u hu).2.1
  let η := S.m u v / S.r u v
  have hη : 0 ≤ η := div_nonneg hm.1 (hS.r_pos _ hp huv).le
  have hη1 : η ≤ 1 := by
    have hμ := hS.one_sub_mu_pos _ hp
    change 0 < 1 - 2 * S.m u v / S.r u v at hμ
    dsimp only [η]
    rw [mul_div_assoc] at hμ
    linarith only [hμ]
  have hηroot : η ≤ Real.sqrt η :=
    (Real.le_sqrt hη hη).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hη1 hη])
  have hroot : Real.sqrt η ≤ Real.sqrt E / Real.sqrt ρ := by
    rw [← Real.sqrt_div hE]
    exact Real.sqrt_le_sqrt hm.2
  have hinner : M₀ * Real.sqrt η + η ≤ 2 * M₀ * (Real.sqrt E / Real.sqrt ρ) := by
    have h1 := mul_le_mul_of_nonneg_left hroot (by linarith only [hM] : 0 ≤ M₀)
    have h2 := mul_le_mul_of_nonneg_right hM (Real.sqrt_nonneg η)
    nlinarith only [h1, h2, hηroot]
  calc
    _ ≤ A * |e| * (M₀ * Real.sqrt η + η) :=
      hcharge e M₀ S (origDomain ui) u v hS huv hcore (hgap u hu) (hphi u hu)
    _ ≤ A * |e| * (2 * M₀ * (Real.sqrt E / Real.sqrt ρ)) :=
      mul_le_mul_of_nonneg_left hinner (mul_nonneg hA.le (abs_nonneg e))
    _ = _ := by ring

/-- [internal] The electric scalar forcing from a charge and scalar profile.
Both profile premises are discharged by the node theorems below. The exact
coefficient is `C / δ`, uniform in all fields and scales. -/
theorem electric_forcing_of_profiles {δ C e M₀ E r μ Q : ℝ} {φ : ℂ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hM : 0 ≤ M₀) (hr : 0 < r)
    (hg : δ ≤ 1 - μ) (hφ : ‖φ‖ ≤ M₀)
    (hq : |Q| / r ^ 2 ≤ C * |e| * M₀ * Real.sqrt E) :
    ‖I * (e : ℂ) * Q * φ / (((1 - μ) * r : ℝ) : ℂ)‖ ≤
      (C / δ) * e ^ 2 * M₀ ^ 2 * Real.sqrt E * r := by
  have hgap := hδ.trans_le hg
  have hQ := (div_le_iff₀ (sq_pos_of_pos hr)).mp hq
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_I, one_mul,
    Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (mul_pos hgap hr)]
  calc
    _ ≤ |e| * ((C * |e| * M₀ * Real.sqrt E) * r ^ 2) * M₀ / ((1 - μ) * r) :=
      div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hQ (abs_nonneg e)) hφ
          (norm_nonneg _) (by positivity)) (mul_pos hgap hr).le
    _ = (C * e ^ 2 * M₀ ^ 2 * Real.sqrt E * r) / (1 - μ) := by
      field_simp
      simp only [sq_abs]
      ring
    _ ≤ (C * e ^ 2 * M₀ ^ 2 * Real.sqrt E * r) / δ :=
      div_le_div_of_nonneg_left (by positivity) hδ hg
    _ = _ := by ring

/-- [internal] The connector radius moment is at most `B² / 2` at every
partial endpoint. The exact coefficient is independent of duration. -/
theorem connector_radius_moment {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v B : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hs : inSeg a b v ⊆ D) (hstart : S.r a v = B) :
    (∫ u in a..b, S.r u v * (-S.nu u v)) ≤ B ^ 2 / 2 := by
  have h := Local.IsSolution.in_section hS hab hbv hs
  have cr := Calculus.continuousOn_in_section hS.cont_r hs
  have cn := Calculus.continuousOn_in_section hS.cont_nu hs
  have hac := (h.1.1.mul h.1.1).const_mul (-1 / 2 : ℝ)
  have hd : ∀ᵐ u, u ∈ uIcc a b → HasDerivAt
      (fun x => (-1 / 2 : ℝ) * (S.r x v * S.r x v))
      (S.r u v * (-S.nu u v)) u := by
    have hh := (ae_restrict_iff' measurableSet_Icc).mp h.1.2
    filter_upwards [hh] with u hu hum
    exact (((hu (by simpa only [uIcc_of_le hab] using hum)).mul
      (hu (by simpa only [uIcc_of_le hab] using hum))).const_mul (-1 / 2 : ℝ)).congr_deriv (by ring)
  have heq := hac.integral_eq_sub_of_ae_hasDerivAt_normed
    ((cr.mul cn.neg).intervalIntegrable_of_Icc (μ := volume) hab) hd
  dsimp only [Pi.mul_apply, Pi.neg_apply] at heq
  rw [hstart] at heq
  nlinarith only [heq, sq_nonneg (S.r b v)]

/-- [internal] Integrated electric forcing from the derived scalar profile.
Its constant depends only on `δ, ρ`; the `sqrt E` factor is retained, also
at zero budget, and no clock duration occurs. -/
theorem connector_electric_integral_of_scalar_bound (δ ρ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) :
    ∃ C > 0, ∀ (ui e M₀ : ℝ) (S : Fields),
      IsSolution e S (origDomain ui) → 1 ≤ M₀ →
      ∀ (a b v B E : ℝ), a ≤ b → b < v →
      inSeg a b v ⊆ origDomain ui → 0 < B → 0 ≤ E →
      S.r a v = B → S.m a v / B ≤ E →
      (∀ u ∈ Icc a b, ρ * B ≤ S.r u v) →
      (∀ u ∈ Icc a b, ∀ w ∈ Icc u v, δ ≤ 1 - S.mu u w) →
      (∀ u ∈ Icc a b, ‖S.phi u v‖ ≤ M₀) →
      (∫ u in a..b, ‖I * (e : ℂ) * S.Q u v * S.phi u v /
        (((1 - S.mu u v) * S.r u v : ℝ) : ℂ)‖ * (-S.nu u v)) ≤
          C * e ^ 2 * M₀ ^ 2 * B ^ 2 * Real.sqrt E := by
  obtain ⟨C, hC, hcharge⟩ := connector_charge_of_scalar_bound δ ρ hδ hδ1 hρ
  refine ⟨C / (2 * δ), by positivity, ?_⟩
  intro ui e M₀ S hS hM a b v B E hab hbv hs hB hE hstart hbudget hrange hgap hphi
  have hq := hcharge ui e M₀ S hS hM a b v B E hab hbv hs hB hE hstart hbudget hrange hgap hphi
  have hp (u : ℝ) (hu : u ∈ Icc a b) : (u, v) ∈ origDomain ui := hs ⟨hu.1, hu.2, rfl⟩
  have cr := Calculus.continuousOn_in_section hS.cont_r hs
  have cn := Calculus.continuousOn_in_section hS.cont_nu hs
  have cm := Calculus.continuousOn_in_section hS.cont_m hs
  have cq := Calculus.continuousOn_in_section hS.cont_Q hs
  have cp := Calculus.continuousOn_in_section hS.cont_phi hs
  have hr u (hu : u ∈ Icc a b) := hS.r_pos _ (hp u hu) (hu.2.trans_lt hbv)
  have cμ : ContinuousOn (fun u => S.mu u v) (Icc a b) :=
    (continuousOn_const.mul cm).div cr (fun u hu => (hr u hu).ne')
  have cf : ContinuousOn (fun u => ‖I * (e : ℂ) * S.Q u v * S.phi u v /
      (((1 - S.mu u v) * S.r u v : ℝ) : ℂ)‖) (Icc a b) :=
    (((continuousOn_const.mul (continuous_ofReal.comp_continuousOn cq)).mul cp).div
    (continuous_ofReal.comp_continuousOn ((continuousOn_const.sub cμ).mul cr))
    (fun u hu => Complex.ofReal_ne_zero.mpr (mul_ne_zero
      (hδ.trans_le (hgap u hu v ⟨(hu.2.trans_lt hbv).le, le_rfl⟩)).ne' (hr u hu).ne'))).norm
  have hle := intervalIntegral.integral_mono_on hab
    ((cf.mul cn.neg).intervalIntegrable_of_Icc (μ := volume) hab)
    (((cr.mul cn.neg).const_mul ((C / δ) * e ^ 2 * M₀ ^ 2 * Real.sqrt E)).intervalIntegrable_of_Icc
      (μ := volume) hab) (fun u hu => by
        have he := electric_forcing_of_profiles hδ hC.le
          (by linarith only [hM] : 0 ≤ M₀) (hr u hu)
          (hgap u hu v ⟨(hu.2.trans_lt hbv).le, le_rfl⟩) (hphi u hu) (hq u hu)
        simpa only [Pi.mul_apply, Pi.neg_apply, mul_assoc] using
          mul_le_mul_of_nonneg_right he (neg_pos.mpr (hS.nu_neg _ (hp u hu))).le)
  rw [intervalIntegral.integral_const_mul] at hle
  calc
    _ ≤ _ := hle
    _ ≤ ((C / δ) * e ^ 2 * M₀ ^ 2 * Real.sqrt E) * (B ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (connector_radius_moment hS hab hbv hs hstart) (by positivity)
    _ = _ := by ring

/-- [internal] Specialization of the proved scalar envelope to the exterior
of an incoming connector. `M₀` is the source formula with terminal bound
`H`; no scalar bound on the connector or its core is assumed. -/
theorem connector_scalar_profile {ui e a b v δ c Λ F ε Jstop H : ℝ}
    {S : Fields} {g : ℝ → ℝ} (h : OriginalData ui e S)
    (hab : a ≤ b) (hia : ui ≤ a) (hbv : b < v) (hv : v ≤ 0)
    (hc : 0 < c) (hF : 0 ≤ F) (hF1 : F < 1) (hJstop : 0 ≤ Jstop)
    (hstop : ExteriorStops S (exteriorDomain ui a b (fun _ => v)) δ c Λ F ε)
    (hterm : ∀ u ∈ Icc a b, ‖S.phi u 0‖ ≤ H)
    (hg : IntegrableOn g (Icc v 0))
    (hg0 : ∀ᵐ w ∂volume.restrict (Icc v 0), 0 ≤ g w)
    (hmajor : ∀ u ∈ Icc a b, ∀ᵐ w ∂volume.restrict (Icc v 0),
      ‖weightedJ S u w‖ ≤ g w)
    (hJ : (∫ w in v..0, g w) ≤ Jstop) :
    let M₀ := 1 + H + (F + c⁻¹ * Jstop) / (1 - F ^ 2)
    1 ≤ M₀ ∧ ∀ u ∈ Icc a b, ‖S.phi u v‖ ≤ M₀ := by
  have hH : 0 ≤ H := (norm_nonneg _).trans (hterm a ⟨le_rfl, hab⟩)
  have hp : 0 < 1 - F ^ 2 := by nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  have hM : 1 ≤ 1 + H + (F + c⁻¹ * Jstop) / (1 - F ^ 2) := by
    have hn : 0 ≤ H + (F + c⁻¹ * Jstop) / (1 - F ^ 2) := by positivity
    linarith only [hn]
  refine ⟨hM, ?_⟩
  have hprof := scalar_profile_of_stops h hc hF hF1
    (u₀ := a) (u₁ := b) (v₀ := v) (vb := fun _ => v)
    (fun u hu => ⟨hia.trans hu.1, hu.2.trans_lt hbv, hv, le_rfl⟩)
    hstop hterm hg hg0 (fun u hu => (hmajor u hu).mono fun _ hx _ => hx) hJ
  intro u hu
  exact hprof (u, v) ⟨⟨hia.trans hu.1, (hu.2.trans_lt hbv).trans_le hv,
    (hu.2.trans_lt hbv).le, hv⟩, hu.1, hu.2, le_rfl⟩

/-- [node sec:charged-terminal-interaction#connector-charge]
Charge at every point of the connector is bounded by the square root
of its preceding mass budget. The source scalar envelope is derived from
its row data. The constant depends only on `δ, ρ`; it is uniform in
coupling, amplitude, radius, budget and all partial endpoints. -/
theorem connector_charge (δ ρ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) :
    ∃ C > 0, ∀ (c Λ F ε : ℝ), 0 < c → 0 ≤ F → F < 1 →
    ∀ (ui e a b v B E H Jstop : ℝ) (S : Fields) (g : ℝ → ℝ),
      OriginalData ui e S → a ≤ b → ui ≤ a → b < v → v ≤ 0 →
      0 ≤ Jstop → 0 < B → 0 ≤ E → S.r a v = B → S.m a v / B ≤ E →
      (∀ u ∈ Icc a b, ρ * B ≤ S.r u v) →
      ExteriorStops S (exteriorDomain ui a b (fun _ => v)) δ c Λ F ε →
      (∀ u ∈ Icc a b, ∀ w ∈ Icc u 0, δ ≤ 1 - S.mu u w) →
      (∀ u ∈ Icc a b, ‖S.phi u 0‖ ≤ H) →
      IntegrableOn g (Icc v 0) →
      (∀ᵐ w ∂volume.restrict (Icc v 0), 0 ≤ g w) →
      (∀ u ∈ Icc a b, ∀ᵐ w ∂volume.restrict (Icc v 0), ‖weightedJ S u w‖ ≤ g w) →
      (∫ w in v..0, g w) ≤ Jstop →
      let M₀ := 1 + H + (F + c⁻¹ * Jstop) / (1 - F ^ 2)
      ∀ u ∈ Icc a b, |S.Q u v| / S.r u v ^ 2 ≤ C * |e| * M₀ * Real.sqrt E := by
  obtain ⟨C, hC, hbound⟩ := connector_charge_of_scalar_bound δ ρ hδ hδ1 hρ
  refine ⟨C, hC, ?_⟩
  intro c Λ F ε hc hF hF1 ui e a b v B E H Jstop S g h hab hia hbv hv hJstop hB hE
    hstart hbudget hrange hstop hcore hterm hg hg0 hmajor hJ
  obtain ⟨hM, hphi⟩ := connector_scalar_profile h hab hia hbv hv hc hF hF1
    hJstop hstop hterm hg hg0 hmajor hJ
  apply hbound ui e _ S h.solution hM a b v B E hab hbv
    (by
      rintro ⟨u, w⟩ ⟨hu, hub, rfl⟩
      exact ⟨hia.trans hu, (hub.trans_lt hbv).trans_le hv, (hub.trans_lt hbv).le, hv⟩)
    hB hE hstart hbudget hrange
    (fun u hu w hw => hcore u hu w ⟨hw.1, hw.2.trans hv⟩) hphi

/-- [node sec:charged-terminal-interaction#connector-electric-integral]
Integrated electric forcing on any full or partial connector, retaining
the multiplicative `sqrt E`. The source-defined scalar envelope is proved,
not assumed. The positive constant depends only on `δ, ρ`, before all
solution data and durations; the estimate includes zero budget. -/
theorem connector_electric_integral (δ ρ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) :
    ∃ C > 0, ∀ (c Λ F ε : ℝ), 0 < c → 0 ≤ F → F < 1 →
    ∀ (ui e a b v B E H Jstop : ℝ) (S : Fields) (g : ℝ → ℝ),
      OriginalData ui e S → a ≤ b → ui ≤ a → b < v → v ≤ 0 →
      0 ≤ Jstop → 0 < B → 0 ≤ E → S.r a v = B → S.m a v / B ≤ E →
      (∀ u ∈ Icc a b, ρ * B ≤ S.r u v) →
      ExteriorStops S (exteriorDomain ui a b (fun _ => v)) δ c Λ F ε →
      (∀ u ∈ Icc a b, ∀ w ∈ Icc u 0, δ ≤ 1 - S.mu u w) →
      (∀ u ∈ Icc a b, ‖S.phi u 0‖ ≤ H) →
      IntegrableOn g (Icc v 0) →
      (∀ᵐ w ∂volume.restrict (Icc v 0), 0 ≤ g w) →
      (∀ u ∈ Icc a b, ∀ᵐ w ∂volume.restrict (Icc v 0), ‖weightedJ S u w‖ ≤ g w) →
      (∫ w in v..0, g w) ≤ Jstop →
      let M₀ := 1 + H + (F + c⁻¹ * Jstop) / (1 - F ^ 2)
      (∫ u in a..b, ‖I * (e : ℂ) * S.Q u v * S.phi u v /
        (((1 - S.mu u v) * S.r u v : ℝ) : ℂ)‖ * (-S.nu u v)) ≤
          C * e ^ 2 * M₀ ^ 2 * B ^ 2 * Real.sqrt E := by
  obtain ⟨C, hC, hbound⟩ := connector_electric_integral_of_scalar_bound δ ρ hδ hδ1 hρ
  refine ⟨C, hC, ?_⟩
  intro c Λ F ε hc hF hF1 ui e a b v B E H Jstop S g h hab hia hbv hv hJstop hB hE
    hstart hbudget hrange hstop hcore hterm hg hg0 hmajor hJ
  obtain ⟨hM, hphi⟩ := connector_scalar_profile h hab hia hbv hv hc hF hF1
    hJstop hstop hterm hg hg0 hmajor hJ
  apply hbound ui e _ S h.solution hM a b v B E hab hbv
    (by
      rintro ⟨u, w⟩ ⟨hu, hub, rfl⟩
      exact ⟨hia.trans hu, (hub.trans_lt hbv).trans_le hv, (hub.trans_lt hbv).le, hv⟩)
    hB hE hstart hbudget hrange
    (fun u hu w hw => hcore u hu w ⟨hw.1, hw.2.trans hv⟩) hphi

end EmcsfAcExtension.Global.Interaction
