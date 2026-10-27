module

public import EmcsfAcExtension.Global.Exterior.DerivativeSourceTerminal
public import EmcsfAcExtension.Global.Exterior.OpticsCoefficients

/-! # A common incoming-transport majorant on the entire exterior

The estimate is proved before selecting a frontier or cylinder. Its
constants `264` and `32` are numerical, independent of the carrier and
its final time. Thus the cylinder tail will use the same pointwise
majorant, without substituting a frontier integral for a cylinder one.
Source: `charged_SF_new_version.tex:L1356–L1360`, L1405–L1408; internal project record (I2).
-/

public section

open Set Filter Topology MeasureTheory Complex

namespace EmcsfAcExtension.Global.Exterior

variable {ui e : ℝ} {S : Fields}

/-- [internal]
The incoming covariant normalized source separates into the expansion
coefficient times the outgoing field and the scalar-charge component.
The identity uses positive outgoing expansion and no derivative trace.
No constants occur. -/
theorem normalized_covariant_source_eq (S : Fields) (e u v : ℝ)
    (hl : S.lam u v ≠ 0) :
    (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) *
          (S.theta u v / (S.lam u v : ℂ)) + I * e * S.Q u v * S.phi u v) =
      (-S.rUV u v / S.lam u v : ℝ) * (S.theta u v / (S.lam u v : ℂ)) +
        I * e * (-S.nu u v / (1 - S.mu u v) : ℝ) *
          (S.Q u v / S.r u v : ℝ) * S.phi u v := by
  unfold Fields.rUV
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hl]
  ring

/-- [internal]
At an exterior point the incoming covariant source is bounded by the common
pointwise majorant of internal project record (I2). Coefficients `264` and `32` are universal.
All helper inputs are optical/scalar/charge estimates, not boundary-tail or
density conclusions; `incoming_transport_bound_of_terminal` discharges them.
-/
theorem incoming_transport_bound_of_profiles (h : OriginalData ui e S)
    {u v ell M L n : ℝ} (hp : (u, v) ∈ origDomain ui)
    (hproper : u < v) (hell : 0 < ell) (hr : ell ≤ S.r u v)
    (hM : 0 ≤ M) (hn : 0 ≤ n)
    (hg : 1 / 2 ≤ 1 - S.mu u v) (hnu : -S.nu u v ≤ 2 * n)
    (hphi : ‖S.phi u v‖ ≤ L)
    (hQ : S.Q u v ^ 2 / S.r u v ^ 2 ≤ 64 * (M / S.r u v))
    (ha : |S.rUV u v / S.lam u v| ≤ 264 * n * M / ell ^ 2) :
    ‖(-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) *
          (S.theta u v / (S.lam u v : ℂ)) + I * e * S.Q u v * S.phi u v)‖ ≤
      n * (264 * (M / ell ^ 2) * ‖S.theta u v / (S.lam u v : ℂ)‖ +
        32 * |e| * L * Real.sqrt (M / ell)) := by
  have hl := h.solution.lam_pos (u, v) hp
  have hRp := h.solution.r_pos (u, v) hp hproper
  have hgp := h.solution.one_sub_mu_pos (u, v) hp
  have hnp := neg_pos.mpr (h.solution.nu_neg (u, v) hp)
  have hL : 0 ≤ L := (norm_nonneg _).trans hphi
  have hgeom : -S.nu u v / (1 - S.mu u v) ≤ 4 * n := by
    apply (div_le_iff₀ hgp).2
    have hh := mul_le_mul_of_nonneg_left hg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hn)
    nlinarith only [hh, hnu]
  have hcharge := charge_div_radius_le_of_pointwise hell hr hM hQ
  have hfirst := mul_le_mul_of_nonneg_right ha (norm_nonneg (S.theta u v / (S.lam u v : ℂ)))
  have hsecond := mul_le_mul hgeom hcharge
    (div_nonneg (abs_nonneg (S.Q u v)) hRp.le) (mul_nonneg (by norm_num) hn)
  have hthird := mul_le_mul hsecond hphi (norm_nonneg _)
    (mul_nonneg (mul_nonneg (by norm_num) hn) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
  have hfourth := mul_le_mul_of_nonneg_left hthird (abs_nonneg e)
  rw [normalized_covariant_source_eq S e u v hl.ne']
  calc
    _ ≤ ‖(-S.rUV u v / S.lam u v : ℝ) * (S.theta u v / (S.lam u v : ℂ))‖ +
        ‖I * e * (-S.nu u v / (1 - S.mu u v) : ℝ) *
          (S.Q u v / S.r u v : ℝ) * S.phi u v‖ := norm_add_le _ _
    _ ≤ (264 * n * M / ell ^ 2) * ‖S.theta u v / (S.lam u v : ℂ)‖ +
        |e| * ((4 * n) * (8 * Real.sqrt (M / ell)) * L) := by
      apply add_le_add
      · simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, neg_div, abs_neg] using hfirst
      · simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_div, abs_neg, abs_of_pos hRp, abs_of_pos hnp, abs_of_pos hgp, mul_assoc] using hfourth
    _ = _ := by ring

/-- [internal]
Terminal consumer deriving the common incoming-source majorant everywhere
in the adaptive exterior. The cutoff depends on the fixed solution and
profile; the coefficients `264`, `32` are universal, uniform in all points
and hence in every frontier or cylinder segment subsequently selected. -/
theorem incoming_transport_bound_of_terminal {C : ℝ}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      let L := (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r p.1 0)))
      ‖(-S.nu p.1 p.2 / ((1 - S.mu p.1 p.2) * S.r p.1 p.2) : ℝ) *
          ((S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) *
            (S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)) + I * e * S.Q p.1 p.2 * S.phi p.1 p.2)‖ ≤
        (-S.nu p.1 0) * (264 * (terminalMass S p.1 / ell (terminalRadius S p.1) ^ 2) *
          ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ +
          32 * |e| * L * Real.sqrt (terminalMass S p.1 / ell (terminalRadius S p.1))) := by
  obtain ⟨us, hus, hsource⟩ := source_inputs_of_terminal h M ell hR hC hcollapse hmass
    hell hellsmall hsmall hphi
  obtain ⟨ua, hua, hopt⟩ := incoming_optical_majorant_of_terminal h M ell hR hC hcollapse hmass
    hell hellsmall hsmall hphi
  obtain ⟨un, hun, hratio⟩ := uniform_nu_ratio_of_terminal h M ell hR hC hcollapse hmass
    hell hellsmall hsmall hphi (1 / 2) (by norm_num)
  let u₀ := max us (max ua un)
  refine ⟨u₀, ⟨lt_max_of_lt_left hus.1, max_lt hus.2 (max_lt hua.2 hun.2)⟩, ?_⟩
  intro p hp
  have hs := hsource p.1 p.2 ⟨hp.1, (le_max_left us (max ua un)).trans hp.2.1, hp.2.2⟩
  have ha := hopt p ⟨hp.1,
    (le_max_left ua un).trans ((le_max_right us (max ua un)).trans hp.2.1), hp.2.2⟩
  have hn := hratio p ⟨hp.1,
    (le_max_right ua un).trans ((le_max_right us (max ua un)).trans hp.2.1), hp.2.2⟩
  have htop : (p.1, 0) ∈ origDomain ui := ⟨hp.1.1, hp.1.2.1, hp.1.2.1.le, le_rfl⟩
  have hnt := neg_pos.mpr (h.solution.nu_neg (p.1, 0) htop)
  have hnu : -S.nu p.1 p.2 ≤ 2 * (-S.nu p.1 0) := by
    have hh : S.nu p.1 p.2 / S.nu p.1 0 ≤ 2 := by
      have hhalf := (abs_lt.mp hn).2
      linarith only [hhalf]
    apply (div_le_iff₀ hnt).mp
    simpa only [neg_div_neg_eq] using hh
  exact incoming_transport_bound_of_profiles h hp.1 hs.1 ha.1 hp.2.2
    (mass_nonneg h htop) hnt.le (hs.2.2.2.1 p.2 ⟨le_rfl, hs.2.1⟩) hnu
    (hs.2.2.2.2.1 p.2 ⟨le_rfl, hs.2.1⟩)
    (hs.2.2.2.2.2 p.2 ⟨le_rfl, hs.2.1⟩) ha.2

end EmcsfAcExtension.Global.Exterior
