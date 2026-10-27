module

public import EmcsfAcExtension.Global.Observation.BoundaryData
public import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Infra.Density.CurveChain
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Global.Observation.CylinderIdentity
import EmcsfAcExtension.Global.Observation.BoundaryCharts

/-! # Transport of the original cylinder tangent equations

These helpers take the original clock tangent rules from internal project record. They
perform the affine clock and physical scale changes explicitly, keeping
the original fields and coordinate maps. No solution assertion on the
observation chart is used.
Source: charged_SF_new_version.tex:L2075–2100; internal project record (B), (C3).
-/

public section

open Set Complex Filter Topology

namespace EmcsfAcExtension.Global

/-- [internal]
An original scalar clock tangent rule transports through the residual
gauge using one derivative of its phase. The clock weights are explicit;
internal project record supplies them from the original solution. -/
theorem Observation.gauge_clock_tangent_of_original_clock_tangent
    (e : ℝ) (S : Fields) (U V χ : ℝ → ℝ) {t du dv dχ : ℝ}
    (hU : HasDerivAt U du t) (hχ : HasDerivAt χ dχ (U t))
    (hφ : HasDerivAt (fun x => S.phi (U x) (V x))
      (du • S.phiU e (U t) (V t) + dv • S.phiV (U t) (V t)) t) :
    HasDerivAt (fun x => (gaugeFields e S χ).phi (U x) (V x))
      (du • (gaugeFields e S χ).phiU e (U t) (V t) +
        dv • (gaugeFields e S χ).phiV (U t) (V t)) t := by
  have hphase : HasDerivAt (fun x => Complex.exp (I * e * χ (U x)))
      (I * e * (dχ * du) * Complex.exp (I * e * χ (U t))) t := by
    convert ((hχ.comp t hU).ofReal_comp.const_mul (I * e)).cexp using 1
    · rfl
    · simp only [Function.comp_apply, Complex.ofReal_mul]
      ring
  apply (hphase.mul hφ).congr_deriv
  simp only [gaugeFields, Fields.phiU, Fields.phiV, hχ.deriv, real_smul,
    Complex.ofReal_sub, div_eq_mul_inv]
  ring

/-- [internal]
The original physical clock sources simplify with exact coefficients.
The electric mass contributions cancel, and the Maxwell current retains
its negative sign. This is pointwise algebra, uniform in all data. -/
theorem Observation.physical_clock_sources (e : ℝ) (S : Fields) {u v b : ℝ}
    (hb : b ≠ 0) (hr : S.r u v = b) (hn : S.nu u v ≠ 0) (hl : S.lam u v ≠ 0)
    (hA : S.A u v = 0) :
    ((-S.nu u v)⁻¹ : ℝ) • S.phiU e u v + (S.lam u v)⁻¹ • S.phiV u v =
      (S.theta u v / S.lam u v - S.xi u v / S.nu u v) / (b : ℂ) ∧
    (-S.nu u v)⁻¹ * S.mU u v + (S.lam u v)⁻¹ * S.mV u v =
      (1 - S.mu u v) / 2 *
        (‖S.theta u v / S.lam u v‖ ^ 2 - ‖S.xi u v / S.nu u v‖ ^ 2) ∧
    (-S.nu u v)⁻¹ * S.QU e u v + (S.lam u v)⁻¹ * S.QV e u v =
      -(e * b) * (starRingEnd ℂ (S.phi u v) *
        (S.theta u v / S.lam u v + S.xi u v / S.nu u v)).im := by
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have hnC : (S.nu u v : ℂ) ≠ 0 := by exact_mod_cast hn
  have hlC : (S.lam u v : ℂ) ≠ 0 := by exact_mod_cast hl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fields.phiU, Fields.phiV, hr, hA, mul_zero, zero_mul,
      sub_zero, real_smul, Complex.ofReal_inv, Complex.ofReal_neg, Complex.ofReal_zero]
    field_simp
    ring
  · simp only [Fields.mU, Fields.mV, norm_div, Complex.norm_real,
      Real.norm_eq_abs, div_pow, sq_abs, hr]
    field_simp
    ring
  · simp only [Fields.QU, Fields.QV, hr, Complex.div_ofReal_im, Complex.div_ofReal_re,
      Complex.mul_im, Complex.add_im, Complex.add_re]
    field_simp
    ring

/-- [internal]
Original scalar and mass clock tangent rules imply the normalized rules
after the affine clock `τ=τ₀+s*t/2`. The mass is divided by `s`, while
the scalar background is retained. internal project record supplies the two tangent inputs;
this helper performs all scale and clock factors. -/
theorem Observation.boundary_clock_equations_of_original_clock_tangents
    (e : ℝ) (S : Fields) (U V : ℝ → ℝ) {s b τ₀ t : ℝ} (hs : 0 < s) (hb : 0 < b)
    (hr : S.r (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) = b)
    (hn : S.nu (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) ≠ 0)
    (hl : S.lam (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) ≠ 0)
    (hA : S.A (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) = 0)
    (hφ : HasDerivAt (fun x => S.phi (U x) (V x))
      (((-S.nu (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ : ℝ) •
        S.phiU e (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) +
        (S.lam (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ •
          S.phiV (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2))) (τ₀ + s * t / 2))
    (hm : HasDerivAt (fun x => S.m (U x) (V x))
      ((-S.nu (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ *
        S.mU (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) +
        (S.lam (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ *
          S.mV (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2))) (τ₀ + s * t / 2)) :
    let τ := τ₀ + s * t / 2
    let y := S.theta (U τ) (V τ) / S.lam (U τ) (V τ)
    let z := S.xi (U τ) (V τ) / S.nu (U τ) (V τ)
    HasDerivAt (fun x => S.phi (U (τ₀ + s * x / 2)) (V (τ₀ + s * x / 2)))
      ((y - z) / (2 * (b / s) : ℝ)) t ∧
    HasDerivAt (fun x => S.m (U (τ₀ + s * x / 2)) (V (τ₀ + s * x / 2)) / s)
      ((1 - S.mu (U τ) (V τ)) * (‖y‖ ^ 2 - ‖z‖ ^ 2) / 4) t := by
  obtain ⟨hφsrc, hmsrc, _⟩ := Observation.physical_clock_sources e S hb.ne' hr hn hl hA
  rw [hφsrc] at hφ
  rw [hmsrc] at hm
  have hf : HasDerivAt (fun x : ℝ => τ₀ + s * x / 2) (s / 2) t := by
    simpa only [id_eq, mul_one, zero_mul, zero_add] using!
      (((hasDerivAt_id t).const_mul s).div_const 2).const_add τ₀
  dsimp only
  constructor
  · convert hφ.scomp t hf using 1
    · rfl
    · simp only [real_smul, Complex.ofReal_div, Complex.ofReal_mul]
      push_cast
      field_simp
  · convert ((hm.comp t hf).div_const s) using 1
    · rfl
    · field_simp
      ring

/-- [node prop:charged-observation#boundary-maxwell-identity]
The original Maxwell clock tangent rule gives the normalized charge
identity, including its negative sign and coefficient `1/2`. Its charged
factor is `(s*e)*(b/s)=e*b`; no chart solution is introduced. -/
theorem Observation.boundary_maxwell_identity_of_original_clock_tangent
    (e : ℝ) (S : Fields) (U V : ℝ → ℝ) {s b τ₀ t : ℝ} (hs : 0 < s) (hb : 0 < b)
    (hr : S.r (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) = b)
    (_hn : S.nu (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) ≠ 0)
    (_hl : S.lam (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) ≠ 0)
    (hQ : HasDerivAt (fun x => S.Q (U x) (V x))
      ((-S.nu (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ *
        S.QU e (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) +
        (S.lam (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ *
          S.QV e (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2))) (τ₀ + s * t / 2)) :
    let τ := τ₀ + s * t / 2
    HasDerivAt (fun x => S.Q (U (τ₀ + s * x / 2)) (V (τ₀ + s * x / 2)) / s)
      (-((s * e) * (b / s) / 2) * (starRingEnd ℂ (S.phi (U τ) (V τ)) *
        (S.theta (U τ) (V τ) / S.lam (U τ) (V τ) +
          S.xi (U τ) (V τ) / S.nu (U τ) (V τ))).im) t := by
  have hsrc : (-S.nu (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ *
        S.QU e (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) +
        (S.lam (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ *
          S.QV e (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) =
      -(e * b) * (starRingEnd ℂ (S.phi (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2))) *
        (S.theta (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) /
          S.lam (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) +
          S.xi (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) /
            S.nu (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))).im := by
    simp only [Fields.QU, Fields.QV, hr, Complex.div_ofReal_im, Complex.div_ofReal_re,
      Complex.mul_im, Complex.add_im, Complex.add_re]
    field_simp
    ring
  rw [hsrc] at hQ
  have hf : HasDerivAt (fun x : ℝ => τ₀ + s * x / 2) (s / 2) t := by
    simpa only [id_eq, mul_one, zero_mul, zero_add] using!
      (((hasDerivAt_id t).const_mul s).div_const 2).const_add τ₀
  dsimp only
  convert ((hQ.comp t hf).div_const s) using 1
  · rfl
  · field_simp

private theorem original_charge_in {e ui u v : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hi : ui < u) (huv : u < v) (hv : v < 0) :
    HasDerivAt (fun x => S.Q x v) (S.QU e u v) u := by
  have hs : inSeg ui v v ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨hx, hxv, rfl⟩
    exact ⟨hx, hxv.trans_lt hv, hxv, hv.le⟩
  have cr := Calculus.continuousOn_in_section hS.cont_r hs
  have cp := Calculus.continuousOn_in_section hS.cont_phi hs
  have cx := Calculus.continuousOn_in_section hS.cont_xi hs
  apply Local.hasDerivAt_of_integralForm_interior ⟨hi, huv⟩
    (((continuousOn_const.mul cr).mul
      (continuous_im.comp_continuousOn (cp.star.mul cx))).mono Ioo_subset_Icc_self)
  intro c d hc hcd hd
  exact (hS.eq_in c d v hcd hd (by
    rintro ⟨x, y⟩ ⟨hcx, hxd, rfl⟩
    exact ⟨hc.le.trans hcx, (hxd.trans hd.le).trans_lt hv, hxd.trans hd.le, hv.le⟩)).2.2.2.1

/-- [internal]
The original Maxwell clock tangent rule follows from continuous sectional
sources and the density chain rule. It is proved pointwise in the clock
interior, rather than restricting a two-dimensional a.e. identity to a
curve. Thus the normalized Maxwell helper has no pending analytic input. -/
theorem Observation.charge_clock_tangent_of_original_solution
    {e ui b a z τ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b a z)
    (hb : 0 < b) (hτ : τ ∈ Ioo a z) :
    HasDerivAt (fun x => S.Q (γ.U x) (γ.V x))
      ((-S.nu (γ.U τ) (γ.V τ))⁻¹ * S.QU e (γ.U τ) (γ.V τ) +
        (S.lam (γ.U τ) (γ.V τ))⁻¹ * S.QV e (γ.U τ) (γ.V τ)) τ := by
  have haz := (hτ.1.trans hτ.2).le
  have ht := Ioo_subset_Icc_self hτ
  have hp := γ.mem τ ht
  obtain ⟨hUm, hVm⟩ := Observation.clock_labels_strictMono hS γ
  have hi : ui < γ.U τ :=
    (γ.mem a ⟨le_rfl, haz⟩).1.trans_lt (hUm ⟨le_rfl, haz⟩ ht hτ.1)
  have hv : γ.V τ < 0 :=
    (hVm ht ⟨haz, le_rfl⟩ hτ.2).trans_le (γ.mem z ⟨haz, le_rfl⟩).2.2.2
  have huv : γ.U τ < γ.V τ := by
    have hle := hS.subset hp
    change γ.U τ ≤ γ.V τ at hle
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · have ha := (hS.axis (γ.U τ) (by simpa only [← h] using hp)).1
      have hr := γ.radius τ ht
      rw [← h, ha] at hr
      exact False.elim (hb.ne' hr.symm)
  have hopen : IsOpen {p : ℝ × ℝ | ui < p.1 ∧ p.1 < p.2 ∧ p.2 < 0} :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter (isOpen_lt continuous_snd continuous_const))
  have hn : origDomain ui ∈ 𝓝 (γ.U τ, γ.V τ) := by
    filter_upwards [hopen.mem_nhds ⟨hi, huv, hv⟩] with p hp'
    exact ⟨hp'.1.le, hp'.2.1.trans hp'.2.2, hp'.2.1.le, hp'.2.2.le⟩
  have cr := (hS.cont_r _ hp).continuousAt hn
  have cp := (hS.cont_phi _ hp).continuousAt hn
  have cx := (hS.cont_xi _ hp).continuousAt hn
  have hQU : ContinuousAt (Function.uncurry (S.QU e)) (γ.U τ, γ.V τ) :=
    (continuousAt_const.mul cr).mul (continuous_im.continuousAt.comp (cp.star.mul cx))
  have hU := (γ.rate_U τ ht).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
  have hV := (γ.rate_V τ ht).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
  have hd := Density.hasDerivAt_trace_of_continuous_incoming_partial hU hV hQU
    (show ∀ᶠ p : ℝ × ℝ in 𝓝 (γ.U τ, γ.V τ),
      HasDerivAt (fun u => S.Q u p.2) (S.QU e p.1 p.2) p.1 from by
      filter_upwards [hopen.mem_nhds ⟨hi, huv, hv⟩] with p hp'
      exact original_charge_in hS hp'.1 hp'.2.1 hp'.2.2)
    (Local.IsSolution.hasDerivAt_charge_out hS (show outSeg (γ.U τ) (γ.U τ) 0 ⊆ origDomain ui by
      rintro ⟨x, y⟩ ⟨rfl, hxy, hy0⟩
      exact ⟨hi.le, huv.trans hv, hxy, hy0⟩) ⟨huv, hv⟩)
  simpa only [smul_eq_mul] using! hd

/-- [node prop:charged-observation#boundary-maxwell-identity]
The normalized Maxwell boundary identity is derived from the original
solution and clock cylinder. The affine clock and charge scale are
explicit, and its right side is invariant under the residual gauge. -/
theorem co_boundary_maxwell_identity
    {e ui b a z s τ₀ t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b a z)
    (hs : 0 < s) (hb : 0 < b) (ht : τ₀ + s * t / 2 ∈ Ioo a z) :
    let τ := τ₀ + s * t / 2
    HasDerivAt (fun x => S.Q (γ.U (τ₀ + s * x / 2)) (γ.V (τ₀ + s * x / 2)) / s)
      (-((s * e) * (b / s) / 2) * (starRingEnd ℂ (S.phi (γ.U τ) (γ.V τ)) *
        (S.theta (γ.U τ) (γ.V τ) / S.lam (γ.U τ) (γ.V τ) +
          S.xi (γ.U τ) (γ.V τ) / S.nu (γ.U τ) (γ.V τ))).im) t := by
  have hmem := γ.mem _ (Ioo_subset_Icc_self ht)
  exact Observation.boundary_maxwell_identity_of_original_clock_tangent e S γ.U γ.V hs hb
    (γ.radius _ (Ioo_subset_Icc_self ht)) (hS.nu_neg _ hmem).ne
    (hS.lam_pos _ hmem).ne' (Observation.charge_clock_tangent_of_original_solution hS γ hb ht)

/-- [internal]
The parallel gauge and normalized clock equations are derived from the
original scalar and mass clock tangents. The potential-zero premise of
the earlier helper is discharged by the constructed gauge derivative;
no solution assertion on the gauged or normalized chart is needed. -/
theorem Observation.boundary_clock_equations_of_parallel_gauge_and_original_tangents
    (e : ℝ) (S : Fields) (U V χ : ℝ → ℝ) {s b τ₀ t : ℝ} (hs : 0 < s) (hb : 0 < b)
    (hr : S.r (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) = b)
    (hn : S.nu (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) ≠ 0)
    (hl : S.lam (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) ≠ 0)
    (hU : HasDerivAt U ((-S.nu (U (τ₀ + s * t / 2))
      (V (τ₀ + s * t / 2)))⁻¹) (τ₀ + s * t / 2))
    (hχ : HasDerivAt χ (S.A (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))
      (U (τ₀ + s * t / 2)))
    (hφ : HasDerivAt (fun x => S.phi (U x) (V x))
      (((-S.nu (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ : ℝ) •
        S.phiU e (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) +
        (S.lam (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ •
          S.phiV (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2))) (τ₀ + s * t / 2))
    (hm : HasDerivAt (fun x => S.m (U x) (V x))
      ((-S.nu (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ *
        S.mU (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) +
        (S.lam (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ *
          S.mV (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2))) (τ₀ + s * t / 2)) :
    let G := gaugeFields e S χ
    let τ := τ₀ + s * t / 2
    let y := G.theta (U τ) (V τ) / G.lam (U τ) (V τ)
    let z := G.xi (U τ) (V τ) / G.nu (U τ) (V τ)
    HasDerivAt (fun x => G.phi (U (τ₀ + s * x / 2)) (V (τ₀ + s * x / 2)))
      ((y - z) / (2 * (b / s) : ℝ)) t ∧
    HasDerivAt (fun x => G.m (U (τ₀ + s * x / 2)) (V (τ₀ + s * x / 2)) / s)
      ((1 - G.mu (U τ) (V τ)) * (‖y‖ ^ 2 - ‖z‖ ^ 2) / 4) t := by
  let G := gaugeFields e S χ
  have hφg := Observation.gauge_clock_tangent_of_original_clock_tangent e S U V χ hU hχ hφ
  have hk := gaugeFields_rhs e S χ (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2))
    (S.A (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2))) hχ
  have hmg : HasDerivAt (fun x => G.m (U x) (V x))
      ((-G.nu (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ *
        G.mU (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) +
        (G.lam (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)))⁻¹ *
          G.mV (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2))) (τ₀ + s * t / 2) := by
    dsimp only [G]
    rw [hk.2.2.1, hk.2.1]
    exact hm
  have hA : G.A (U (τ₀ + s * t / 2)) (V (τ₀ + s * t / 2)) = 0 := by
    simp only [G, gaugeFields, hχ.deriv, sub_self]
  exact Observation.boundary_clock_equations_of_original_clock_tangents e G U V hs hb
    hr hn hl hA hφg hmg

/-- [node prop:charged-observation#boundary-clock-equations]
An original solution and its clock cylinder admit a constructed C¹ parallel
gauge in which both normalized clock equations hold. The scalar and mass
tangents, clock rate and gauge derivative are all discharged. Only the
positive physical length scale is chosen; there are no estimate constants
or regularity premises on independent trace profiles. -/
theorem Observation.boundary_clock_equations_of_solution
    {e ui b a z s τ₀ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (γ : ClockCylinder S (origDomain ui) b a z)
    (haz : a ≤ z) (hs : 0 < s) (hb : 0 < b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ 1 χ ∧ χ (γ.U a) = 0 ∧
      (∀ τ ∈ Icc a z, HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) ∧
      ∀ t, τ₀ + s * t / 2 ∈ Ioo a z →
        let G := gaugeFields e S χ
        let τ := τ₀ + s * t / 2
        let y := G.theta (γ.U τ) (γ.V τ) / G.lam (γ.U τ) (γ.V τ)
        let z := G.xi (γ.U τ) (γ.V τ) / G.nu (γ.U τ) (γ.V τ)
        HasDerivAt (fun x => G.phi (γ.U (τ₀ + s * x / 2))
          (γ.V (τ₀ + s * x / 2))) ((y - z) / (2 * (b / s) : ℝ)) t ∧
        HasDerivAt (fun x => G.m (γ.U (τ₀ + s * x / 2))
          (γ.V (τ₀ + s * x / 2)) / s)
          ((1 - G.mu (γ.U τ) (γ.V τ)) * (‖y‖ ^ 2 - ‖z‖ ^ 2) / 4) t := by
  obtain ⟨U, V, _hU, hV, hUi, _hVi, _hUp, _hVp, heq, _hdU, _hdV⟩ :=
    Observation.boundary_c1_maps_of_clock_cylinder hS haz γ
  obtain ⟨χ, hχ, hχ0, hχd, _⟩ :=
    Observation.boundary_parallel_gauge_of_c1_clock_maps hS haz γ U V
      hUi.continuous hV.continuous heq
  have hd (τ) (hτ : τ ∈ Icc a z) :
      HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ) := by
    simpa only [(heq τ hτ).1, (heq τ hτ).2] using hχd τ hτ
  refine ⟨χ, hχ, ?_, hd, ?_⟩
  · simpa only [(heq a ⟨le_rfl, haz⟩).1] using hχ0
  · intro t ht
    have hmem := γ.mem _ (Ioo_subset_Icc_self ht)
    exact Observation.boundary_clock_equations_of_parallel_gauge_and_original_tangents
      e S γ.U γ.V χ hs hb (γ.radius _ (Ioo_subset_Icc_self ht))
      (hS.nu_neg _ hmem).ne (hS.lam_pos _ hmem).ne'
      (γ.hasDerivAt_U ht) (hd _ (Ioo_subset_Icc_self ht))
      (Cylinder.hasDerivAt_phi hS γ hb ht) (Cylinder.hasDerivAt_mass hS γ hb ht)

end EmcsfAcExtension.Global
