module

public import EmcsfAcExtension.Global.Observation.CylinderClock
public import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Infra.Null.IntegralForm
import EmcsfAcExtension.Infra.Density.CurveChain

/-! # Exact scalar and mass flux on a cylinder

The frozen integral equations give pointwise sectional derivatives off the
axis. A continuous incoming partial gives the chain rule on an interior
cylinder point. Strictly increasing clock labels put every such point in
the interior of the original development. The electric terms cancel with
opposite signs, as in approved internal project record, `eq:co-cylinder-flux`.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global

namespace Cylinder

private theorem interior_nhds {ui : ℝ} {p : ℝ × ℝ}
    (hi : ui < p.1) (hp : p.1 < p.2) (h0 : p.2 < 0) :
    origDomain ui ∈ 𝓝 p := by
  have hopen : IsOpen {q : ℝ × ℝ | ui < q.1 ∧ q.1 < q.2 ∧ q.2 < 0} :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  filter_upwards [hopen.mem_nhds ⟨hi, hp, h0⟩] with q hq
  exact ⟨hq.1.le, hq.2.1.trans hq.2.2, hq.2.1.le, hq.2.2.le⟩

private theorem phi_in {e ui v u : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (h0 : v < 0) (hu : u ∈ Ioo ui v) :
    HasDerivAt (fun x => S.phi x v) (S.phiU e u v) u := by
  have hs : inSeg ui v v ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff (hu.1.trans hu.2).le).2
      ⟨le_rfl, h0, le_rfl, h0.le⟩
  have hp (x : ℝ) (hx : x ∈ Ioo ui v) : (x, v) ∈ origDomain ui :=
    hs ⟨hx.1.le, hx.2.le, rfl⟩
  have cx := (Local.continuousOn_in_section hS.cont_xi hs).mono Ioo_subset_Icc_self
  have cr := (Local.continuousOn_in_section hS.cont_r hs).mono Ioo_subset_Icc_self
  have ca := (Local.continuousOn_in_section hS.cont_A hs).mono Ioo_subset_Icc_self
  have cp := (Local.continuousOn_in_section hS.cont_phi hs).mono Ioo_subset_Icc_self
  have hc : ContinuousOn (fun x => S.phiU e x v) (Ioo ui v) := by
    change ContinuousOn (fun x => S.xi x v / (S.r x v : ℂ) -
      I * e * S.A x v * S.phi x v) (Ioo ui v)
    exact (cx.div (Complex.continuous_ofReal.comp_continuousOn cr)
      (fun x hx => Complex.ofReal_ne_zero.mpr (hS.r_pos _ (hp x hx) hx.2).ne')).sub
        ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ca)).mul cp)
  apply Local.hasDerivAt_of_integralForm_interior hu hc
  intro c d hc hcd hd
  exact (hS.eq_in c d v hcd hd (fun p hp =>
    hs ⟨hc.le.trans hp.1, hp.2.1.trans hd.le, hp.2.2⟩)).2.2.2.2.1

private theorem phi_out {e ui u v : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hi : ui ≤ u) (hv : v ∈ Ioo u 0) :
    HasDerivAt (S.phi u) (S.phiV u v) v := by
  have hs : outSeg u u 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff (hv.1.trans hv.2).le).2
      ⟨hi, hv.1.trans hv.2, le_rfl, le_rfl⟩
  have hc : ContinuousOn (S.phiV u) (Ioo u 0) :=
    ((Local.continuousOn_out_section hS.cont_theta hs).mono Ioo_subset_Icc_self).div
      (Complex.continuous_ofReal.comp_continuousOn
        ((Local.continuousOn_out_section hS.cont_r hs).mono Ioo_subset_Icc_self))
      (fun x hx => Complex.ofReal_ne_zero.mpr
        (hS.r_pos (u, x) (hs ⟨rfl, hx.1.le, hx.2.le⟩) hx.1).ne')
  apply Local.hasDerivAt_of_integralForm_interior hv hc
  intro c d hc hcd hd
  exact (hS.eq_out u c d hc hcd (fun p hp =>
    hs ⟨hp.1, hc.le.trans hp.2.1, hp.2.2.trans hd.le⟩)).2.2.2.2.2.1

/-- [internal] An interior clock point of a positive-radius cylinder lies
strictly inside both original coordinate boundaries and off the axis. -/
theorem interior_labels {e ui b s t τ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hτ : τ ∈ Ioo s t) :
    ui < γ.U τ ∧ γ.U τ < γ.V τ ∧ γ.V τ < 0 := by
  have hst := hτ.1.trans hτ.2
  have hs := γ.mem s (left_mem_Icc.mpr hst.le)
  have ht := γ.mem t (right_mem_Icc.mpr hst.le)
  have hp := γ.mem τ (Ioo_subset_Icc_self hτ)
  have hu : ui < γ.U τ := hs.1.trans_lt
    (γ.strictMonoOn_U hS (left_mem_Icc.mpr hst.le) (Ioo_subset_Icc_self hτ) hτ.1)
  have hv : γ.V τ < 0 :=
    (γ.strictMonoOn_V hS (Ioo_subset_Icc_self hτ) (right_mem_Icc.mpr hst.le) hτ.2).trans_le
      ht.2.2.2
  refine ⟨hu, lt_of_le_of_ne hp.2.2.1 ?_, hv⟩
  intro heq
  have ha := (hS.axis (γ.U τ) (by simpa only [← heq] using hp)).1
  have hr := γ.radius τ (Ioo_subset_Icc_self hτ)
  rw [← heq, ha] at hr
  exact (ne_of_gt hb) hr.symm

private theorem massU_continuousAt {e ui u v : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hi : ui < u) (huv : u < v) (hv : v < 0) :
    ContinuousAt (Function.uncurry S.mU) (u, v) := by
  have hp : (u, v) ∈ origDomain ui := ⟨hi.le, huv.trans hv, huv.le, hv.le⟩
  have hn := interior_nhds (p := (u, v)) hi huv hv
  have cr := (hS.cont_r _ hp).continuousAt hn
  have cm := (hS.cont_m _ hp).continuousAt hn
  have cn := (hS.cont_nu _ hp).continuousAt hn
  have cq := (hS.cont_Q _ hp).continuousAt hn
  have cx := (hS.cont_xi _ hp).continuousAt hn
  have hr := (hS.r_pos _ hp huv).ne'
  have hnu := (hS.nu_neg _ hp).ne
  exact ((continuousAt_const.sub ((continuousAt_const.mul cm).div cr hr)).mul
    (cx.norm.pow 2) |>.div (continuousAt_const.mul cn) (mul_ne_zero (by norm_num) hnu)).add
      (((cq.pow 2).mul cn).div (continuousAt_const.mul (cr.pow 2))
        (mul_ne_zero (by norm_num) (pow_ne_zero _ hr)))

/-- [internal] Pointwise mass chain rule obtained from continuous sectional
partials, rather than a restriction of a two-dimensional a.e. derivative. -/
theorem hasDerivAt_mass {e ui b s t τ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hτ : τ ∈ Ioo s t) :
    HasDerivAt (fun x => S.m (γ.U x) (γ.V x))
      ((-S.nu (γ.U τ) (γ.V τ))⁻¹ * S.mU (γ.U τ) (γ.V τ) +
        (S.lam (γ.U τ) (γ.V τ))⁻¹ * S.mV (γ.U τ) (γ.V τ)) τ := by
  obtain ⟨hi, huv, hv⟩ := interior_labels hS γ hb hτ
  apply Density.hasDerivAt_trace_of_continuous_incoming_partial
    (γ.hasDerivAt_U hτ) (γ.hasDerivAt_V hτ) (massU_continuousAt hS hi huv hv)
  · have hopen : IsOpen {p : ℝ × ℝ | ui < p.1 ∧ p.1 < p.2 ∧ p.2 < 0} :=
      (isOpen_lt continuous_const continuous_fst).inter
        ((isOpen_lt continuous_fst continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const))
    filter_upwards [hopen.mem_nhds ⟨hi, huv, hv⟩] with p hp
    exact Local.IsSolution.hasDerivAt_mass_in hS
      ((inSeg_subset_origDomain_iff (hp.1.trans hp.2.1).le).2
        ⟨le_rfl, hp.2.2, le_rfl, hp.2.2.le⟩) ⟨hp.1, hp.2.1⟩
  · exact Local.IsSolution.hasDerivAt_mass_out hS
      ((outSeg_subset_origDomain_iff (huv.trans hv).le).2
        ⟨hi.le, huv.trans hv, le_rfl, le_rfl⟩) ⟨huv, hv⟩

/-- [internal] The scalar chain rule uses only the original integral class
and the two clock rates. -/
theorem hasDerivAt_phi {e ui b s t τ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hτ : τ ∈ Ioo s t) :
    HasDerivAt (fun x => S.phi (γ.U x) (γ.V x))
      ((-S.nu (γ.U τ) (γ.V τ))⁻¹ • S.phiU e (γ.U τ) (γ.V τ) +
        (S.lam (γ.U τ) (γ.V τ))⁻¹ • S.phiV (γ.U τ) (γ.V τ)) τ := by
  obtain ⟨hi, huv, hv⟩ := interior_labels hS γ hb hτ
  have hp := γ.mem τ (Ioo_subset_Icc_self hτ)
  have hn := interior_nhds (p := (γ.U τ, γ.V τ)) hi huv hv
  have cr := (hS.cont_r _ hp).continuousAt hn
  have cp := (hS.cont_phi _ hp).continuousAt hn
  have ca := (hS.cont_A _ hp).continuousAt hn
  have cx := (hS.cont_xi _ hp).continuousAt hn
  have hc : ContinuousAt (Function.uncurry (S.phiU e)) (γ.U τ, γ.V τ) :=
    (cx.div cr.ofReal (Complex.ofReal_ne_zero.mpr (hS.r_pos _ hp huv).ne')).sub
      ((continuousAt_const.mul ca.ofReal).mul cp)
  apply Density.hasDerivAt_trace_of_continuous_incoming_partial
    (γ.hasDerivAt_U hτ) (γ.hasDerivAt_V hτ) hc
  · have hopen : IsOpen {p : ℝ × ℝ | ui < p.1 ∧ p.1 < p.2 ∧ p.2 < 0} :=
      (isOpen_lt continuous_const continuous_fst).inter
        ((isOpen_lt continuous_fst continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const))
    filter_upwards [hopen.mem_nhds ⟨hi, huv, hv⟩] with p hp
    exact phi_in hS hp.2.2 ⟨hp.1, hp.2.1⟩
  · exact phi_out hS hi.le ⟨huv, hv⟩

/-- [internal] The two electric mass contributions cancel exactly under the
constant-radius clock rates. No field equation or size bound is assumed. -/
theorem mass_clock_cancellation (S : Fields) (u v : ℝ)
    (hr : S.r u v ≠ 0) (hn : S.nu u v ≠ 0) (hl : S.lam u v ≠ 0) :
    (-S.nu u v)⁻¹ * S.mU u v + (S.lam u v)⁻¹ * S.mV u v =
      (1 - S.mu u v) / 2 *
        (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 -
          ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2) := by
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  dsimp [Fields.mU, Fields.mV]
  field_simp [hr, hn, hl]
  ring

/-- [internal] The scalar cylinder derivative with the pulled-back connection
written explicitly. There is no electric source in the covariant flux. -/
theorem hasDerivAt_scalar_flux {e ui b s t τ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hτ : τ ∈ Ioo s t) :
    HasDerivAt (fun x => S.phi (γ.U x) (γ.V x))
      ((S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ) -
          S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ)) / (b : ℂ) -
        I * e * S.A (γ.U τ) (γ.V τ) *
          ((-S.nu (γ.U τ) (γ.V τ))⁻¹ : ℝ) * S.phi (γ.U τ) (γ.V τ)) τ := by
  apply (hasDerivAt_phi hS γ hb hτ).congr_deriv
  have hp := γ.mem τ (Ioo_subset_Icc_self hτ)
  have hn := Complex.ofReal_ne_zero.mpr (hS.nu_neg _ hp).ne
  have hl := Complex.ofReal_ne_zero.mpr (hS.lam_pos _ hp).ne'
  have hr := γ.radius τ (Ioo_subset_Icc_self hτ)
  simp only [Fields.phiU, Fields.phiV, hr, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_neg]
  field_simp [hn, hl, Complex.ofReal_ne_zero.mpr hb.ne']
  ring

/-- [internal] The ordinary mass-ratio derivative on a cylinder. The radius
is constant on a whole clock neighborhood, so it contributes no derivative. -/
theorem hasDerivAt_mu_flux {e ui b s t τ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hτ : τ ∈ Ioo s t) :
    HasDerivAt (fun x => S.mu (γ.U x) (γ.V x))
      ((1 - S.mu (γ.U τ) (γ.V τ)) *
        (‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 -
          ‖S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2) / b) τ := by
  have hp := γ.mem τ (Ioo_subset_Icc_self hτ)
  have hr := γ.radius τ (Ioo_subset_Icc_self hτ)
  have hc := mass_clock_cancellation S (γ.U τ) (γ.V τ) (hr.trans_ne hb.ne')
    (hS.nu_neg _ hp).ne (hS.lam_pos _ hp).ne'
  have hd := ((hasDerivAt_mass hS γ hb hτ).const_mul 2).div_const b
  rw [hc] at hd
  have hd' : HasDerivAt (fun x => 2 * S.m (γ.U x) (γ.V x) / b)
      ((1 - S.mu (γ.U τ) (γ.V τ)) *
        (‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 -
          ‖S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2) / b) τ := by
    convert hd using 1
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hτ.1 hτ.2] with x hx
  simp only [Fields.mu, γ.radius x hx]

/-- [internal] Both normalized scalar traces and the mass ratio are continuous
on the closed cylinder. No a.e. representative is evaluated pointwise here. -/
theorem continuousOn_normalized_traces {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    {b s t : ℝ} (hS : IsSolution e S D) (γ : ClockCylinder S D b s t) :
    ContinuousOn (fun x => S.theta (γ.U x) (γ.V x) /
      (S.lam (γ.U x) (γ.V x) : ℂ)) (Icc s t) ∧
    ContinuousOn (fun x => S.xi (γ.U x) (γ.V x) /
      (S.nu (γ.U x) (γ.V x) : ℂ)) (Icc s t) ∧
    ContinuousOn (fun x => S.mu (γ.U x) (γ.V x)) (Icc s t) := by
  refine ⟨(γ.continuousOn_trace hS.cont_theta).div
    (Complex.continuous_ofReal.comp_continuousOn (γ.continuousOn_trace hS.cont_lam))
      (fun x hx => Complex.ofReal_ne_zero.mpr (hS.lam_pos _ (γ.mem x hx)).ne'),
    (γ.continuousOn_trace hS.cont_xi).div
      (Complex.continuous_ofReal.comp_continuousOn (γ.continuousOn_trace hS.cont_nu))
      (fun x hx => Complex.ofReal_ne_zero.mpr (hS.nu_neg _ (γ.mem x hx)).ne), ?_⟩
  have hc : ContinuousOn (fun x => 2 * S.m (γ.U x) (γ.V x) / b) (Icc s t) :=
    (continuousOn_const.mul (γ.continuousOn_trace hS.cont_m)).div_const b
  exact hc.congr (fun x hx => by simp only [Fields.mu, γ.radius x hx])

/-- [internal] A continuous curve with its continuous interior derivative is
AC up to both endpoints. Only compact interval FTC is used. -/
theorem ac_of_continuous_density {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E} {s t : ℝ}
    (hst : s ≤ t) (hf : ContinuousOn f (Icc s t)) (hg : ContinuousOn g (Icc s t))
    (hd : ∀ x ∈ Ioo s t, HasDerivAt f (g x) x) :
    AbsolutelyContinuousOnInterval f s t := by
  apply absolutelyContinuousOnInterval_of_integralForm_on (g := g) hst
  intro x hx
  have hsub : Icc s x ⊆ Icc s t := Icc_subset_Icc le_rfl hx.2
  refine ⟨(hg.mono hsub).intervalIntegrable_of_Icc hx.1, ?_⟩
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 (hf.mono hsub)
    (fun y hy => hd y ⟨hy.1, hy.2.trans_le hx.2⟩)
    ((hg.mono hsub).intervalIntegrable_of_Icc hx.1)).symm

/-- [internal] The scalar and mass ratio are AC on the closed cylinder. Their
continuous interior derivative densities suffice even at physical coordinate
boundaries; no off-domain extension is used. -/
theorem ac_scalar_mu {e ui b s t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) (hst : s ≤ t) :
    AbsolutelyContinuousOnInterval (fun x => S.phi (γ.U x) (γ.V x)) s t ∧
      AbsolutelyContinuousOnInterval (fun x => S.mu (γ.U x) (γ.V x)) s t := by
  obtain ⟨cy, cz, cm⟩ := continuousOn_normalized_traces hS γ
  have cp := γ.continuousOn_trace hS.cont_phi
  have ca := γ.continuousOn_trace hS.cont_A
  have cn := γ.continuousOn_trace hS.cont_nu
  have ci := cn.neg.inv₀ (fun x hx => neg_ne_zero.mpr (hS.nu_neg _ (γ.mem x hx)).ne)
  have cf : ContinuousOn (fun x =>
      (S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ) -
          S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)) / (b : ℂ) -
        I * e * S.A (γ.U x) (γ.V x) *
          ((-S.nu (γ.U x) (γ.V x))⁻¹ : ℝ) * S.phi (γ.U x) (γ.V x)) (Icc s t) :=
    ((cy.sub cz).div_const (b : ℂ)).sub
      (((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ca)).mul
        (Complex.continuous_ofReal.comp_continuousOn ci)).mul cp)
  have cg : ContinuousOn (fun x => (1 - S.mu (γ.U x) (γ.V x)) *
      (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 -
        ‖S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2) / b) (Icc s t) :=
    ((continuousOn_const.sub cm).mul ((cy.norm.pow 2).sub (cz.norm.pow 2))).div_const b
  exact ⟨ac_of_continuous_density hst cp cf (fun x hx => hasDerivAt_scalar_flux hS γ hb hx),
    ac_of_continuous_density hst cm cg (fun x hx => hasDerivAt_mu_flux hS γ hb hx)⟩

end Cylinder

/-- [node eq:co-cylinder-flux]
The two exact flux identities hold a.e. in the actual cylinder clock
(`charged_SF_new_version.tex:L1869`), with the pulled-back connection displayed in the
scalar derivative. Constants: none; arbitrary coupling and data size. -/
theorem co_cylinder_flux {e ui b s t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (γ : ClockCylinder S (origDomain ui) b s t)
    (hb : 0 < b) :
    ∀ᵐ τ ∂volume.restrict (Icc s t),
      (b : ℂ) * (deriv (fun x => S.phi (γ.U x) (γ.V x)) τ +
        I * e * S.A (γ.U τ) (γ.V τ) * deriv γ.U τ * S.phi (γ.U τ) (γ.V τ)) =
          S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ) -
            S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ) ∧
      b * deriv (fun x => S.mu (γ.U x) (γ.V x)) τ =
        (1 - S.mu (γ.U τ) (γ.V τ)) *
          (‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 -
            ‖S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2) := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
  constructor
  · rw [(Cylinder.hasDerivAt_scalar_flux hS γ hb hτ).deriv, (γ.hasDerivAt_U hτ).deriv]
    simp only [sub_add_cancel]
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hb.ne')
  · rw [(Cylinder.hasDerivAt_mu_flux hS γ hb hτ).deriv]
    exact mul_div_cancel₀ _ hb.ne'

end EmcsfAcExtension.Global
