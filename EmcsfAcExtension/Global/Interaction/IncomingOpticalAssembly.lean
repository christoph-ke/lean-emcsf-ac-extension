module

public import EmcsfAcExtension.Global.Interaction.IncomingOpticalCost
public import EmcsfAcExtension.Global.Interaction.BoundaryOpticalSum
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Api.Mono
import Mathlib.Tactic

/-! # Uniform incoming optical estimate

The radial mass is separated into its actual boundary, derivative-source,
and electric parts. The two-label finite endpoint is integrated before
its labels. Source: charged_SF_new_version.tex:L3747–L3777; internal project record.
-/

public section
open Set MeasureTheory
open scoped ENNReal
namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The actual radial mass is bounded by its explicit boundary upper mass,
the actual derivative-source square, and the electric cubic upper mass.
All coefficients are displayed; they depend only on the fixed scalar
amplitude, uniformly in fields, charge profile, radii and labels. -/
theorem radial_mass_split_upper {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b F A : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hF : 0 ≤ F) (hp : 1 / 2 < 1 - F ^ 2) (hA : 0 ≤ A)
    (hmu : ∀ v ∈ Icc a b, 0 ≤ S.mu u v)
    (hy : ∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F)
    (hQ : ∀ v ∈ Icc a b, |S.Q u v| ≤ A * S.r u v ^ 2) :
    S.m u b ≤ S.r u a * (S.m u a / S.r u a +
      ‖S.theta u a / S.lam u a‖ ^ 2 / (2 * (1 - F ^ 2) - 1)) +
        (∫ v in a..b, S.lam u v * ‖radialYSource S u a v‖ ^ 2) +
        A ^ 2 / 6 * S.r u b ^ 3 := by
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have cy := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne')
  have cB := continuousOn_radialYBoundary_end hS hua hab hs
  have cJ := continuousOn_radialYSource_end hS hua hab hs
  have iy := (cl.mul (cy.norm.pow 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have iB := (cl.mul (cB.norm.pow 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have iJ := (cl.mul (cJ.norm.pow 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have hsq (v : ℝ) (hv : v ∈ Icc a b) :
      (1 / 2 : ℝ) * (S.lam u v * ‖S.theta u v / S.lam u v‖ ^ 2) ≤
        S.lam u v * ‖radialYBoundary S u a v‖ ^ 2 + S.lam u v * ‖radialYSource S u a v‖ ^ 2 := by
    have heq := ct_y_split_identity hS hua hv.1
      (fun q hq => hs ⟨hq.1, hq.2.1, hq.2.2.trans hv.2⟩)
    have hn : ‖S.theta u v / S.lam u v‖ ≤ ‖radialYBoundary S u a v‖ + ‖radialYSource S u a v‖ := by
      rw [heq]
      exact norm_add_le _ _
    have hh := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
    have he : ‖S.theta u v / S.lam u v‖ ^ 2 / 2 ≤
        ‖radialYBoundary S u a v‖ ^ 2 + ‖radialYSource S u a v‖ ^ 2 := by
      nlinarith only [hh, sq_nonneg (‖radialYBoundary S u a v‖ - ‖radialYSource S u a v‖)]
    have hl := (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le
    nlinarith only [mul_le_mul_of_nonneg_left he hl]
  have hi := intervalIntegral.integral_mono_on hab (iy.const_mul (1 / 2)) (iB.add iJ) hsq
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add iB iJ] at hi
  change (1 / 2 : ℝ) * (∫ v in a..b, S.lam u v * ‖S.theta u v / S.lam u v‖ ^ 2) ≤
    (∫ v in a..b, S.lam u v * ‖radialYBoundary S u a v‖ ^ 2) +
    (∫ v in a..b, S.lam u v * ‖radialYSource S u a v‖ ^ 2) at hi
  have hmass := radial_mass_reconstruction_of_charge_profile hS hua hab hs hmu hA hQ
  have hbound := boundary_scalar_mass_le hS hua hab hs hF hp hy
  have hra := hS.r_pos (u, a) (hs ⟨rfl, le_rfl, hab⟩) hua
  have heq : S.r u a * (S.m u a / S.r u a +
      ‖S.theta u a / S.lam u a‖ ^ 2 / (2 * (1 - F ^ 2) - 1)) =
      S.m u a + S.r u a * ‖S.theta u a / S.lam u a‖ ^ 2 / (2 * (1 - F ^ 2) - 1) := by
    field_simp [hra.ne']
  rw [heq]
  linarith only [hmass, hi, hbound]

/-- [internal]
The incoming positive optical exponent is uniformly bounded by
`C sum E_n + C J² + C ζ²` on every actual exterior label history.
The positive constant depends only on fixed `δ,c,Λ,F,ε,ρ,Cq`, chosen
before coupling, scalar background, radius scale, boundary, envelope,
stage number, and every duration. The source mass retains its finite
endpoint through incoming substitution; electric cost uses the radius
moment and boundary cost uses the actual full-stage budgets.
Source: charged_SF_new_version.tex:L3610–L3614, L3747–L3777; internal project record. -/
theorem ct_optical_in (δ c Λ F ε ρ Cq : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e ui M R₀ u₀ u₁ v₀ : ℝ) (S : Fields)
      (vb g : ℝ → ℝ) (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
      IsSolution e S (origDomain ui) → BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
      0 ≤ M → 0 ≤ R₀ → (∀ u ∈ Icc u₀ u₁, S.r u 0 ≤ R₀) →
      (∀ p ∈ exteriorDomain ui u₀ u₁ vb, |S.Q p.1 p.2| / S.r p.1 p.2 ^ 2 ≤ Cq * |e| * M * F) →
      IntervalIntegrable g volume v₀ 0 →
      (∀ᵐ s ∂volume.restrict (Icc v₀ 0), 0 ≤ g s) →
      (∀ u ∈ Icc u₀ u₁, ∀ᵐ v ∂volume.restrict (Icc (vb u) 0), ‖weightedJ S u v‖ ≤ g v) →
      ∀ v ∈ Icc v₀ 0,
      (∫⁻ u in {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ v}, ENNReal.ofReal
        ((-S.nu u v) * S.mu u v / ((1 - S.mu u v) * S.r u v))) ≤
        ENNReal.ofReal (C * (∑ n, E n) + C * (∫ s in v₀..0, g s) ^ 2 +
          C * Local.sigma e M (2 * R₀)) := by
  rcases hbox with ⟨hδ, _, hc, hcΛ, hF, hF1, _, hp, hρ, _⟩
  have hΛ := hc.trans_le hcΛ
  have hp' : 1 / 2 < 1 - F ^ 2 := (le_max_right ε (1 / 2)).trans_lt hp
  have hq : 0 < 2 * (1 - F ^ 2) - 1 := by linarith only [hp']
  obtain ⟨Cj, hCj, hj⟩ := source_mass_finite_endpoint c Λ F hc hΛ hF hF1.le
  obtain ⟨Ce, hCe, he⟩ := electromagnetic_incoming_optical_cost δ Cq hδ
  let Cb := 2 * (1 + (2 * (1 - F ^ 2) - 1)⁻¹) / (δ * ρ)
  let β := 2 * Cj / δ
  let Cs := β * c⁻¹
  let C := Cb + Cs + Ce
  have hCb : 0 < Cb := by dsimp [Cb]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have hCs : 0 < Cs := mul_pos hβ (inv_pos.mpr hc)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro e ui M R₀ u₀ u₁ v₀ S vb g N B E hS hE hstop hM hR hupper hQ hg hg0 hmajor v hv
  let D := exteriorDomain ui u₀ u₁ vb
  let I := Icc u₀ u₁
  let U := {u | u ∈ I ∧ vb u ≤ v}
  let w := I.indicator vb
  let A := Cq * |e| * M * F
  have hSE : IsSolution e S D := Local.isSolution_mono hS inter_subset_left
  obtain ⟨z, hz, hzv, hist, hin⟩ := label_history_interval B hv
  have hUeq : U = Icc u₀ z := hist
  have hU : MeasurableSet U := hUeq ▸ measurableSet_Icc
  have hsub : U ⊆ Icc u₀ z := by rw [hUeq]
  have hui (u : ℝ) (hu : u ∈ U) : u ∈ Icc u₀ u₁ := hu.1
  have hrow (u : ℝ) (hu : u ∈ U) : outSeg u (vb u) v ⊆ D :=
    fun p hp => finite_boundary_row B u hu.1 ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩
  have hmem (u : ℝ) (hu : u ∈ U) : (u, v) ∈ D := hrow u hu ⟨rfl, hu.2, le_rfl⟩
  have hr (u : ℝ) (hu : u ∈ U) : 0 < S.r u v := hSE.r_pos (u, v) (hmem u hu)
    ((B.off_axis u hu.1).trans_le hu.2)
  have hn (u : ℝ) (hu : u ∈ U) : 0 < -S.nu u v := neg_pos.mpr (hSE.nu_neg (u, v) (hmem u hu))
  have hgap (u : ℝ) (hu : u ∈ U) : 0 < 1 - S.mu u v := hδ.trans_le (hstop (u, v) (hmem u hu)).2.1
  have hv0 : v₀ ≤ 0 := hv.1.trans hv.2
  obtain ⟨G, hG, hGeq, hmassG⟩ := exists_measurable_envelope hv0 g hg hg0
  have hJ0 := intervalIntegral.integral_nonneg_of_ae_restrict hv0 hg0
  have hw (u : ℝ) (hu : u ∈ I) : w u = vb u := indicator_of_mem hu _
  have hwm : Measurable w := by
    convert B.cont.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
      measurableSet_Icc using 1
    ext u
    by_cases hu : u ∈ Icc u₀ u₁ <;> simp [w, I, Set.piecewise, hu]
  let K := fun u => D.indicator (fun p => ENNReal.ofReal ((-S.nu p.1 p.2) / S.r p.1 p.2 ^ 2)) (u, v)
  have hrad (p : ℝ × ℝ) (hp : p ∈ D) : 0 < S.r p.1 p.2 :=
    hSE.r_pos p hp ((B.off_axis p.1 ⟨hp.2.1, hp.2.2.1⟩).trans_le hp.2.2.2)
  have hKm : Measurable K := (measurable_exterior_indicator B _
    (ENNReal.continuous_ofReal.comp_continuousOn (hSE.cont_nu.neg.div (hSE.cont_r.pow 2)
      (fun p hp => pow_ne_zero _ (hrad p hp).ne')))).comp (measurable_id.prodMk measurable_const)
  have hKeq (u : ℝ) (hu : u ∈ U) : K u = ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 2) :=
    indicator_of_mem (hmem u hu) _
  let Q := fun (s t : ℝ) => ENNReal.ofReal (v - max s t) * G s * G t
  let Jm := fun u => ∫⁻ s in Icc (w u) v, ∫⁻ t in Icc (w u) v, Q s t
  have hQm : Measurable (Function.uncurry (fun (_u : ℝ) (st : ℝ × ℝ) => Q st.1 st.2)) :=
    ((ENNReal.continuous_ofReal.measurable.comp (measurable_const.sub
      (measurable_snd.fst.max measurable_snd.snd))).mul (hG.comp measurable_snd.fst)).mul
        (hG.comp measurable_snd.snd)
  have hJm : Measurable Jm := measurable_history_square hwm v _ hQm
  let fJ := fun u => ENNReal.ofReal β * (K u * Jm u)
  let fB := fun u => ENNReal.ofReal (2 * (-S.nu u v) * S.r u (vb u) *
    (S.m u (vb u) / S.r u (vb u) + ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 / (2 * (1 - F ^ 2) -
      1)) /
      ((1 - S.mu u v) * S.r u v ^ 2))
  let fE := fun u => ENNReal.ofReal (2 * (-S.nu u v) * (A ^ 2 / 6 * S.r u v ^ 3) /
    ((1 - S.mu u v) * S.r u v ^ 2))
  have hfJ : Measurable fJ := measurable_const.mul (hKm.mul hJm)
  have cRv := (Calculus.continuousOn_in_section hSE.cont_r hin).mono hsub
  have cNv := (Calculus.continuousOn_in_section hSE.cont_nu hin).neg.mono hsub
  have cMv := (Calculus.continuousOn_in_section hSE.cont_m hin).mono hsub
  have cμv : ContinuousOn (fun u => S.mu u v) U :=
    (continuousOn_const.mul cMv).div cRv (fun u hu => (hr u hu).ne')
  have cDen : ContinuousOn (fun u => (1 - S.mu u v) * S.r u v ^ 2) U :=
    (continuousOn_const.sub cμv).mul (cRv.pow 2)
  have hpB := continuousOn_id.prodMk B.cont
  have cRb := (hS.cont_r.comp hpB B.mem).mono (fun u hu => hui u hu)
  have cMb := (hS.cont_m.comp hpB B.mem).mono (fun u hu => hui u hu)
  obtain ⟨cy, _, _, _⟩ := continuousOn_boundary_traces hS B
  have cYb := cy.mono (fun u hu => hui u hu)
  have hfB : AEMeasurable fB (volume.restrict U) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      ((((cNv.const_mul 2).mul cRb).mul ((cMb.div cRb (fun u hu =>
        (hS.r_pos (u, vb u) (B.mem u hu.1) (B.off_axis u hu.1)).ne')).add
          ((cYb.pow 2).div_const _))).div cDen (fun u hu =>
            mul_ne_zero (hgap u hu).ne' (pow_ne_zero _ (hr u hu).ne')))).aemeasurable hU
  have hpoint (u : ℝ) (hu : u ∈ U) : ENNReal.ofReal
      ((-S.nu u v) * S.mu u v / ((1 - S.mu u v) * S.r u v)) ≤ fB u + (fJ u + fE u) := by
    have hs := hrow u hu
    have hua := B.off_axis u hu.1
    have hrb := hS.r_pos (u, vb u) (B.mem u hu.1) hua
    have hr' := hr u hu
    have hn' := hn u hu
    have hg' := hgap u hu
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hsplit := radial_mass_split_upper hSE hua hu.2 hs hF hp' hA
      (fun x hx => (hstop (u, x) (hs ⟨rfl, hx⟩)).1)
      (fun x hx => (hstop (u, x) (hs ⟨rfl, hx⟩)).2.2.2.2.1)
      (fun x hx => (div_le_iff₀ (sq_pos_of_pos (hSE.r_pos (u, x) (hs ⟨rfl, hx⟩)
        (hua.trans_le hx.1)))).mp (hQ (u, x) (hs ⟨rfl, hx⟩)))
    let Ms := ∫ x in (vb u)..v, S.lam u x * ‖radialYSource S u (vb u) x‖ ^ 2
    let Mb := S.r u (vb u) * (S.m u (vb u) / S.r u (vb u) +
      ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 / (2 * (1 - F ^ 2) - 1))
    let Me := A ^ 2 / 6 * S.r u v ^ 3
    let H := 2 * (-S.nu u v) / ((1 - S.mu u v) * S.r u v ^ 2)
    have hH : 0 ≤ H := by dsimp [H]; positivity
    have hmr : 0 ≤ S.m u (vb u) / S.r u (vb u) := by
      have heq : S.m u (vb u) / S.r u (vb u) = S.mu u (vb u) / 2 := by dsimp [Fields.mu]; ring
      rw [heq]
      exact div_nonneg (hstop (u, vb u) (hs ⟨rfl, le_rfl, hu.2⟩)).1 (by norm_num)
    have hMb : 0 ≤ Mb := by dsimp [Mb]; positivity
    have hMe : 0 ≤ Me := by dsimp [Me]; positivity
    have cJ := continuousOn_radialYSource_end hSE hua hu.2 hs
    have cl := Calculus.continuousOn_out_section hSE.cont_lam hs
    have iJ := (cl.mul (cJ.norm.pow 2)).intervalIntegrable_of_Icc (μ := volume) hu.2
    have hMs : 0 ≤ Ms := intervalIntegral.integral_nonneg hu.2 (fun x hx =>
      mul_nonneg (hSE.lam_pos (u, x) (hs ⟨rfl, hx⟩)).le (sq_nonneg _))
    have hMsEq : ENNReal.ofReal Ms = ∫⁻ x in Icc (vb u) v,
        ENNReal.ofReal (S.lam u x * ‖radialYSource S u (vb u) x‖ ^ 2) := by
      dsimp only [Ms]
      rw [intervalIntegral.integral_of_le hu.2, ← integral_Icc_eq_integral_Ioc]
      exact ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hu.2).mp iJ)
        (ae_restrict_of_forall_mem measurableSet_Icc (fun x hx =>
          mul_nonneg (hSE.lam_pos (u, x) (hs ⟨rfl, hx⟩)).le (sq_nonneg _)))
    have hsubg : Icc (vb u) v ⊆ Icc v₀ 0 := Icc_subset_Icc (finite_boundary_label_bounds B u
      hu.1).1 hv.2
    have hsubg' : uIcc (vb u) v ⊆ uIcc v₀ 0 := by simpa only [uIcc_of_le hu.2, uIcc_of_le hv0]
      using hsubg
    have hsrc := hj e S D u (vb u) v g hSE hua hu.2 hs
      (fun x hx => ⟨(hstop (u, x) (hs ⟨rfl, hx⟩)).2.2.1, (hstop (u, x) (hs ⟨rfl, hx⟩)).2.2.2.1⟩)
      (fun x hx => (hstop (u, x) (hs ⟨rfl, hx⟩)).2.2.2.2.1) (hg.mono_set hsubg')
      ((hmajor u hu.1).filter_mono (ae_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl hv.2)
        le_rfl)))
    have hdouble : (∫⁻ s in Icc (vb u) v, ∫⁻ t in Icc (vb u) v,
        ENNReal.ofReal (v - max s t) * ENNReal.ofReal (g s) * ENNReal.ofReal (g t)) = Jm u := by
      dsimp only [Jm]
      rw [hw u hu.1]
      apply lintegral_congr_ae
      filter_upwards [hGeq.filter_mono (ae_mono (Measure.restrict_mono hsubg le_rfl))] with s hgs
      apply lintegral_congr_ae
      filter_upwards [hGeq.filter_mono (ae_mono (Measure.restrict_mono hsubg le_rfl))] with t hgt
      dsimp only [Q]
      rw [hgs, hgt]
    rw [← hMsEq, hdouble] at hsrc
    have hcoeff : H * Cj ≤ β * ((-S.nu u v) / S.r u v ^ 2) := by
      have hh : H ≤ (2 / δ) * ((-S.nu u v) / S.r u v ^ 2) := by
        calc
          _ = (2 * ((-S.nu u v) / S.r u v ^ 2)) / (1 - S.mu u v) := by
            dsimp only [H]
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
          _ ≤ (2 * ((-S.nu u v) / S.r u v ^ 2)) / δ :=
            div_le_div_of_nonneg_left (by positivity) hδ (hstop (u, v) (hmem u hu)).2.1
          _ = _ := by ring
      exact (mul_le_mul_of_nonneg_right hh hCj.le).trans_eq (by dsimp [β]; ring)
    have hscalar : ENNReal.ofReal H * ENNReal.ofReal Ms ≤ fJ u := by
      apply (mul_le_mul le_rfl hsrc bot_le bot_le).trans
      dsimp only [fJ]
      rw [hKeq u hu, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hH,
        ← ENNReal.ofReal_mul hβ.le]
      exact mul_le_mul (ENNReal.ofReal_le_ofReal hcoeff) le_rfl bot_le bot_le
    calc
      _ = ENNReal.ofReal H * ENNReal.ofReal (S.m u v) := by
        rw [← ENNReal.ofReal_mul hH]
        congr 1
        dsimp only [H, Fields.mu]
        field_simp [hr'.ne', hg'.ne']
      _ ≤ ENNReal.ofReal H * ENNReal.ofReal (Mb + Ms + Me) :=
        mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal hsplit) bot_le bot_le
      _ = ENNReal.ofReal H * ENNReal.ofReal Mb +
          (ENNReal.ofReal H * ENNReal.ofReal Ms + ENNReal.ofReal H * ENNReal.ofReal Me) := by
        rw [ENNReal.ofReal_add (add_nonneg hMb hMs) hMe, ENNReal.ofReal_add hMb hMs]
        ring
      _ ≤ fB u + (fJ u + fE u) := by
        have hb : ENNReal.ofReal H * ENNReal.ofReal Mb = fB u := by
          rw [← ENNReal.ofReal_mul hH]
          congr 1
          dsimp only [H, Mb, fB]
          ring
        have he' : ENNReal.ofReal H * ENNReal.ofReal Me = fE u := by
          rw [← ENNReal.ofReal_mul hH]
          congr 1
          dsimp only [H, Me, fE]
          ring
        rw [hb, he']
        exact add_le_add le_rfl (add_le_add hscalar le_rfl)
  have hJcost : (∫⁻ u in U, fJ u) ≤ ENNReal.ofReal (Cs * (∫ s in v₀..0, g s) ^ 2) := by
    calc
      _ = ENNReal.ofReal β * (∫⁻ u in U, ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 2) *
          (∫⁻ s in Icc (vb u) v, ∫⁻ t in Icc (vb u) v, Q s t)) := by
        dsimp only [fJ]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        apply setLIntegral_congr_fun hU
        intro u hu
        change K u * Jm u = _
        rw [hKeq u hu]
        dsimp only [Jm]
        rw [hw u hu.1]
      _ ≤ ENNReal.ofReal β * (ENNReal.ofReal c⁻¹ * (∫⁻ s in Icc v₀ 0, G s) ^ 2) := by
        gcongr
        exact incoming_source_optical_kernel hS B hstop hc v hv G hG
      _ = _ := by
        rw [hmassG, ← ENNReal.ofReal_pow hJ0 2,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ← ENNReal.ofReal_mul hβ.le]
        congr 1
        dsimp only [Cs]
        ring
  have hBcost : (∫⁻ u in U, fB u) ≤ ENNReal.ofReal (Cb * ∑ n, E n) :=
    boundary_upper_optical_cost hS B hE hstop hδ hρ hp' v hv
  have hEcost : (∫⁻ u in U, fE u) ≤ ENNReal.ofReal (Ce * Local.sigma e M (2 * R₀)) := by
    apply (he e M F R₀ u₀ z v S D U hSE hz.1 hzv.le hin hU hsub hR
      (fun u hu => ⟨hr u hu, ((outgoing_radius_calculus hSE
        ((B.off_axis u hu.1).trans_le hu.2).le hv.2
        (fun p hp => finite_boundary_row B u hu.1 ⟨hp.1, hu.2.trans hp.2.1, hp.2.2⟩)).2.monotoneOn
          ⟨le_rfl, hv.2⟩ ⟨hv.2, le_rfl⟩ hv.2).trans (hupper u hu.1)⟩)
      (fun u hu => (hstop (u, v) (hmem u hu)).2.1)).trans
    apply ENNReal.ofReal_le_ofReal
    have hsigma : 0 ≤ Local.sigma e M (2 * R₀) := by rw [ct_zeta]; positivity
    have hF2 : F ^ 2 ≤ 1 := by nlinarith only [hF, hF1, sq_nonneg (F - 1)]
    exact mul_le_of_le_one_right (mul_nonneg hCe.le hsigma) hF2
  calc
    _ ≤ ∫⁻ u in U, fB u + (fJ u + fE u) := setLIntegral_mono' hU hpoint
    _ = (∫⁻ u in U, fB u) + ((∫⁻ u in U, fJ u) + ∫⁻ u in U, fE u) := by
      rw [lintegral_add_left' hfB, lintegral_add_left' hfJ.aemeasurable]
    _ ≤ ENNReal.ofReal (Cb * ∑ n, E n) +
        (ENNReal.ofReal (Cs * (∫ s in v₀..0, g s) ^ 2) + ENNReal.ofReal (Ce * Local.sigma e M (2
          * R₀))) :=
      add_le_add hBcost (add_le_add hJcost hEcost)
    _ ≤ _ := by
      have hEs : 0 ≤ ∑ n, E n := Finset.sum_nonneg (fun n _ => (hE n).1)
      have hsigma : 0 ≤ Local.sigma e M (2 * R₀) := by rw [ct_zeta]; positivity
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hb : Cb ≤ C := by dsimp [C]; linarith only [hCs, hCe]
      have hs : Cs ≤ C := by dsimp [C]; linarith only [hCb, hCe]
      have he' : Ce ≤ C := by dsimp [C]; linarith only [hCb, hCs]
      exact add_le_add (mul_le_mul_of_nonneg_right hb hEs)
        (add_le_add (mul_le_mul_of_nonneg_right hs (sq_nonneg _)) (mul_le_mul_of_nonneg_right
          he' hsigma)) |>.trans_eq (by ring)

end EmcsfAcExtension.Global.InteractionEstimate
