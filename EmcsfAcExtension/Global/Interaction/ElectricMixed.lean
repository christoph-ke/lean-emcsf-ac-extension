module

public import EmcsfAcExtension.Global.Interaction.PairSource
public import EmcsfAcExtension.Global.Interaction.PairKernel
public import EmcsfAcExtension.Global.Defs.Stages
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Global.Interaction.PairTonelli
import EmcsfAcExtension.Local.Api.Mono
import Mathlib.Tactic

/-! # The mixed electromagnetic curvature source

The electric incoming summand is selected inside the actual curvature
primitive. Its radial cubic moment is retained before incoming integration.
Source: `charged_SF_new_version.tex:L3730–L3742`; internal project record `(mixed)`.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The incoming electric primitive is continuous in its outgoing endpoint.
Only the frozen continuous wave source is integrated. -/
theorem continuousOn_radialZEM_end {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) : ContinuousOn (radialZEM e S u a) (Icc a b) := by
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cq := Calculus.continuousOn_out_section hS.cont_Q hs
  have cp := Calculus.continuousOn_out_section hS.cont_phi hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : S.r u v ≠ 0 :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have cm : ContinuousOn (S.mu u) (Icc a b) := by
    simpa only [Fields.mu, Pi.mul_apply, Pi.div_apply] using!
      ((Calculus.continuousOn_out_section hS.cont_m hs).const_mul 2).div cr hr
  have hn (v : ℝ) (hv : v ∈ Icc a b) : (S.nu u v : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (hS.nu_neg (u, v) (hs ⟨rfl, hv⟩)).ne
  have hg (v : ℝ) (hv : v ∈ Icc a b) : 1 - S.mu u v ≠ 0 :=
    (hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩)).ne'
  have cw : ContinuousOn (S.waveSource e u) (Icc a b) := by
    unfold Fields.waveSource
    exact (((((continuousOn_const.mul continuousOn_const).mul
      (continuous_ofReal.comp_continuousOn cq)).mul cp).mul
      (continuous_ofReal.comp_continuousOn cn)).mul
      (continuous_ofReal.comp_continuousOn cl)).div
      ((continuousOn_const.sub (continuous_ofReal.comp_continuousOn cm)).mul
        (continuous_ofReal.comp_continuousOn cr))
      (fun v hv => mul_ne_zero (by exact_mod_cast hg v hv) (ofReal_ne_zero.mpr (hr v hv)))
  have ci := intervalIntegral.continuousOn_primitive_interval'
    (cw.intervalIntegrable_of_Icc hab (μ := volume)) left_mem_uIcc
  have ci' : ContinuousOn (fun v => ∫ t in a..v, S.waveSource e u t) (Icc a b) := by
    simpa only [uIcc_of_le hab] using! ci
  exact ((continuous_ofReal.comp_continuousOn cn).inv₀ hn).mul ci'

/-- [internal]
The actual electric incoming summand selected in the curvature primitive.
Its positive coefficient depends only on `δ,c,Λ,Cq`, chosen before coupling,
scalar background, stopping amplitude, solution, row, and physical scales.
The cubic radial moment is retained. The scalar and charge profiles are the
explicit inputs authorized by the interaction architecture.
Source: charged_SF_new_version.tex:L3730–L3736; internal project record `(mixed)`. -/
theorem electromagnetic_mixed_source (δ c Λ Cq : ℝ)
    (hδ : 0 < δ) (hc : 0 < c) (hΛ : 0 < Λ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M F ε : ℝ) (S : Fields) (D : Set (ℝ × ℝ))
      (u a b : ℝ) (g : ℝ → ℝ), IsSolution e S D → ExteriorStops S D δ c Λ F ε →
      u < a → a ≤ b → outSeg u a b ⊆ D → 0 ≤ M → 0 ≤ F →
      (∀ v ∈ Icc a b, ‖S.phi u v‖ ≤ M) →
      (∀ v ∈ Icc a b, |S.Q u v| / S.r u v ^ 2 ≤ Cq * |e| * M * F) →
      IntervalIntegrable g volume a b →
      (∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) →
      ‖curvatureScalarSource S u b (S.theta u b / S.lam u b)
        (radialCurvatureWith S u a b (radialZEM e S u a))‖ ≤
        C * e ^ 2 * M ^ 2 * F ^ 2 * ((-S.nu u b) / S.r u b ^ 3) *
          (∫ s in a..b, S.r u s ^ 3 * g s) := by
  obtain ⟨A, hA, hZ⟩ := ct_z_charge_of_profiles δ Cq hδ hCq
  refine ⟨3 * Λ ^ 2 * A / (δ * c), by positivity, ?_⟩
  intro e M F ε S D u a b g hS hstop hua hab hs hM hF hphi hQ hg hmajor
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cZ := continuousOn_radialZEM_end hS hua hab hs
  have iz := hg.continuousOn_mul (by simpa only [uIcc_of_le hab] using cr.mul cZ.norm)
  have ir := hg.continuousOn_mul (by simpa only [uIcc_of_le hab] using cr.pow 3)
  have hi : (∫ s in a..b, S.r u s * ‖radialZEM e S u a s‖ * g s) ≤
      (A * e ^ 2 * M ^ 2 * F) * (∫ s in a..b, S.r u s ^ 3 * g s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_ae_restrict hab iz
      (ir.const_mul (A * e ^ 2 * M ^ 2 * F))
    filter_upwards [hmajor, ae_restrict_mem measurableSet_Icc] with s hgs hsmem
    have hrs := hS.r_pos (u, s) (hs ⟨rfl, hsmem⟩) (hua.trans_le hsmem.1)
    have hz := hZ e M F c Λ ε S D u a s hS hstop hua hsmem.1
      (fun z hz => hs ⟨hz.1, hz.2.1, hz.2.2.trans hsmem.2⟩) hM hF
      (fun t ht => hphi t ⟨ht.1, ht.2.trans hsmem.2⟩)
      (fun t ht => hQ t ⟨ht.1, ht.2.trans hsmem.2⟩)
    change S.r u s * ‖radialZEM e S u a s‖ * g s ≤
      (A * e ^ 2 * M ^ 2 * F) * (S.r u s ^ 3 * g s)
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hz hrs.le) ((norm_nonneg _).trans hgs)
    convert hh using 1
    ring
  have hr := hS.r_pos (u, b) (hs ⟨rfl, hab, le_rfl⟩) (hua.trans_le hab)
  have hcurv := (radial_curvature_with_le hS hstop hua hab hs hc _ cZ g hg hmajor).trans
    (mul_le_mul_of_nonneg_left hi (by positivity))
  have hst := hstop (u, b) (hs ⟨rfl, hab, le_rfl⟩)
  have hn := (hS.nu_neg (u, b) (hs ⟨rfl, hab, le_rfl⟩)).le
  have hn0 := neg_nonneg.mpr hn
  have hl := (hS.lam_pos (u, b) (hs ⟨rfl, hab, le_rfl⟩)).le
  calc
    _ ≤ (3 * Λ ^ 2 * F / δ) * ((-S.nu u b) / S.r u b ^ 2) *
        ‖radialCurvatureWith S u a b (radialZEM e S u a)‖ :=
      curvature_scalar_source_le S u b δ Λ F _ _ hδ hr hn hl hst.2.2.2.1 hst.2.1
        hst.2.2.2.2.1
    _ ≤ (3 * Λ ^ 2 * F / δ) * ((-S.nu u b) / S.r u b ^ 2) *
        ((c * S.r u b)⁻¹ * ((A * e ^ 2 * M ^ 2 * F) *
          (∫ s in a..b, S.r u s ^ 3 * g s))) :=
      mul_le_mul_of_nonneg_left hcurv (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The actual cubic radius moment against the outer source kernel on a finite
stopped exterior. Its coefficient is `1/(2c(2-ε))`, depending only on fixed
`c,ε`, uniformly in the solution, label density, radius scale, stage count,
and durations. Outgoing integration precedes the incoming radius moment. -/
theorem electromagnetic_mixed_kernel {e ui u₀ u₁ v₀ ρ δ c Λ F ε R₀ : ℝ}
    {S : Fields} {vb : ℝ → ℝ} {N : ℕ}
    (hS : IsSolution e S (origDomain ui))
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    (hstop : ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε)
    (hc : 0 < c) (hε : ε < 2) (hR : 0 ≤ R₀)
    (hupper : ∀ u ∈ Icc u₀ u₁, S.r u 0 ≤ R₀)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
      ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
        (∫⁻ s in Icc (vb u) v, ENNReal.ofReal (S.r u s ^ 3) * G s)) ≤
      ENNReal.ofReal (R₀ ^ 2 / (2 * c * (2 - ε))) * (∫⁻ s in Icc v₀ 0, G s) := by
  classical
  let E := exteriorDomain ui u₀ u₁ vb
  let w := (Icc u₀ u₁).indicator vb
  let K := fun u v => E.indicator
    (fun p => ENNReal.ofReal ((-S.nu p.1 p.2) / S.r p.1 p.2 ^ 3)) (u, v)
  let A := fun u s => E.indicator (fun p => ENNReal.ofReal (S.r p.1 p.2 ^ 3)) (u, s)
  have h01 : u₀ ≤ u₁ := calc
    _ = B.cuts 0 := B.first.symm
    _ ≤ B.cuts (Fin.last N) := B.ordered (Fin.zero_le _)
    _ = _ := B.last
  have hw (u : ℝ) (hu : u ∈ Icc u₀ u₁) : w u = vb u := indicator_of_mem hu _
  have hwm : Measurable w := by
    convert B.cont.measurable_piecewise (g := fun _ => (0 : ℝ))
      continuousOn_const measurableSet_Icc using 1
    ext u
    by_cases hu : u ∈ Icc u₀ u₁ <;> simp [w, Set.piecewise, hu]
  have hbnd (u : ℝ) (hu : u ∈ Icc u₀ u₁) : v₀ ≤ w u ∧ w u ≤ 0 := by
    rw [hw u hu]
    refine ⟨?_, (B.mem u hu).2.2.2⟩
    rw [← B.entry_label]
    exact B.mono ⟨le_rfl, h01⟩ hu hu.1
  have hrow (u : ℝ) (hu : u ∈ Icc u₀ u₁) : outSeg u (vb u) 0 ⊆ E := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    dsimp only at hx
    subst x
    exact ⟨⟨(B.mem u hu).1, (B.mem u hu).2.1,
      (B.off_axis u hu).le.trans hv.1, hv.2⟩, hu.1, hu.2, hv.1⟩
  have hSE : IsSolution e S E := Local.isSolution_mono hS inter_subset_left
  have hr (p : ℝ × ℝ) (hp : p ∈ E) : 0 < S.r p.1 p.2 :=
    hSE.r_pos p hp ((B.off_axis p.1 ⟨hp.2.1, hp.2.2.1⟩).trans_le hp.2.2.2)
  have hKm : Measurable (Function.uncurry K) := by
    exact measurable_exterior_indicator B _
      (ENNReal.continuous_ofReal.comp_continuousOn
        (hSE.cont_nu.neg.div (hSE.cont_r.pow 3) (fun p hp => pow_ne_zero _ (hr p hp).ne')))
  have hAm : Measurable (Function.uncurry A) := by
    exact measurable_exterior_indicator B _
      (ENNReal.continuous_ofReal.comp_continuousOn (hSE.cont_r.pow 3))
  have hKeq (u : ℝ) (hu : u ∈ Icc u₀ u₁) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :
      K u v = ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) :=
    indicator_of_mem (show (u, v) ∈ E from hrow u hu ⟨rfl, hv.1, hv.2⟩) _
  have hAeq (u : ℝ) (hu : u ∈ Icc u₀ u₁) (s : ℝ) (hs : s ∈ Icc (vb u) 0) :
      A u s = ENNReal.ofReal (S.r u s ^ 3) := indicator_of_mem (show (u, s) ∈ E from hrow u hu
        ⟨rfl, hs.1, hs.2⟩) _
  have hmoment (s : ℝ) (hs : s ∈ Icc v₀ 0) :
      (∫⁻ u in Icc u₀ u₁ ∩ {u | w u ≤ s}, A u s * (∫⁻ v in Icc s 0, K u v)) ≤
        ENNReal.ofReal (R₀ ^ 2 / (2 * c * (2 - ε))) := by
    obtain ⟨t, ht, hts, hist, hin⟩ := label_history_interval B hs
    have hhist : Icc u₀ u₁ ∩ {u | w u ≤ s} = Icc u₀ t := by
      rw [← hist]
      ext u
      constructor
      · rintro ⟨hu, hwu⟩
        change w u ≤ s at hwu
        refine ⟨hu, ?_⟩
        rw [← hw u hu]
        exact hwu
      · rintro ⟨hu, hwu⟩
        refine ⟨hu, ?_⟩
        change w u ≤ s
        rw [hw u hu]
        exact hwu
    rw [hhist]
    have hsub : Icc u₀ t ⊆ Icc u₀ u₁ := Icc_subset_Icc le_rfl ht.2
    have hpoint (u : ℝ) (hu : u ∈ Icc u₀ t) :
        A u s * (∫⁻ v in Icc s 0, K u v) ≤
          ENNReal.ofReal ((c * (2 - ε))⁻¹) * ENNReal.ofReal ((-S.nu u s) * S.r u s) := by
      have huv : vb u ≤ s := (show u ∈ {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ s} from hist.symm ▸ hu).2
      have hseg : outSeg u s 0 ⊆ E :=
        fun p hp => hrow u (hsub hu) ⟨hp.1, huv.trans hp.2.1, hp.2.2⟩
      have hrus := hr (u, s) (hseg ⟨rfl, le_rfl, hs.2⟩)
      have hi := outgoing_inverse_cube_kernel hSE ((B.off_axis u (hsub hu)).trans_le huv)
        hs.2 hseg hc hε (fun v hv => (hstop (u, v) (hseg ⟨rfl, hv⟩)).2.2.1)
        (fun v hv => (hstop (u, v) (hseg ⟨rfl, hv⟩)).2.2.2.2.2.1)
      have heq : (∫⁻ v in Icc s 0, K u v) =
          ∫⁻ v in Icc s 0, ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro v hv
        exact hKeq u (hsub hu) v ⟨huv.trans hv.1, hv.2⟩
      rw [heq, hAeq u (hsub hu) s ⟨huv, hs.2⟩]
      apply (mul_le_mul le_rfl hi bot_le bot_le).trans_eq
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp [hrus.ne', hc.ne', (sub_pos.mpr hε).ne']
    calc
      _ ≤ ∫⁻ u in Icc u₀ t, ENNReal.ofReal ((c * (2 - ε))⁻¹) *
          ENNReal.ofReal ((-S.nu u s) * S.r u s) :=
        setLIntegral_mono' measurableSet_Icc hpoint
      _ = ENNReal.ofReal ((c * (2 - ε))⁻¹) *
          (∫⁻ u in Icc u₀ t, ENNReal.ofReal ((-S.nu u s) * S.r u s)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((c * (2 - ε))⁻¹) * ENNReal.ofReal (R₀ ^ 2 / 2) := by
        gcongr
        apply fixed_label_radius_moment hSE ht.1 hts.le hin measurableSet_Icc Subset.rfl hR
        intro u hu
        have humem := hsub hu
        have huv : vb u ≤ s := (show u ∈ {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ s} from hist.symm ▸ hu).2
        have hsrow : outSeg u s 0 ⊆ E :=
          fun p hp => hrow u humem ⟨hp.1, huv.trans hp.2.1, hp.2.2⟩
        exact ⟨(hr (u, s) (hsrow ⟨rfl, le_rfl, hs.2⟩)).le,
          ((outgoing_radius_calculus hSE ((B.off_axis u humem).trans_le huv).le hs.2
            hsrow).2.monotoneOn
            ⟨le_rfl, hs.2⟩ ⟨hs.2, le_rfl⟩ hs.2).trans (hupper u humem)⟩
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  calc
    _ = ∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (w u) 0,
        K u v * (∫⁻ s in Icc (w u) v, A u s * G s) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro u hu
      dsimp only
      rw [hw u hu]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [hKeq u hu v hv]
      congr 1
      apply setLIntegral_congr_fun measurableSet_Icc
      intro s hs
      change ENNReal.ofReal (S.r u s ^ 3) * G s = A u s * G s
      rw [hAeq u hu s ⟨hs.1, hs.2.trans hv.2⟩]
    _ = ∫⁻ s in Icc v₀ 0, G s *
        (∫⁻ u in Icc u₀ u₁ ∩ {u | w u ≤ s}, A u s * (∫⁻ v in Icc s 0, K u v)) :=
      lintegral_history_swap measurableSet_Icc hwm hbnd K A hKm hAm G hG
    _ ≤ ∫⁻ s in Icc v₀ 0, G s * ENNReal.ofReal (R₀ ^ 2 / (2 * c * (2 - ε))) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro s hs
      exact mul_le_mul le_rfl (hmoment s hs) bot_le bot_le
    _ = _ := by
      simp_rw [mul_comm (G _) (ENNReal.ofReal _)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- [internal]
The actual mixed electric curvature source has cost `C ζ² F² J`.
The positive coefficient depends only on `δ,c,Λ,ε,Cq`, before coupling,
scalar background, radius scale, envelope, amplitude, stage count, or
duration. Its row primitive is bounded first; the actual outer kernel and
incoming radius moment then discharge the spacetime estimate.
Source: charged_SF_new_version.tex:L3736–L3742. -/
theorem electromagnetic_mixed_cost (δ c Λ ε Cq : ℝ)
    (hδ : 0 < δ) (hc : 0 < c) (hΛ : 0 < Λ) (hε : ε < 2) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e ui M R₀ u₀ u₁ v₀ ρ F : ℝ) (S : Fields)
      (vb g : ℝ → ℝ) (N : ℕ) (_B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N),
      IsSolution e S (origDomain ui) →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
      0 ≤ M → 0 ≤ F → 0 ≤ R₀ → (∀ u ∈ Icc u₀ u₁, S.r u 0 ≤ R₀) →
      (∀ p ∈ exteriorDomain ui u₀ u₁ vb, ‖S.phi p.1 p.2‖ ≤ M ∧
        |S.Q p.1 p.2| / S.r p.1 p.2 ^ 2 ≤ Cq * |e| * M * F) →
      IntervalIntegrable g volume v₀ 0 →
      (∀ᵐ s ∂volume.restrict (Icc v₀ 0), 0 ≤ g s) →
      (∀ u ∈ Icc u₀ u₁, ∀ᵐ v ∂volume.restrict (Icc (vb u) 0), ‖weightedJ S u v‖ ≤ g v) →
      (∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
          (radialCurvatureWith S u (vb u) v (radialZEM e S u (vb u)))‖) ≤
        ENNReal.ofReal (C * Local.sigma e M (2 * R₀) * F ^ 2 * (∫ s in v₀..0, g s)) := by
  obtain ⟨C₀, hC₀, hpoint⟩ := electromagnetic_mixed_source δ c Λ Cq hδ hc hΛ hCq
  refine ⟨C₀ / (2 * c * (2 - ε)), by positivity, ?_⟩
  intro e ui M R₀ u₀ u₁ v₀ ρ F S vb g N B hS hstop hM hF hR hupper hprofile hg hg0 hmajor
  let E := exteriorDomain ui u₀ u₁ vb
  let μ := volume.restrict (Icc v₀ 0)
  let β := C₀ * e ^ 2 * M ^ 2 * F ^ 2
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hSE : IsSolution e S E := Local.isSolution_mono hS inter_subset_left
  have h01 : u₀ ≤ u₁ := calc
    _ = B.cuts 0 := B.first.symm
    _ ≤ B.cuts (Fin.last N) := B.ordered (Fin.zero_le _)
    _ = _ := B.last
  have hv0 : v₀ ≤ 0 := (finite_boundary_label_bounds B u₀ ⟨le_rfl, h01⟩).1.trans
    (finite_boundary_label_bounds B u₀ ⟨le_rfl, h01⟩).2
  have ig : Integrable g μ := (intervalIntegrable_iff_integrableOn_Icc_of_le hv0).mp hg
  have hm : AEMeasurable (fun s => ENNReal.ofReal (g s)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable ig.aestronglyMeasurable.aemeasurable
  let G := hm.mk (fun s => ENNReal.ofReal (g s))
  have hG : Measurable G := hm.measurable_mk
  have hGeq : (fun s => ENNReal.ofReal (g s)) =ᵐ[μ] G := hm.ae_eq_mk
  have hmassG : (∫⁻ s in Icc v₀ 0, G s) = ENNReal.ofReal (∫ s in v₀..0, g s) := by
    rw [intervalIntegral.integral_of_le hv0, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal ig hg0]
    exact lintegral_congr_ae hGeq.symm
  have hbound (u : ℝ) (hu : u ∈ Icc u₀ u₁) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :
      ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
        (radialCurvatureWith S u (vb u) v (radialZEM e S u (vb u)))‖ ≤
        ENNReal.ofReal β * (ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, ENNReal.ofReal (S.r u s ^ 3) * G s)) := by
    have hs : outSeg u (vb u) v ⊆ E :=
      fun p hp => finite_boundary_row B u hu ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩
    have hgsub : uIcc (vb u) v ⊆ uIcc v₀ 0 := by
      rw [uIcc_of_le hv.1, uIcc_of_le hv0]
      exact Icc_subset_Icc (finite_boundary_label_bounds B u hu).1 hv.2
    have hsub : Icc (vb u) v ⊆ Icc v₀ 0 :=
      Icc_subset_Icc (finite_boundary_label_bounds B u hu).1 hv.2
    have hmp := (hmajor u hu).filter_mono (ae_mono (Measure.restrict_mono
      (Icc_subset_Icc le_rfl hv.2) le_rfl))
    have hpt := hpoint e M F ε S E u (vb u) v g hSE hstop
      (B.off_axis u hu) hv.1 hs hM hF
      (fun s hs' => (hprofile (u, s) (hs ⟨rfl, hs'⟩)).1)
      (fun s hs' => (hprofile (u, s) (hs ⟨rfl, hs'⟩)).2)
      (hg.mono_set hgsub) hmp
    have hr (s : ℝ) (hs' : s ∈ Icc (vb u) v) : 0 < S.r u s :=
      hSE.r_pos (u, s) (hs ⟨rfl, hs'⟩) ((B.off_axis u hu).trans_le hs'.1)
    have cr := Calculus.continuousOn_out_section hSE.cont_r hs
    have ir : IntervalIntegrable (fun s => S.r u s ^ 3 * g s) volume (vb u) v := by
      apply ((hg.mono_set hgsub).continuousOn_mul (by
        simpa only [uIcc_of_le hv.1] using cr.pow 3)).congr
      intro s _
      rfl
    have hreal : ENNReal.ofReal (∫ s in (vb u)..v, S.r u s ^ 3 * g s) =
        ∫⁻ s in Icc (vb u) v, ENNReal.ofReal (S.r u s ^ 3) * G s := by
      have h0 := hg0.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
      rw [intervalIntegral.integral_of_le hv.1, ← integral_Icc_eq_integral_Ioc,
        ofReal_integral_eq_lintegral_ofReal
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mp ir)
          (by filter_upwards [h0, ae_restrict_mem measurableSet_Icc] with s hgs hs';
              exact mul_nonneg (pow_nonneg (hr s hs').le 3) hgs)]
      apply lintegral_congr_ae
      filter_upwards [hGeq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
        ae_restrict_mem measurableSet_Icc] with s hgs hs'
      rw [ENNReal.ofReal_mul (pow_nonneg (hr s hs').le 3), hgs]
    have hn : 0 ≤ -S.nu u v :=
      (neg_pos.mpr (hSE.nu_neg (u, v) (hs ⟨rfl, hv.1, le_rfl⟩))).le
    have hrv := hr v ⟨hv.1, le_rfl⟩
    have hratio : 0 ≤ (-S.nu u v) / S.r u v ^ 3 := by positivity
    apply (ENNReal.ofReal_le_ofReal hpt).trans_eq
    change ENNReal.ofReal (β * ((-S.nu u v) / S.r u v ^ 3) * _) = _
    rw [ENNReal.ofReal_mul (mul_nonneg hβ hratio), ENNReal.ofReal_mul hβ, hreal, mul_assoc]
  calc
    _ ≤ ∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal β * (ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, ENNReal.ofReal (S.r u s ^ 3) * G s)) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      exact setLIntegral_mono' measurableSet_Icc (hbound u hu)
    _ = ENNReal.ofReal β * (∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3) *
          (∫⁻ s in Icc (vb u) v, ENNReal.ofReal (S.r u s ^ 3) * G s)) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal β * (ENNReal.ofReal (R₀ ^ 2 / (2 * c * (2 - ε))) *
        (∫⁻ s in Icc v₀ 0, G s)) := by
      gcongr
      exact electromagnetic_mixed_kernel hS B hstop hc hε hR hupper G hG
    _ = _ := by
      rw [hmassG, ← mul_assoc, ← ENNReal.ofReal_mul hβ,
        ← ENNReal.ofReal_mul (mul_nonneg hβ (by positivity)), ct_zeta]
      congr 1
      dsimp [β]
      ring

end EmcsfAcExtension.Global.InteractionEstimate
