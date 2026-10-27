module

public import EmcsfAcExtension.Local.Construction.PicardGap

/-! # Normalized radial calculus for the incoming construction

The compact rescaled interval keeps the scalar difference quotient in continuous
functions and outgoing first jets. This module supplies operators and estimates
for the radial `C¹_v` proof; it does not yet close that graph node.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The outgoing tail of a rescaled field. Its parameter extension is continuous
on `K × ℝ`; norm bounds below are restricted to the integration range. -/
@[expose] noncomputable def picardRadialTail (g : C(PicardDomain c a L, E)) :
    C(PicardDomain c a L × ℝ, E) where
  toFun q := ∫ s in q.2..1, g (picardRadialPoint q.1 s)
  continuous_toFun := by
    let F : PicardDomain c a L → ℝ → E := fun p s => g (picardRadialPoint p s)
    have hF : Continuous (Function.uncurry F) := g.continuous.comp continuous_picardRadialPoint
    have hFixed : Continuous (fun p => ∫ s in (0 : ℝ)..1, F p s) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 1
    have hPrim := intervalIntegral.continuous_parametric_primitive_of_continuous
      (μ := volume) (a₀ := 0) hF
    have heq : (fun q : PicardDomain c a L × ℝ => ∫ s in q.2..1, F q.1 s) =
        (fun q => (∫ s in (0 : ℝ)..1, F q.1 s) - ∫ s in (0 : ℝ)..q.2, F q.1 s) := by
      funext q
      have hc : Continuous (F q.1) := hF.comp (continuous_const.prodMk continuous_id)
      exact (intervalIntegral.integral_interval_sub_left
        (hc.intervalIntegrable (μ := volume) 0 1) (hc.intervalIntegrable (μ := volume) 0 q.2)).symm
    change Continuous (fun q : PicardDomain c a L × ℝ => ∫ s in q.2..1, F q.1 s)
    rw [heq]
    exact (hFixed.comp continuous_fst).sub hPrim

/-- The rescaled tail is bounded by the remaining interval length times `D`.
The numerical constant one is uniform in `c,a,L,E` and the field. -/
theorem picardRadialTail_norm_le (g : C(PicardDomain c a L, E)) {D t : ℝ}
    (hg : ∀ q, ‖g q‖ ≤ D) (p : PicardDomain c a L) (ht : t ≤ 1) :
    ‖picardRadialTail g (p, t)‖ ≤ D * (1 - t) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => g (picardRadialPoint p s)) (a := t) (b := 1)
    (fun s _ => hg (picardRadialPoint p s))
  change ‖∫ s in t..1, g (picardRadialPoint p s)‖ ≤ D * (1 - t)
  simpa only [abs_of_nonneg (sub_nonneg.mpr ht)] using hb

/-- The nested radial integral in the scalar difference quotient (internal project record A1). -/
@[expose] noncomputable def picardRadialBilinear (f : C(PicardDomain c a L, ℝ))
    (g : C(PicardDomain c a L, E)) : C(PicardDomain c a L, E) where
  toFun p := ∫ t in (0 : ℝ)..1, f (picardRadialPoint p t) • picardRadialTail g (p, t)
  continuous_toFun := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (f.continuous.comp continuous_picardRadialPoint).smul (picardRadialTail g).continuous

/-- The nested radial kernel has total mass `1/2`. The displayed bound is
uniform in `c,a,L,E`, the fields and the evaluation point. -/
theorem picardRadialBilinear_norm_le (f : C(PicardDomain c a L, ℝ)) (g : C(PicardDomain c a L, E))
    {U D : ℝ} (hU : 0 ≤ U) (_hD : 0 ≤ D) (hf : ∀ q, |f q| ≤ U) (hg : ∀ q, ‖g q‖ ≤ D)
    (p : PicardDomain c a L) : ‖picardRadialBilinear f g p‖ ≤ U * D / 2 := by
  have hBound : IntervalIntegrable (fun t : ℝ => U * D * (1 - t)) volume 0 1 :=
    ((continuous_const.mul continuous_const).mul
      (continuous_const.sub continuous_id)).intervalIntegrable 0 1
  have hb := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun t => f (picardRadialPoint p t) • picardRadialTail g (p, t))
    (by norm_num : (0 : ℝ) ≤ 1) (Filter.Eventually.of_forall (fun t ht => by
      rw [norm_smul, Real.norm_eq_abs]
      have hTail := picardRadialTail_norm_le g hg p ht.2
      calc
        |f (picardRadialPoint p t)| * ‖picardRadialTail g (p, t)‖ ≤ U * (D * (1 - t)) :=
          mul_le_mul (hf _) hTail (norm_nonneg _) hU
        _ = U * D * (1 - t) := by ring))
    hBound
  have hInt : (∫ t in (0 : ℝ)..1, U * D * (1 - t)) = U * D / 2 := by
    have hOne : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := intervalIntegrable_const
    have hId : IntervalIntegrable (fun t : ℝ => t) volume 0 1 :=
      continuous_id.intervalIntegrable 0 1
    have hUnit : (∫ t in (0 : ℝ)..1, 1 - t) = (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_sub hOne hId]
      norm_num
    rw [intervalIntegral.integral_const_mul, hUnit]
    ring
  rw [hInt] at hb
  change ‖∫ t in (0 : ℝ)..1, f (picardRadialPoint p t) • picardRadialTail g (p, t)‖ ≤ U * D / 2
  exact hb
private theorem picardRadialIntegrand_cont_aux (f : C(PicardDomain c a L, ℝ))
    (g : C(PicardDomain c a L, E)) :
    Continuous (fun q : PicardDomain c a L × ℝ =>
      f (picardRadialPoint q.1 q.2) • picardRadialTail g q) :=
  (f.continuous.comp continuous_picardRadialPoint).smul (picardRadialTail g).continuous

/-- Rescaled tails commute with subtraction. -/
theorem picardRadialTail_sub (g h : C(PicardDomain c a L, E)) :
    picardRadialTail (g - h) = picardRadialTail g - picardRadialTail h := by
  ext q
  have hc (f : C(PicardDomain c a L, E)) : Continuous (fun s => f (picardRadialPoint q.1 s)) :=
    f.continuous.comp (continuous_picardRadialPoint.comp (continuous_const.prodMk continuous_id))
  change (∫ s in q.2..1, g (picardRadialPoint q.1 s) - h (picardRadialPoint q.1 s)) =
    (∫ s in q.2..1, g (picardRadialPoint q.1 s)) - (∫ s in q.2..1, h (picardRadialPoint q.1 s))
  exact intervalIntegral.integral_sub
    ((hc g).intervalIntegrable q.2 1) ((hc h).intervalIntegrable q.2 1)

/-- The nested radial integral is linear in its real head field. -/
theorem picardRadialBilinear_sub_left (f h : C(PicardDomain c a L, ℝ))
    (g : C(PicardDomain c a L, E)) :
    picardRadialBilinear (f - h) g = picardRadialBilinear f g - picardRadialBilinear h g := by
  ext p
  have hc (f : C(PicardDomain c a L, ℝ)) :
      Continuous (fun t => f (picardRadialPoint p t) • picardRadialTail g (p, t)) :=
    (picardRadialIntegrand_cont_aux f g).comp (continuous_const.prodMk continuous_id)
  change (∫ t in (0 : ℝ)..1, (f (picardRadialPoint p t) - h (picardRadialPoint p t)) •
    picardRadialTail g (p, t)) = _
  simp_rw [sub_smul]
  exact intervalIntegral.integral_sub
    ((hc f).intervalIntegrable 0 1) ((hc h).intervalIntegrable 0 1)

/-- The nested radial integral is linear in its vector tail field. -/
theorem picardRadialBilinear_sub_right (f : C(PicardDomain c a L, ℝ))
    (g h : C(PicardDomain c a L, E)) :
    picardRadialBilinear f (g - h) = picardRadialBilinear f g - picardRadialBilinear f h := by
  ext p
  have hc (g : C(PicardDomain c a L, E)) :
      Continuous (fun t => f (picardRadialPoint p t) • picardRadialTail g (p, t)) :=
    (picardRadialIntegrand_cont_aux f g).comp (continuous_const.prodMk continuous_id)
  change (∫ t in (0 : ℝ)..1, f (picardRadialPoint p t) • picardRadialTail (g - h) (p, t)) = _
  rw [picardRadialTail_sub]
  change (∫ t in (0 : ℝ)..1, f (picardRadialPoint p t) •
    (picardRadialTail g (p, t) - picardRadialTail h (p, t))) = _
  simp_rw [smul_sub]
  exact intervalIntegral.integral_sub
    ((hc g).intervalIntegrable 0 1) ((hc h).intervalIntegrable 0 1)

/-- The bilinear operator has norm bound `1/2`, uniformly in `c,a,L,E`. -/
theorem picardRadialBilinear_norm (f : C(PicardDomain c a L, ℝ))
    (g : C(PicardDomain c a L, E)) : ‖picardRadialBilinear f g‖ ≤ ‖f‖ * ‖g‖ / 2 := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  exact picardRadialBilinear_norm_le f g (norm_nonneg _) (norm_nonneg _)
    (fun q => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm q)
    (fun q => g.norm_coe_le_norm q) p

/-- The bilinear difference bound with universal coefficient `1/2`.
It is uniform in the wedge geometry and all fields. -/
theorem picardRadialBilinear_dist_le (f f' : C(PicardDomain c a L, ℝ))
    (g g' : C(PicardDomain c a L, E)) :
    dist (picardRadialBilinear f g) (picardRadialBilinear f' g') ≤
      (dist f f' * ‖g‖ + ‖f'‖ * dist g g') / 2 := by
  have hsub : picardRadialBilinear f g - picardRadialBilinear f' g' =
      picardRadialBilinear (f - f') g + picardRadialBilinear f' (g - g') := by
    rw [picardRadialBilinear_sub_left, picardRadialBilinear_sub_right]
    abel
  simp only [dist_eq_norm]
  rw [hsub]
  calc
    _ ≤ ‖picardRadialBilinear (f - f') g‖ + ‖picardRadialBilinear f' (g - g')‖ := norm_add_le _ _
    _ ≤ ‖f - f'‖ * ‖g‖ / 2 + ‖f'‖ * ‖g - g'‖ / 2 :=
      add_le_add (picardRadialBilinear_norm _ _) (picardRadialBilinear_norm _ _)
    _ = (‖f - f'‖ * ‖g‖ + ‖f'‖ * ‖g - g'‖) / 2 := by ring

/-- The real value component of a Picard candidate. -/
@[expose] noncomputable def picardLamValues (z : PicardCarrier c a L (ℝ × ℂ)) :
    C(PicardDomain c a L, ℝ) :=
  ⟨fun p => (z.1.1 p).1, z.1.1.continuous.fst⟩
/-- The outgoing scalar jet of a Picard candidate. -/
@[expose] noncomputable def picardHJets (z : PicardCarrier c a L (ℝ × ℂ)) :
    C(PicardDomain c a L, ℂ) :=
  ⟨fun p => (z.1.2 p).2, z.1.2.continuous.snd⟩
/-- The continuous normalized scalar remainder `f / (v-u)` from internal project record A1.
Its denominator is the radial average of the positive candidate lambda. -/
@[expose] noncomputable def picardScalarRemainder (ℓ : ℝ) (hℓ : 0 < ℓ)
    (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q : PicardDomain c a L, ℓ ≤ (z.1.1 q).1) : C(PicardDomain c a L, ℂ) where
  toFun p := (picardRadialAverage (picardLamValues z) p)⁻¹ •
    picardRadialBilinear (picardLamValues z) (picardHJets z) p
  continuous_toFun := by
    have hpos (p : PicardDomain c a L) : 0 < picardRadialAverage (picardLamValues z) p :=
      hℓ.trans_le (picardRadialAverage_lower _ hl p)
    exact ((picardRadialAverage (picardLamValues z)).continuous.inv₀
      (fun p => (hpos p).ne')).smul
      (picardRadialBilinear (picardLamValues z) (picardHJets z)).continuous

/-- Exact normalized formula for the existing difference quotient. It holds
on the axis as well as on the positive-radius region. -/
theorem picard_ratio_eq_normalized (ha : 0 ≤ a) (haL : a ≤ L) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q : PicardDomain c a L, ℓ ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) :
    Recon.ratio (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 =
      (p.1.2 - p.1.1) • picardScalarRemainder ℓ hℓ z hl p := by
  rcases lt_or_eq_of_le p.2.1.2.1 with hp | hp
  · let x := p.1.2 - p.1.1
    let R := picardRadialAverage (picardLamValues z) p
    let J := picardRadialBilinear (picardLamValues z) (picardHJets z) p
    have hx : 0 < x := sub_pos.mpr hp
    have hR : 0 < R := hℓ.trans_le (picardRadialAverage_lower _ hl p)
    have hr := picard_recon_r_eq_radialAverage ha haL z p
    have hrpos : 0 < Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 := by
      rw [hr]
      exact mul_pos hx hR
    have hrC : (Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 : ℂ) ≠ 0 := by
      exact_mod_cast hrpos.ne'
    have hlamc : Continuous (picardCandidateLam ha haL z p.1.1) :=
      (continuous_picardCandidateLam ha haL z).comp (continuous_const.prodMk continuous_id)
    have hhc : Continuous (picardCandidateH ha haL z p.1.1) :=
      (continuous_picardCandidateH ha haL z).comp (continuous_const.prodMk continuous_id)
    have hRaw : (Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 : ℂ) *
        Recon.ratio (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 =
        ∫ s in p.1.1..p.1.2, (picardCandidateLam ha haL z p.1.1 s : ℂ) *
          (picardCandidateH ha haL z p.1.1 p.1.2 - picardCandidateH ha haL z p.1.1 s) := by
      rw [Recon.picard_ratio_eq_phi_increment_aux hp hrpos hlamc hhc,
        Recon.phi_def, ite_eq_left hp]
      field_simp
    have hMul : (∫ s in p.1.1..p.1.2, (picardCandidateLam ha haL z p.1.1 s : ℂ) *
          (picardCandidateH ha haL z p.1.1 p.1.2 - picardCandidateH ha haL z p.1.1 s)) =
        ∫ s in p.1.1..p.1.2, picardCandidateLam ha haL z p.1.1 s •
          (picardCandidateH ha haL z p.1.1 p.1.2 - picardCandidateH ha haL z p.1.1 s) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      symm
      exact Complex.real_smul
    rw [hMul] at hRaw
    have hOuter := intervalIntegral.smul_integral_comp_mul_add
      (f := fun s => picardCandidateLam ha haL z p.1.1 s •
        (picardCandidateH ha haL z p.1.1 p.1.2 - picardCandidateH ha haL z p.1.1 s))
      (a := 0) (b := 1) x p.1.1
    have he : x * 1 + p.1.1 = p.1.2 := by dsimp [x]; ring
    simp only [mul_zero, zero_add] at hOuter
    rw [he] at hOuter
    have hI : (∫ t in (0 : ℝ)..1,
        picardCandidateLam ha haL z p.1.1 (x * t + p.1.1) •
          (picardCandidateH ha haL z p.1.1 p.1.2 -
            picardCandidateH ha haL z p.1.1 (x * t + p.1.1))) =
        ∫ t in (0 : ℝ)..1, (z.1.1 (picardRadialPoint p t)).1 •
          ((z.1.1 p).2 - (z.1.1 (picardRadialPoint p t)).2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have hlam := picardCandidateLam_coe ha haL z (picardRadialPoint p t)
      have hh := picardCandidateH_coe ha haL z (picardRadialPoint p t)
      simp only [picardRadialPoint_of_mem p ht] at hlam hh
      have hlam' : picardCandidateLam ha haL z p.1.1 (x * t + p.1.1) =
          (z.1.1 (picardRadialPoint p t)).1 := by
        simpa only [x, add_comm, mul_comm] using hlam
      have hh' : picardCandidateH ha haL z p.1.1 (x * t + p.1.1) =
          (z.1.1 (picardRadialPoint p t)).2 := by
        simpa only [x, add_comm, mul_comm] using hh
      change picardCandidateLam ha haL z p.1.1 (x * t + p.1.1) •
        (picardCandidateH ha haL z p.1.1 p.1.2 - picardCandidateH ha haL z p.1.1 (x * t + p.1.1)) =
        (z.1.1 (picardRadialPoint p t)).1 • ((z.1.1 p).2 - (z.1.1 (picardRadialPoint p t)).2)
      rw [hlam', hh', picardCandidateH_coe ha haL z p]
    rw [hI] at hOuter
    have hJ : (∫ t in (0 : ℝ)..1, (z.1.1 (picardRadialPoint p t)).1 •
        ((z.1.1 p).2 - (z.1.1 (picardRadialPoint p t)).2)) = x • J := by
      change _ = x • ∫ t in (0 : ℝ)..1,
        (z.1.1 (picardRadialPoint p t)).1 • picardRadialTail (picardHJets z) (p, t)
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have hi := picardCarrier_h_increment_radial z p ht
      change (z.1.1 p).2 - (z.1.1 (picardRadialPoint p t)).2 =
        x • picardRadialTail (picardHJets z) (p, t) at hi
      change (z.1.1 (picardRadialPoint p t)).1 •
        ((z.1.1 p).2 - (z.1.1 (picardRadialPoint p t)).2) =
        x • ((z.1.1 (picardRadialPoint p t)).1 • picardRadialTail (picardHJets z) (p, t))
      rw [hi, smul_smul, smul_smul, mul_comm]
    have hWeighted := hRaw.trans hOuter.symm
    rw [hJ, hr] at hWeighted
    change ((x * R : ℝ) : ℂ) *
      Recon.ratio (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 =
        x • (x • J) at hWeighted
    have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    have hxRC : ((x * R : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero hx.ne' hR.ne'
    change _ = x • (R⁻¹ • J)
    apply mul_left_cancel₀ hxRC
    calc
      _ = x • (x • J) := hWeighted
      _ = ((x * R : ℝ) : ℂ) * (x • (R⁻¹ • J)) := by
        simp only [Complex.real_smul]
        push_cast
        field_simp
  · simp [hp, Recon.ratio_def, Recon.phi_def]
/-- Continuous scalar reconstruction values on the whole closed wedge. -/
@[expose] noncomputable def picardPhiValues (ℓ : ℝ) (hℓ : 0 < ℓ)
    (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q : PicardDomain c a L, ℓ ≤ (z.1.1 q).1) : C(PicardDomain c a L, ℂ) where
  toFun p := (z.1.1 p).2 - (p.1.2 - p.1.1) • picardScalarRemainder ℓ hℓ z hl p
  continuous_toFun := z.1.1.continuous.snd.sub
    (((continuous_snd.comp continuous_subtype_val).sub
      (continuous_fst.comp continuous_subtype_val)).smul
        (picardScalarRemainder ℓ hℓ z hl).continuous)
/-- Continuous outgoing scalar reconstruction jets, including the axis. -/
@[expose] noncomputable def picardPhiJets (ℓ : ℝ) (hℓ : 0 < ℓ)
    (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q : PicardDomain c a L, ℓ ≤ (z.1.1 q).1) : C(PicardDomain c a L, ℂ) where
  toFun p := ((z.1.1 p).1 / picardRadialAverage (picardLamValues z) p) •
    picardScalarRemainder ℓ hℓ z hl p
  continuous_toFun := by
    have hpos (p : PicardDomain c a L) : 0 < picardRadialAverage (picardLamValues z) p :=
      hℓ.trans_le (picardRadialAverage_lower _ hl p)
    exact (z.1.1.continuous.fst.div (picardRadialAverage (picardLamValues z)).continuous
      (fun p => (hpos p).ne')).smul (picardScalarRemainder ℓ hℓ z hl).continuous

/-- The normalized scalar values equal the existing `Recon.phi` definition. -/
theorem picardPhiValues_eq_recon (ha : 0 ≤ a) (haL : a ≤ L) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q : PicardDomain c a L, ℓ ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) : picardPhiValues ℓ hℓ z hl p =
      Recon.phi (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 := by
  have h := picard_ratio_eq_normalized ha haL ℓ hℓ z hl p
  rw [Recon.ratio_def, picardCandidateH_coe ha haL z p] at h
  change (z.1.1 p).2 - (p.1.2 - p.1.1) • picardScalarRemainder ℓ hℓ z hl p = _
  rw [← h]
  abel

/-- The off-axis derivative of the literal scalar reconstruction equals the
continuous normalized jet. This auxiliary is independent of internal project record. -/
theorem picardPhi_hasDerivAt_aux (ha : 0 ≤ a) (haL : a ≤ L) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q : PicardDomain c a L, ℓ ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) (hp : p.1.1 < p.1.2) :
    HasDerivAt (Recon.phi (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1)
      (picardPhiJets ℓ hℓ z hl p) p.1.2 := by
  let x := p.1.2 - p.1.1
  let R := picardRadialAverage (picardLamValues z) p
  have hx : 0 < x := sub_pos.mpr hp
  have hR : 0 < R := hℓ.trans_le (picardRadialAverage_lower _ hl p)
  have hr := picard_recon_r_eq_radialAverage ha haL z p
  have hrpos : 0 < Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 := by
    rw [hr]
    exact mul_pos hx hR
  have hlamc : Continuous (picardCandidateLam ha haL z p.1.1) :=
    (continuous_picardCandidateLam ha haL z).comp (continuous_const.prodMk continuous_id)
  have hhc : Continuous (picardCandidateH ha haL z p.1.1) :=
    (continuous_picardCandidateH ha haL z).comp (continuous_const.prodMk continuous_id)
  have h := Recon.phi_hasDerivAt_of_r_pos_aux hp hrpos hlamc hhc
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  convert h using 1
  rw [picard_recon_r_eq_radialAverage ha haL z p, picard_ratio_eq_normalized ha haL ℓ hℓ z hl p,
    picardCandidateLam_coe ha haL z p]
  change ((z.1.1 p).1 / R) • picardScalarRemainder ℓ hℓ z hl p =
    (((z.1.1 p).1 / (x * R) : ℝ) : ℂ) * (x • picardScalarRemainder ℓ hℓ z hl p)
  simp only [Complex.real_smul]
  push_cast
  field_simp

/-- The existing scalar reconstruction as an outgoing continuously differentiable
carrier. Only positivity of lambda and the candidate carrier are required. -/
@[expose] noncomputable def picardScalarRecon (ha : 0 ≤ a) (haL : a ≤ L) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q : PicardDomain c a L, ℓ ≤ (z.1.1 q).1) :
    PicardCarrier c a L ℂ :=
  picardCarrierOfRawDeriv
    (Recon.phi (picardCandidateLam ha haL z) (picardCandidateH ha haL z))
    (picardPhiValues ℓ hℓ z hl) (picardPhiJets ℓ hℓ z hl)
    (picardPhiValues_eq_recon ha haL ℓ hℓ z hl)
    (fun p hp _ => picardPhi_hasDerivAt_aux ha haL ℓ hℓ z hl p hp)

end EmcsfAcExtension.Local
