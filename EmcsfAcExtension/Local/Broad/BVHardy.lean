module

public import EmcsfAcExtension.Local.Broad.ScalarAverage
public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
public import EmcsfAcExtension.Infra.HardyBV
import EmcsfAcExtension.Infra.Null.Segments

/-! # Continuous BV Hardy bounds in the matching characteristic direction

The outgoing estimate applies to continuous BV traces, including singular
derivative measures. It uses the variation-majorant proof in `Infra.HardyBV`.
Incoming variation must be measured in a parallel frame (internal project record).
-/

public section

open Set MeasureTheory Filter Complex
open scoped Topology
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

private def clip (H x : ℝ) : ℝ := max 0 (min H x)

private theorem clip_continuous (H : ℝ) : Continuous (clip H) :=
  continuous_const.max (continuous_const.min continuous_id)

private theorem clip_monotone (H : ℝ) : Monotone (clip H) :=
  monotone_const.max (monotone_const.min monotone_id)

private theorem clip_mem {H : ℝ} (hH : 0 ≤ H) (x : ℝ) : clip H x ∈ Icc 0 H :=
  ⟨le_max_left _ _, max_le hH (min_le_left _ _)⟩

private theorem clip_eq {H x : ℝ} (hx : x ∈ Icc 0 H) : clip H x = x := by
  simp only [clip, min_eq_right hx.2, max_eq_right hx.1]

private theorem clip_bv {H : ℝ} (hH : 0 ≤ H) :
    BoundedVariationOn (clip H) univ :=
  ((clip_monotone H).monotoneOn univ).boundedVariationOn (C := H) (by
    intro x _
    rw [abs_of_nonneg (clip_mem hH x).1]
    exact (clip_mem hH x).2)

private theorem clip_measure {H : ℝ} (hH : 0 ≤ H) :
    (clip_bv hH).vectorMeasure = (volume.restrict (Icc 0 H)).toSignedMeasure := by
  apply VectorMeasure.ext_of_Icc
  intro a b hab
  rw [BoundedVariationOn.vectorMeasure_Icc _ hab,
    (clip_continuous H).continuousAt.continuousWithinAt.rightLim_eq,
    (clip_continuous H).continuousAt.continuousWithinAt.leftLim_eq,
    Measure.toSignedMeasure_apply_measurable measurableSet_Icc]
  simp only [Measure.real, Measure.restrict_apply measurableSet_Icc, Icc_inter_Icc,
    Real.volume_Icc, ENNReal.toReal_ofReal', clip]
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
    rcases le_total H a with hHa | hHa <;> rcases le_total H b with hHb | hHb <;>
    simp_all <;> linarith

/-- Constant extension of a trace on `[0,H]` to the real line. The values outside
the interval are its endpoint values, so a continuous trace stays continuous. -/
@[expose] def constant_extension (H : ℝ) (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  F (max 0 (min H x))

/-- Constant extension preserves bounded variation. No derivative or absolute
continuity is needed. -/
theorem boundedVariationOn_constant_extension {H : ℝ} {F : ℝ → ℂ}
    (hH : 0 ≤ H) (hBV : BoundedVariationOn F (Icc 0 H)) :
    BoundedVariationOn (constant_extension H F) univ :=
  ne_top_of_le_ne_top hBV (eVariationOn.comp_le_of_monotoneOn F (clip H)
    ((clip_monotone H).monotoneOn univ) (fun x _ => clip_mem hH x))

/-- The continuous BV radial moment in its Stieltjes form. The measure is the
vector measure of the trace extended constantly off `[0,H]`. This exact identity
has no constant, no AC hypothesis, and no derivative-density assumption. -/
theorem continuous_bv_radial_moment {H ρ : ℝ} {F : ℝ → ℂ}
    (hH : 0 ≤ H) (hρ : ρ ∈ Icc 0 H) (hF : ContinuousOn F (Icc 0 H))
    (hBV : BoundedVariationOn F (Icc 0 H)) :
    let hExt := boundedVariationOn_constant_extension hH hBV
    (∫ᵛ x in Ioc 0 ρ, x ∂•hExt.vectorMeasure) =
      (ρ : ℂ) * F ρ - ∫ x in 0..ρ, F x := by
  dsimp only
  let G := constant_extension H F
  have hG : Continuous G := hF.comp_continuous (clip_continuous H)
    (fun x => clip_mem hH x)
  have hGBV : BoundedVariationOn G univ := boundedVariationOn_constant_extension hH hBV
  have heq := (clip_bv hH).setIntegral_Ioc_leftLim_smul_vectorMeasure_eq_sub hGBV hρ.1
  have hcl : (clip H).leftLim = clip H := funext fun x =>
    (clip_continuous H).continuousAt.continuousWithinAt.leftLim_eq
  have hcr : (clip H).rightLim = clip H := funext fun x =>
    (clip_continuous H).continuousAt.continuousWithinAt.rightLim_eq
  have hgr : G.rightLim = G := funext fun x =>
    hG.continuousAt.continuousWithinAt.rightLim_eq
  rw [hcl, hcr, hgr, clip_eq hρ, clip_eq (show (0 : ℝ) ∈ Icc 0 H from ⟨le_rfl, hH⟩),
    zero_smul, sub_zero, clip_measure hH,
    VectorMeasure.setIntegral_toSignedMeasure measurableSet_Ioc] at heq
  have hcint : (∫ᵛ x in Ioc 0 ρ, clip H x ∂•hGBV.vectorMeasure) =
      ∫ᵛ x in Ioc 0 ρ, x ∂•hGBV.vectorMeasure := by
    apply VectorMeasure.setIntegral_congr_fun
    intro x hx
    exact clip_eq ⟨hx.1.le, hx.2.trans hρ.2⟩
  have hGint : (∫ x in Ioc 0 ρ, G x ∂volume.restrict (Icc 0 H)) =
      ∫ x in 0..ρ, F x := by
    rw [Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (show Ioc 0 ρ ⊆ Icc 0 H from fun x hx =>
        ⟨hx.1.le, hx.2.trans hρ.2⟩), intervalIntegral.integral_of_le hρ.1]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    change F (clip H x) = F x
    rw [clip_eq ⟨hx.1.le, hx.2.trans hρ.2⟩]
  rw [hcint, hGint] at heq
  change (∫ᵛ x in Ioc 0 ρ, x ∂•hGBV.vectorMeasure) =
    (ρ : ℂ) * F ρ - ∫ x in 0..ρ, F x
  simpa only [G, constant_extension, min_eq_right hρ.2, max_eq_right hρ.1,
    Complex.real_smul] using heq

/-- [node restart-stab-broad-uniqueness#incoming-Stieltjes-radial-identity]
The incoming radial Stieltjes identity in its parallel-frame reading,
charged_SF_new_version.tex:L5715–5720 and internal project record (S). The radial averaging identity
and
the BV trace are in the same frame `P`; ordinary and transported variation
are never identified. This is an exact identity without a constant. -/
theorem incoming_stieltjes_radial_identity {H ρ : ℝ} {F P b phi : ℝ → ℂ}
    (hρ : ρ ∈ Ioc 0 H) (hF : ContinuousOn F (Icc 0 H))
    (hBV : BoundedVariationOn F (Icc 0 H))
    (hframe : F ρ = P ρ * b ρ)
    (haverage : (ρ : ℂ) * P ρ * phi ρ = ∫ x in 0..ρ, F x) :
    P ρ * (b ρ - phi ρ) = (ρ : ℂ)⁻¹ *
      ∫ᵛ x in Ioc 0 ρ, x ∂•(boundedVariationOn_constant_extension
        (hρ.1.le.trans hρ.2) hBV).vectorMeasure := by
  have hmoment := continuous_bv_radial_moment (hρ.1.le.trans hρ.2) ⟨hρ.1.le, hρ.2⟩ hF hBV
  dsimp only at hmoment
  rw [hmoment, hframe, ← haverage]
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.1.ne'
  field_simp [hρC]



/-- [node restart-stab-broad-uniqueness#outgoing-BV-Hardy]
The outgoing Hardy bound for an arbitrary continuous BV normalized trace with
its radial averaging identity, charged_SF_new_version.tex:L5737 and internal project record (HO).
The exact
constant one is universal, independent of the weight, trace, interval and BV
budget. Absolute continuity of the normalized trace is not assumed. -/
theorem outgoing_bv_hardy {u v : ℝ} {lam r : ℝ → ℝ} {a phi : ℝ → ℂ}
    (huv : u ≤ v) (hlam : ContinuousOn lam (Icc u v))
    (hlam0 : ∀ x ∈ Icc u v, 0 ≤ lam x)
    (ha : ContinuousOn a (Icc u v)) (hbv : BoundedVariationOn a (Icc u v))
    (hr : ∀ x ∈ Icc u v, r x = ∫ y in u..x, lam y)
    (hphi : ∀ x ∈ Ioc u v, (r x : ℂ) * phi x = ∫ y in u..x, (lam y : ℂ) * a y) :
    IntervalIntegrable (fun x => lam x / r x * ‖a x - phi x‖) volume u v ∧
      (∫ x in u..v, lam x / r x * ‖a x - phi x‖) ≤
        (eVariationOn a (Icc u v)).toReal := by
  have hi := integrable_and_integral_weighted_deviation_le_variation huv
    (ContinuousOn.intervalIntegrable_of_Icc huv hlam) hlam0 ha hbv
  have heq : ∀ x ∈ uIcc u v,
      lam x / (∫ y in u..x, lam y) * ‖a x - radialAverage lam a u x‖ =
        lam x / r x * ‖a x - phi x‖ := by
    intro x hx
    rw [uIcc_of_le huv] at hx
    rw [← hr x hx]
    by_cases hrx : r x = 0
    · simp only [hrx, div_zero, zero_mul]
    · have hxu : u < x := by
        apply lt_of_le_of_ne hx.1
        intro h
        subst x
        exact hrx (by simpa using hr u ⟨le_rfl, huv⟩)
      have hphi' : radialAverage lam a u x = phi x := by
        dsimp only [radialAverage]
        rw [← hr x hx]
        change (r x)⁻¹ • (∫ y in u..x, (lam y : ℂ) * a y) = phi x
        rw [← hphi x ⟨hxu, hx.2⟩, Complex.real_smul, Complex.ofReal_inv,
          ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hrx), one_mul]
      rw [hphi']
  exact ⟨hi.1.congr (fun x hx => heq x (uIoc_subset_uIcc hx)),
    (intervalIntegral.integral_congr heq).symm.trans_le hi.2⟩

/-- Applying the continuous BV theorem to a frozen outgoing section costs its
ordinary characteristic variation, with exact universal coefficient one. -/
theorem outgoing_bv_hardy_solution {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) :
    IntervalIntegrable (fun x => S.lam u x / S.r u x *
      ‖S.theta u x / S.lam u x‖) volume u v ∧
      (∫ x in u..v, S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖) ≤
        (eVariationOn (S.a u) (Icc u v)).toReal := by
  have hbv := (hS.ac_out u u v huv hseg).2.2.2.2.boundedVariationOn_Icc huv
  have hi := outgoing_bv_hardy huv (continuousOn_out_section hS.cont_lam hseg)
    (fun x hx => (hS.lam_pos (u, x) (hseg ⟨rfl, hx⟩)).le)
    (continuousOn_out_section (IsSolution.cont_a hS) hseg) hbv
    (fun x hx => (outgoing_radius_reconstruction hS hx.1 (by
      rintro p ⟨rfl, hp⟩
      exact hseg ⟨rfl, hp.1, hp.2.trans hx.2⟩)).symm)
    (fun x hx => outgoing_scalar_reconstruction hS hx.1.le (by
      rintro p ⟨rfl, hp⟩
      exact hseg ⟨rfl, hp.1, hp.2.trans hx.2⟩))
  simpa only [Fields.a, add_sub_cancel_left] using hi

/-- The outgoing oscillatory scalar ratio is bounded by the ordinary
variation of the outgoing normalized trace. The exact coefficient one is
uniform in the solution and complete section. -/
theorem norm_outgoing_ratio_le_variation {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) :
    ‖S.theta u v / S.lam u v‖ ≤ (eVariationOn (S.a u) (Icc u v)).toReal := by
  rcases eq_or_lt_of_le huv with huv | huv
  · subst v
    have hz : S.theta u u / S.lam u u = 0 := by
      simpa only [Fields.a, add_eq_left] using
        (hS.axis u (hseg ⟨rfl, le_rfl, le_rfl⟩)).2.2.2.2.1
    rw [hz, norm_zero]
    exact ENNReal.toReal_nonneg
  · have hbv := (hS.ac_out u u v huv.le hseg).2.2.2.2.boundedVariationOn_Icc huv.le
    have hb := scalar_average_bracket_bound hS huv hseg (right_mem_Icc.mpr huv.le)
      (fun x hx y hy => by simpa only [dist_eq_norm] using hbv.dist_le hx hy)
    simpa only [Fields.a, add_sub_cancel_left] using hb

/-- [node restart-stab-broad-uniqueness#incoming-BV-Hardy]
Incoming Hardy in radial coordinates and a unitary parallel frame,
charged_SF_new_version.tex:L5511–5733, with the binding internal project record reading of internal
project record.
The exact universal coefficient is one. The right side is the variation of
the transported trace `F = P b`; there is no ordinary-variation substitution
or AC assumption on that trace. -/
theorem incoming_bv_hardy {H : ℝ} {F P b phi : ℝ → ℂ}
    (hH : 0 ≤ H) (hF : ContinuousOn F (Icc 0 H))
    (hBV : BoundedVariationOn F (Icc 0 H))
    (hframe : ∀ ρ ∈ Ioc 0 H, F ρ = P ρ * b ρ)
    (hunit : ∀ ρ ∈ Ioc 0 H, ‖P ρ‖ = 1)
    (haverage : ∀ ρ ∈ Ioc 0 H,
      (ρ : ℂ) * P ρ * phi ρ = ∫ x in 0..ρ, F x) :
    IntervalIntegrable (fun ρ => 1 / ρ * ‖b ρ - phi ρ‖) volume 0 H ∧
      (∫ ρ in 0..H, 1 / ρ * ‖b ρ - phi ρ‖) ≤
        (eVariationOn F (Icc 0 H)).toReal := by
  have hi := outgoing_bv_hardy (lam := fun _ => 1) (r := id)
    (a := F) (phi := fun ρ => P ρ * phi ρ) hH continuousOn_const
    (fun _ _ => zero_le_one) hF hBV
    (fun x _ => by simp)
    (fun x hx => by simpa only [id_eq, Complex.ofReal_one, one_mul, mul_assoc] using haverage x hx)
  have heq : ∀ ρ ∈ uIcc 0 H,
      1 / ρ * ‖F ρ - P ρ * phi ρ‖ = 1 / ρ * ‖b ρ - phi ρ‖ := by
    intro ρ hρ
    rw [uIcc_of_le hH] at hρ
    rcases eq_or_lt_of_le hρ.1 with hρ0 | hρpos
    · rw [← hρ0, div_zero, zero_mul, zero_mul]
    · rw [hframe ρ ⟨hρpos, hρ.2⟩, ← mul_sub, norm_mul,
        hunit ρ ⟨hρpos, hρ.2⟩, one_mul]
  exact ⟨hi.1.congr (fun x hx => heq x (uIoc_subset_uIcc hx)),
    (intervalIntegral.integral_congr heq).symm.trans_le hi.2⟩

/-- Incoming Hardy on a complete frozen section, with the variation of its
actual unitary parallel representative. Its exact coefficient is one. This
does not assume incoming AC regularity of `b`, and does not replace transported
variation by ordinary variation. -/
theorem incoming_bv_hardy_solution {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : inSeg u v v ⊆ D) :
    IntervalIntegrable (fun x => (-S.nu x v) / S.r x v *
      ‖S.xi x v / S.nu x v‖) volume u v ∧
      (∫ x in u..v, (-S.nu x v) / S.r x v * ‖S.xi x v / S.nu x v‖) ≤
        (eVariationOn (fun x => Complex.exp (I * e * (∫ y in v..x, S.A y v : ℝ)) *
          S.b x v) (Icc u v)).toReal := by
  let P := fun x => Complex.exp (I * e * (∫ y in v..x, S.A y v : ℝ))
  let F := fun x => P x * S.b x v
  have hPnorm (x : ℝ) : ‖P x‖ = 1 := Area.incoming_parallel_factor_norm e v x v S
  have cA := continuousOn_in_section hS.cont_A hseg
  have iA := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cA
  have hθ := (iA.absolutelyContinuousOnInterval_intervalIntegral right_mem_uIcc).const_smul e
  have hPAC : AbsolutelyContinuousOnInterval P u v := by
    simpa only [P, smul_eq_mul, Complex.ofReal_mul, mul_assoc] using hθ.unit_phase
  have cP : ContinuousOn P (Icc u v) := by
    simpa only [uIcc_of_le huv] using hPAC.continuousOn
  have cb := continuousOn_in_section (IsSolution.cont_b hS) hseg
  obtain ⟨B, hB, _, hiB⟩ := hS.bv_loc (inSeg u v v) hseg (isCompact_inSeg u v v)
  have hbBV : BoundedVariationOn (fun x => S.b x v) (Icc u v) :=
    ne_top_of_le_ne_top hB.ne ((hiB u v v Subset.rfl).2.2.2)
  have hFBV : BoundedVariationOn F (Icc u v) :=
    (hPAC.boundedVariationOn_Icc huv).mul_normed_algebra hbBV
  have hmaps : MapsTo (fun x : ℝ => -x) (Icc (-v) (-u)) (Icc u v) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hvar : eVariationOn (fun x => F (-x)) (Icc (-v) (-u)) =
      eVariationOn F (Icc u v) := by
    have himage : (fun x : ℝ => -x) '' Icc (-v) (-u) = Icc u v := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hmaps hy
      · intro hx
        exact ⟨-x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, neg_neg x⟩
    have h := eVariationOn.comp_eq_of_antitoneOn F (t := Icc (-v) (-u)) (fun x : ℝ => -x)
      (fun _ _ _ _ hxy => neg_le_neg hxy)
    simpa only [Function.comp_def, himage] using h
  have hFBV' : BoundedVariationOn (fun x => F (-x)) (Icc (-v) (-u)) := by
    change eVariationOn (fun x => F (-x)) (Icc (-v) (-u)) ≠ ⊤
    rw [hvar]
    exact hFBV
  have cn := continuousOn_in_section hS.cont_nu hseg
  have hi := outgoing_bv_hardy (u := -v) (v := -u)
    (lam := fun x => -S.nu (-x) v) (r := fun x => S.r (-x) v)
    (a := fun x => F (-x)) (phi := fun x => P (-x) * S.phi (-x) v)
    (by linarith)
    (cn.neg.comp continuous_neg.continuousOn hmaps)
    (fun x hx => (neg_pos.mpr (hS.nu_neg (-x, v)
      (hseg ⟨(hmaps hx).1, (hmaps hx).2, rfl⟩))).le)
    ((cP.mul cb).comp continuous_neg.continuousOn hmaps) hFBV'
    (fun x hx => ?_) (fun x hx => ?_)
  · have heq : ∀ x ∈ uIcc (-v) (-u),
        (-S.nu (-x) v) / S.r (-x) v * ‖F (-x) - P (-x) * S.phi (-x) v‖ =
        (-S.nu (-x) v) / S.r (-x) v * ‖S.xi (-x) v / S.nu (-x) v‖ := by
      intro x _
      dsimp only [F]
      rw [← mul_sub, norm_mul, hPnorm, one_mul]
      simp only [Fields.b, add_sub_cancel_left]
    have hi' := hi.1.congr (fun x hx => heq x (uIoc_subset_uIcc hx))
    have hInt : IntervalIntegrable (fun x => (-S.nu x v) / S.r x v *
        ‖S.xi x v / S.nu x v‖) volume u v :=
      (IntervalIntegrable.iff_comp_neg).mpr hi'.symm
    refine ⟨hInt, ?_⟩
    have hbound := (intervalIntegral.integral_congr heq).symm.trans_le hi.2
    rw [intervalIntegral.integral_comp_neg (f := fun x => (-S.nu x v) / S.r x v *
      ‖S.xi x v / S.nu x v‖), neg_neg, neg_neg, hvar] at hbound
    exact hbound
  · have hx' := hmaps hx
    have hs : inSeg (-x) v v ⊆ D := by
      rintro p ⟨hp₁, hp₂, rfl⟩
      exact hseg ⟨hx'.1.trans hp₁, hp₂, rfl⟩
    rw [intervalIntegral.integral_comp_neg (f := fun y => -S.nu y v), neg_neg]
    exact (incoming_radius_reconstruction hS hx'.2 hs).symm
  · have hx' : -x ∈ Icc u v := hmaps ⟨hx.1.le, hx.2⟩
    have hs : inSeg (-x) v v ⊆ D := by
      rintro p ⟨hp₁, hp₂, rfl⟩
      exact hseg ⟨hx'.1.trans hp₁, hp₂, rfl⟩
    have hr := incoming_parallel_reconstruction hS hx'.2 hs
      (show v ∈ Icc (-x) v from ⟨hx'.2, le_rfl⟩)
    simp_rw [Complex.ofReal_neg]
    rw [intervalIntegral.integral_comp_neg (f := fun y => (-S.nu y v : ℂ) * F y), neg_neg]
    simpa only [F, P, mul_assoc, Complex.ofReal_neg] using hr

end EmcsfAcExtension.Local.Broad
