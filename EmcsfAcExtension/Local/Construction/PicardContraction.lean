module

public import EmcsfAcExtension.Local.Construction.PicardBall
public import EmcsfAcExtension.Local.Defs.Picard

/-! # Banach's theorem on the Picard ball

Abstract wrappers around `ContractingWith.fixedPoint`. The Lipschitz constant
is an explicit nonnegative real number strictly smaller than one. These
conditional helpers do not assert contraction of the radial reconstruction
map, or close any graph node.
-/

public section

open Set Metric Function MeasureTheory
open scoped NNReal

namespace EmcsfAcExtension.Local

variable {c a L : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A self-map of a Picard ball with explicit Lipschitz constant `q < 1` is a
contraction. The constant is supplied before the map. -/
theorem picard_contractingWith_of_dist_le {q : ℝ≥0} (hq : q < 1)
    {datum : ℝ → E} {center : PicardCarrier c a L E} {ρ : ℝ}
    (F : PicardBall datum center ρ → PicardBall datum center ρ)
    (hF : ∀ x y, dist (F x) (F y) ≤ (q : ℝ) * dist x y) :
    ContractingWith q F :=
  ⟨hq, LipschitzWith.of_dist_le_mul hF⟩

/-- Incoming integration of a continuous value field on the wedge. Its total
integrand uses the continuous clamp; on every integration segment the clamp
fixes all arguments. -/
@[expose] noncomputable def picardIncomingComponent (ha : 0 ≤ a) (haL : a ≤ L)
    (f : C(PicardDomain c a L, E)) : C(PicardDomain c a L, E) where
  toFun p := ∫ s in c..p.1.1, f (picardClamp ha haL (s, p.1.2))
  continuous_toFun := by
    have hG : Continuous (fun q : ℝ × ℝ => f (picardClamp ha haL (q.2, q.1))) :=
      f.continuous.comp ((continuous_picardClamp ha haL).comp continuous_swap)
    have hp := intervalIntegral.continuous_parametric_primitive_of_continuous
      (μ := volume) (a₀ := c) (f := fun v s => f (picardClamp ha haL (s, v))) hG
    exact hp.comp (continuous_swap.comp continuous_subtype_val)
/-- Incoming integration gains the strip length `a` in sup distance.
The numerical constant one is universal, uniformly in `E,c,L` and both fields. -/
theorem picardIncomingComponent_dist_le (ha : 0 ≤ a) (haL : a ≤ L)
    (f g : C(PicardDomain c a L, E)) :
    dist (picardIncomingComponent ha haL f) (picardIncomingComponent ha haL g) ≤ a * dist f g := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro p
  have hf : IntervalIntegrable (fun s => f (picardClamp ha haL (s, p.1.2))) volume c p.1.1 :=
    (f.continuous.comp ((continuous_picardClamp ha haL).comp
      (continuous_id.prodMk continuous_const))).intervalIntegrable c p.1.1
  have hg : IntervalIntegrable (fun s => g (picardClamp ha haL (s, p.1.2))) volume c p.1.1 :=
    (g.continuous.comp ((continuous_picardClamp ha haL).comp
      (continuous_id.prodMk continuous_const))).intervalIntegrable c p.1.1
  change dist (∫ s in c..p.1.1, f (picardClamp ha haL (s, p.1.2)))
    (∫ s in c..p.1.1, g (picardClamp ha haL (s, p.1.2))) ≤ a * dist f g
  rw [dist_eq_norm, ← intervalIntegral.integral_sub hf hg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => f (picardClamp ha haL (s, p.1.2)) - g (picardClamp ha haL (s, p.1.2)))
    (a := c) (b := p.1.1) (fun s _ => by
      simpa only [dist_eq_norm] using
        (ContinuousMap.dist_apply_le_dist (f := f) (g := g) (picardClamp ha haL (s, p.1.2))))
  rw [abs_of_nonneg (sub_nonneg.mpr p.2.1.1)] at hb
  have hpUpper : p.1.1 ≤ c + a := p.2.2
  have hwidth : p.1.1 - c ≤ a := by linarith
  exact hb.trans (by simpa only [mul_comm, dist_eq_norm] using
    mul_le_mul_of_nonneg_left hwidth (show 0 ≤ dist f g from dist_nonneg))


variable [CompleteSpace E]


/-- Integrate values and outgoing jets in the incoming direction. FTC on the
outgoing sections and Fubini on the enclosed rectangle preserve compatibility;
no incoming derivative of the old candidate is needed. -/
@[expose] noncomputable def picardIncoming (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L E) : PicardCarrier c a L E := by
  refine ⟨(picardIncomingComponent ha haL z.1.1, picardIncomingComponent ha haL z.1.2), ?_⟩
  intro p
  let F : ℝ → ℝ → E := fun s t => z.1.1 (picardClamp ha haL (s, t))
  let dF : ℝ → ℝ → E := fun s t => z.1.2 (picardClamp ha haL (s, t))
  have hF : Continuous (Function.uncurry F) := z.1.1.continuous.comp (continuous_picardClamp ha haL)
  have hdF : Continuous (Function.uncurry dF) :=
    z.1.2.continuous.comp (continuous_picardClamp ha haL)
  have hClamp (q : PicardDomain c a L) (t : ℝ) (ht : t ∈ Icc q.1.1 (c + L)) :
      picardClamp ha haL (q.1.1, t) = picardSectionPoint q t := by
    rw [← picardSectionPoint_of_mem q ht]
    exact picardClamp_coe ha haL _
  have hsection (s : ℝ) (hs : s ∈ Icc c p.1.1) :
      (∫ t in p.1.1..p.1.2, dF s t) = F s p.1.2 - F s p.1.1 := by
    have hpUpper : p.1.1 ≤ c + a := p.2.2
    let q : PicardDomain c a L := ⟨(s, p.1.2),
      ⟨⟨hs.1, hs.2.trans p.2.1.2.1, p.2.1.2.2⟩, hs.2.trans hpUpper⟩⟩
    have hv : p.1.2 ∈ Icc q.1.1 (c + L) := ⟨hs.2.trans p.2.1.2.1, p.2.1.2.2⟩
    have hu : p.1.1 ∈ Icc q.1.1 (c + L) := ⟨hs.2, p.2.1.2.1.trans p.2.1.2.2⟩
    have hi : (∫ t in p.1.1..p.1.2, dF s t) =
        ∫ t in p.1.1..p.1.2, z.1.2 (picardSectionPoint q t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le p.2.1.2.1] at ht
      exact congrArg z.1.2 (hClamp q t ⟨hs.2.trans ht.1, ht.2.trans p.2.1.2.2⟩)
    rw [hi]
    change _ = z.1.1 (picardClamp ha haL (q.1.1, p.1.2)) -
      z.1.1 (picardClamp ha haL (q.1.1, p.1.1))
    rw [hClamp q p.1.2 hv, hClamp q p.1.1 hu]
    exact picardCarrier_integral_between z q hv hu
  have hDiff : (∫ s in c..p.1.1, F s p.1.2) - (∫ s in c..p.1.1, F s p.1.1) =
      ∫ s in c..p.1.1, ∫ t in p.1.1..p.1.2, dF s t := by
    have h₁ : IntervalIntegrable (fun s => F s p.1.2) volume c p.1.1 :=
      (hF.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have h₂ : IntervalIntegrable (fun s => F s p.1.1) volume c p.1.1 :=
      (hF.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub h₁ h₂]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le p.2.1.1] at hs
    exact (hsection s hs).symm
  have hCompact : IntegrableOn (Function.uncurry dF) (Icc c p.1.1 ×ˢ Icc p.1.1 p.1.2) volume :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hdF.continuousOn
  have hRect : IntegrableOn (Function.uncurry dF) (uIoc c p.1.1 ×ˢ uIoc p.1.1 p.1.2) volume := by
    apply hCompact.mono_set
    rw [uIoc_of_le p.2.1.1, uIoc_of_le p.2.1.2.1]
    exact Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hSwap := MeasureTheory.intervalIntegral_intervalIntegral_swap hRect
  have hNew : (∫ t in p.1.1..p.1.2,
      (picardIncomingComponent ha haL z.1.2) (picardSectionPoint p t)) =
      ∫ t in p.1.1..p.1.2, ∫ s in c..p.1.1, dF s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le p.2.1.2.1] at ht
    change (∫ s in c..p.1.1, dF s (picardSectionPoint p t).1.2) = _
    rw [picardSectionPoint_of_mem p ⟨ht.1, ht.2.trans p.2.1.2.2⟩]
  change (∫ s in c..p.1.1, F s p.1.2) =
    (∫ s in c..p.1.1, F s (picardSectionPoint p p.1.1).1.2) +
      ∫ t in p.1.1..p.1.2, (picardIncomingComponent ha haL z.1.2) (picardSectionPoint p t)
  rw [picardSectionPoint_of_mem p ⟨le_rfl, p.2.1.2.1.trans p.2.1.2.2⟩, hNew]
  exact (sub_eq_iff_eq_add').mp (hDiff.trans hSwap)

/-- Incoming integration is Lipschitz with explicit constant `a` on the
complete carrier. This constant is uniform in all candidates and `c,L`. -/
theorem picardIncoming_lipschitz (ha : 0 ≤ a) (haL : a ≤ L) :
    LipschitzWith ⟨a, ha⟩ (picardIncoming (c := c) ha haL (E := E)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change max (dist (picardIncomingComponent ha haL z.1.1) (picardIncomingComponent ha haL w.1.1))
    (dist (picardIncomingComponent ha haL z.1.2)
      (picardIncomingComponent ha haL w.1.2)) ≤ a * dist z w
  refine max_le ((picardIncomingComponent_dist_le ha haL _ _).trans ?_)
    ((picardIncomingComponent_dist_le ha haL _ _).trans ?_)
  · exact mul_le_mul_of_nonneg_left (le_max_left _ _) ha
  · exact mul_le_mul_of_nonneg_left (le_max_right _ _) ha

/-- Banach fixed point in the closed affine ball. This helper requires the
self-map and Lipschitz estimate, which the concrete Picard construction must
prove from its datum. No constants depend on hidden candidate choices. -/
theorem picard_existsUnique_fixedPoint_of_contracting {q : ℝ≥0} (hq : q < 1)
    {datum : ℝ → E} {center : PicardCarrier c a L E} {ρ : ℝ}
    (hc : center ∈ picardInitialSet datum) (hρ : 0 ≤ ρ)
    (F : PicardBall datum center ρ → PicardBall datum center ρ)
    (hF : ∀ x y, dist (F x) (F y) ≤ (q : ℝ) * dist x y) :
    ∃! z, F z = z := by
  have : Nonempty (PicardBall datum center ρ) := picardBall_nonempty hc hρ
  have hcontract := picard_contractingWith_of_dist_le hq F hF
  refine ⟨hcontract.fixedPoint F, hcontract.fixedPoint_isFixedPt, ?_⟩
  intro z hz
  exact hcontract.fixedPoint_unique hz

/-- Choose the positive time in internal project record (E4) from finite nonnegative update
and Lipschitz bounds. Time depends only on `T,ρ,K,C`; both numerical margins
are universal. No candidate or datum is used to choose it. -/
theorem picard_exists_pos_time (T ρ K C : ℝ) (hT : 0 < T) (hρ : 0 < ρ) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ a : ℝ, 0 < a ∧ a ≤ T ∧ a ≤ 1 ∧ a * K ≤ ρ / 2 ∧ a * C ≤ 1 / 2 := by
  have hKd : 0 < 2 * K + 2 := by positivity
  have hCd : 0 < 2 * C + 2 := by positivity
  let a := min T (min 1 (min (ρ / (2 * K + 2)) (1 / (2 * C + 2))))
  have ha : 0 < a := by dsimp [a]; positivity
  have haT : a ≤ T := min_le_left _ _
  have haRest := min_le_right T (min 1 (min (ρ / (2 * K + 2)) (1 / (2 * C + 2))))
  have haOne : a ≤ 1 := haRest.trans (min_le_left _ _)
  have haBoth : a ≤ min (ρ / (2 * K + 2)) (1 / (2 * C + 2)) :=
    haRest.trans (min_le_right _ _)
  have hAK := (le_div_iff₀ hKd).mp (haBoth.trans (min_le_left _ _))
  have hAC := (le_div_iff₀ hCd).mp (haBoth.trans (min_le_right _ _))
  ring_nf at hAK hAC
  refine ⟨a, ha, haT, haOne, ?_, ?_⟩ <;> linarith

namespace Recon

variable (e : ℝ) (lam : ℝ → ℝ → ℝ) (hh : ℝ → ℝ → ℂ)

/-- On the starting cone, the incoming expansion update equals its datum. -/
@[simp] theorem picardLam_initial (c : ℝ) (lam₀ : ℝ → ℝ) (v : ℝ) :
    picardLam e lam hh c lam₀ c v = lam₀ v := by
  simp [picardLam]

/-- On the starting cone, the scalar update equals its datum. -/
@[simp] theorem picardH_initial (c : ℝ) (h₀ : ℝ → ℂ) (v : ℝ) :
    picardH e lam hh c h₀ c v = h₀ v := by
  simp [picardH]

end Recon

/-- Exact incoming update of the carrier values on a cone based at `c`.
This uses the audited `Recon.picardLam` and `Recon.picardH` definitions. To obtain
a carrier self-map one must still prove continuous outgoing jets and ball bounds. -/
@[expose] noncomputable def picardUpdate (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ) (z : PicardCarrier c a L (ℝ × ℂ))
    (u v : ℝ) : ℝ × ℂ :=
  (Recon.picardLam e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) c lam₀ u v,
    Recon.picardH e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) c h₀ u v)

/-- The carrier update fixes the prescribed later-cone values exactly. -/
@[simp] theorem picardUpdate_initial (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ) (z : PicardCarrier c a L (ℝ × ℂ)) (v : ℝ) :
    picardUpdate ha haL e lam₀ h₀ z c v = (lam₀ v, h₀ v) := by
  simp [picardUpdate]

end EmcsfAcExtension.Local
