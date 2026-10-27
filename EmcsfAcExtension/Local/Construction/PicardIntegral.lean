module

public import EmcsfAcExtension.Local.Construction.PicardCarrier

/-! # Outgoing primitives and weighted radial moments

Continuous outgoing sources define compatible value/jet carriers. The moment
identity factors powers of the distance to the axis before taking derivatives.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The outgoing primitive of a continuous field, using its clamped representative. -/
@[expose] noncomputable def picardOutgoingComponent (ha : 0 ≤ a) (haL : a ≤ L)
    (f : C(PicardDomain c a L, E)) : C(PicardDomain c a L, E) where
  toFun p := ∫ s in p.1.1..p.1.2, f (picardClamp ha haL (p.1.1, s))
  continuous_toFun := by
    let F : PicardDomain c a L → ℝ → E := fun p s => f (picardClamp ha haL (p.1.1, s))
    have hF : Continuous (Function.uncurry F) := f.continuous.comp
      ((continuous_picardClamp ha haL).comp
        ((continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd))
    have hPrim := intervalIntegral.continuous_parametric_primitive_of_continuous
      (μ := volume) (a₀ := 0) hF
    have hUpper := hPrim.comp (continuous_id.prodMk (continuous_snd.comp continuous_subtype_val))
    have hLower := hPrim.comp (continuous_id.prodMk (continuous_fst.comp continuous_subtype_val))
    convert hUpper.sub hLower using 1
    funext p
    have hc : Continuous (F p) := hF.comp (continuous_const.prodMk continuous_id)
    exact (intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable (μ := volume) 0 p.1.2)
      (hc.intervalIntegrable (μ := volume) 0 p.1.1)).symm
/-- An outgoing primitive with its continuous first jet and zero axis values. -/
@[expose] noncomputable def picardOutgoing [CompleteSpace E] (ha : 0 ≤ a) (haL : a ≤ L)
    (f : C(PicardDomain c a L, E)) : PicardCarrier c a L E :=
  picardCarrierOfRawDeriv (fun u v => ∫ s in u..v, f (picardClamp ha haL (u, s)))
    (picardOutgoingComponent ha haL f) f (fun _ => rfl) (by
      intro p _ _
      have hc : Continuous (fun s => f (picardClamp ha haL (p.1.1, s))) :=
        f.continuous.comp ((continuous_picardClamp ha haL).comp
          (continuous_const.prodMk continuous_id))
      have hd := (hc.integral_hasStrictDerivAt p.1.1 p.1.2).hasDerivAt
      convert hd using 1
      exact congrArg f (picardClamp_coe ha haL p).symm)

/-- A radial average with the nonnegative weight `t^n` on the normalized interval. -/
@[expose] noncomputable def picardRadialMoment (n : ℕ) (f : C(PicardDomain c a L, E)) :
    C(PicardDomain c a L, E) where
  toFun p := ∫ t in (0 : ℝ)..1, t ^ n • f (picardRadialPoint p t)
  continuous_toFun := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (continuous_snd.pow n).smul (f.continuous.comp continuous_picardRadialPoint)

/-- Weighted radial averaging has Lipschitz constant at most one, universally
in the domain geometry, target space, and moment order. -/
theorem picardRadialMoment_dist_le (n : ℕ) (f g : C(PicardDomain c a L, E)) :
    dist (picardRadialMoment n f) (picardRadialMoment n g) ≤ dist f g := by
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro p
  have hc (f : C(PicardDomain c a L, E)) : Continuous
      (fun t : ℝ => t ^ n • f (picardRadialPoint p t)) :=
    (continuous_id.pow n).smul (f.continuous.comp
      (continuous_picardRadialPoint.comp (continuous_const.prodMk continuous_id)))
  rw [dist_eq_norm]
  change ‖(∫ t in (0 : ℝ)..1, t ^ n • f (picardRadialPoint p t)) -
    (∫ t in (0 : ℝ)..1, t ^ n • g (picardRadialPoint p t))‖ ≤ dist f g
  rw [← intervalIntegral.integral_sub ((hc f).intervalIntegrable 0 1)
    ((hc g).intervalIntegrable 0 1)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := dist f g) (f := fun t => t ^ n • f (picardRadialPoint p t) - t ^ n • g (picardRadialPoint
        p t))
    (by
      intro t ht
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1.le n)]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ht.1.le ht.2) (norm_nonneg _)).trans
        (by simpa only [one_mul, ← dist_eq_norm] using
          (ContinuousMap.dist_apply_le_dist (picardRadialPoint p t) :
            dist (f (picardRadialPoint p t)) (g (picardRadialPoint p t)) ≤ dist f g)))
  simpa using hb

/-- Exact rescaling of an outgoing primitive with a vanishing power.
This identity includes the zero-width axis without cancellation. -/
theorem picardOutgoing_moment (ha : 0 ≤ a) (haL : a ≤ L) (n : ℕ)
    (f : C(PicardDomain c a L, E)) (p : PicardDomain c a L) :
    (∫ s in p.1.1..p.1.2, (s - p.1.1) ^ n • f (picardClamp ha haL (p.1.1, s))) =
      (p.1.2 - p.1.1) ^ (n + 1) • picardRadialMoment n f p := by
  let x := p.1.2 - p.1.1
  have hScaled := intervalIntegral.smul_integral_comp_mul_add
    (f := fun s => (s - p.1.1) ^ n • f (picardClamp ha haL (p.1.1, s)))
    (a := 0) (b := 1) x p.1.1
  have he : x * 1 + p.1.1 = p.1.2 := by dsimp [x]; ring
  simp only [mul_zero, zero_add] at hScaled
  rw [he] at hScaled
  rw [← hScaled]
  change x • (∫ t in (0 : ℝ)..1, (x * t + p.1.1 - p.1.1) ^ n •
    f (picardClamp ha haL (p.1.1, x * t + p.1.1))) = x ^ (n + 1) •
      ∫ t in (0 : ℝ)..1, t ^ n • f (picardRadialPoint p t)
  rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  have hClamp : picardClamp ha haL (p.1.1, x * t + p.1.1) = picardRadialPoint p t := by
    have hq := picardClamp_coe ha haL (picardRadialPoint p t)
    simpa only [picardRadialPoint_of_mem p ht, x, add_comm, mul_comm] using hq
  dsimp only
  rw [hClamp]
  have hc : x * (x * t + p.1.1 - p.1.1) ^ n = x ^ (n + 1) * t ^ n := by
    rw [add_sub_cancel_right, mul_pow, pow_succ]; ring
  simpa only [smul_smul] using congrArg (fun r : ℝ => r • f (picardRadialPoint p t)) hc

end EmcsfAcExtension.Local
