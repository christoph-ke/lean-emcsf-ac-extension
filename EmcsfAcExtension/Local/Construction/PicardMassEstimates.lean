module

public import EmcsfAcExtension.Local.Construction.PicardMass
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Quantitative normalized mass estimates

Nonnegative damping gives uniform second-moment bounds and difference estimates
without exponential growth. The mass coefficient bounds use normalized scalar
and charge bounds. Further candidate Lipschitz estimates and the downstream
radial coefficients remain open; this module closes no graph node.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- The continuous normalized damped second moment. This is the mass
integrating-factor operator before substituting the radial coefficient maps. -/
@[expose] noncomputable def picardDampedMoment
    (f k : C(PicardDomain c a L, ℝ)) : C(PicardDomain c a L, ℝ) where
  toFun p := ∫ t in (0 : ℝ)..1, t ^ 2 * k (picardRadialPoint p t) *
    Real.exp (-(p.1.2 - p.1.1) * picardRadialTail f (p, t))
  continuous_toFun := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact ((continuous_snd.pow 2).mul (k.continuous.comp continuous_picardRadialPoint)).mul
      (Real.continuous_exp.comp ((((continuous_snd.comp continuous_subtype_val).sub
        (continuous_fst.comp continuous_subtype_val)).comp continuous_fst).neg.mul
          (picardRadialTail f).continuous))

private theorem picard_damping_nonpos_aux (f : C(PicardDomain c a L, ℝ))
    (hf : ∀ q, 0 ≤ f q) (p : PicardDomain c a L) {t : ℝ} (ht : t ≤ 1) :
    -(p.1.2 - p.1.1) * picardRadialTail f (p, t) ≤ 0 := by
  have htail : 0 ≤ picardRadialTail f (p, t) :=
    intervalIntegral.integral_nonneg ht (fun _ _ => hf _)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr p.2.1.2.1)) htail

private theorem picard_damping_norm_aux (f : C(PicardDomain c a L, ℝ))
    (hf : ∀ q, 0 ≤ f q) (p : PicardDomain c a L) {t : ℝ} (ht : t ≤ 1) :
    |Real.exp (-(p.1.2 - p.1.1) * picardRadialTail f (p, t))| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact (Real.exp_le_exp.mpr (picard_damping_nonpos_aux f hf p ht)).trans_eq Real.exp_zero

/-- Nonnegative damping has operator norm at most one on the radial forcing,
with universal numerical constant one, uniformly in the wedge and damping. -/
theorem picardDampedMoment_norm_le (f k : C(PicardDomain c a L, ℝ)) (hf : ∀ q, 0 ≤ f q) :
    ‖picardDampedMoment f k‖ ≤ ‖k‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg k)).mpr
  intro p
  change ‖∫ t in (0 : ℝ)..1, t ^ 2 * k (picardRadialPoint p t) *
    Real.exp (-(p.1.2 - p.1.1) * picardRadialTail f (p, t))‖ ≤ _
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := ‖k‖)
    (f := fun t => t ^ 2 * k (picardRadialPoint p t) * Real.exp (-(p.1.2 - p.1.1) * picardRadialTail
        f (p, t))) (by
      intro t ht
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ht.1.le]
      have h1 : t ^ 2 ≤ 1 := pow_le_one₀ ht.1.le ht.2
      have hk : |k (picardRadialPoint p t)| ≤ ‖k‖ := k.norm_coe_le_norm _
      exact (mul_le_mul (mul_le_mul h1 hk (abs_nonneg _) zero_le_one)
        (picard_damping_norm_aux f hf p ht.2) (abs_nonneg _) (by positivity)).trans_eq (by ring))
  simpa using hb

private theorem picard_damping_dist_aux (hL : 0 ≤ L)
    (f g : C(PicardDomain c a L, ℝ)) (hf : ∀ q, 0 ≤ f q) (hg : ∀ q, 0 ≤ g q)
    (p : PicardDomain c a L) {t : ℝ} (ht : t ∈ Icc 0 1) :
    |Real.exp (-(p.1.2 - p.1.1) * picardRadialTail f (p, t)) -
      Real.exp (-(p.1.2 - p.1.1) * picardRadialTail g (p, t))| ≤ L * dist f g := by
  have h := (LipschitzOnWith.exp_on_Iic 0).dist_le_mul _
    (picard_damping_nonpos_aux f hf p ht.2) _ (picard_damping_nonpos_aux g hg p ht.2)
  change dist (Real.exp (-(p.1.2 - p.1.1) * picardRadialTail f (p, t)))
    (Real.exp (-(p.1.2 - p.1.1) * picardRadialTail g (p, t))) ≤
      Real.exp 0 * dist (-(p.1.2 - p.1.1) * picardRadialTail f (p, t))
        (-(p.1.2 - p.1.1) * picardRadialTail g (p, t)) at h
  simp only [Real.exp_zero, one_mul, Real.dist_eq, ←mul_sub, abs_mul,
    abs_neg, abs_of_nonneg (sub_nonneg.mpr p.2.1.2.1)] at h
  have htD : |picardRadialTail f (p, t) - picardRadialTail g (p, t)| ≤ dist f g := by
    have hn := picardRadialTail_norm_le (f - g)
      (fun q =>
          by simpa only [ContinuousMap.sub_apply, dist_eq_norm] using
               ContinuousMap.dist_apply_le_dist (f := f) (g := g) q) p ht.2
    rw [picardRadialTail_sub] at hn
    have hn0 : |picardRadialTail f (p, t) - picardRadialTail g (p, t)| ≤ dist f g * (1 - t) := by
      rw [dist_eq_norm]
      simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using hn
    exact hn0.trans
        (by have h0 : 0 ≤ dist f g * t := mul_nonneg dist_nonneg ht.1; linarith only [h0])
  have hx : p.1.2 - p.1.1 ≤ L := by linarith [p.2.1.1, p.2.1.2.2]
  exact h.trans (mul_le_mul hx htD (abs_nonneg _) hL)

/-- The normalized damped moment has the displayed local Lipschitz bound,
uniformly in `c,a` and all fields. The only constants are cone length `L`
and the forcing size `norm(k')`; nonnegative damping avoids exponential growth. -/
theorem picardDampedMoment_dist_le (hL : 0 ≤ L)
    (f g k k' : C(PicardDomain c a L, ℝ)) (hf : ∀ q, 0 ≤ f q) (hg : ∀ q, 0 ≤ g q) :
    dist (picardDampedMoment f k) (picardDampedMoment g k') ≤ dist k k' + L * ‖k'‖ * dist f g := by
  have hC : 0 ≤ dist k k' + L * ‖k'‖ * dist f g := by positivity
  apply (ContinuousMap.dist_le hC).mpr
  intro p
  let F : ℝ → ℝ := fun t => t ^ 2 * k (picardRadialPoint p t) *
    Real.exp (-(p.1.2 - p.1.1) * picardRadialTail f (p, t))
  let G : ℝ → ℝ := fun t => t ^ 2 * k' (picardRadialPoint p t) *
    Real.exp (-(p.1.2 - p.1.1) * picardRadialTail g (p, t))
  have hc (f k : C(PicardDomain c a L, ℝ)) : Continuous (fun t : ℝ => t ^ 2 * k (picardRadialPoint p
      t) *
      Real.exp (-(p.1.2 - p.1.1) * picardRadialTail f (p, t))) :=
    ((continuous_id.pow 2).mul (k.continuous.comp
      (continuous_picardRadialPoint.comp (continuous_const.prodMk continuous_id)))).mul
        (Real.continuous_exp.comp (continuous_const.mul
          ((picardRadialTail f).continuous.comp (continuous_const.prodMk continuous_id))))
  change ‖(∫ t in (0 : ℝ)..1, F t) - (∫ t in (0 : ℝ)..1, G t)‖ ≤ _
  rw [←intervalIntegral.integral_sub ((hc f k).intervalIntegrable 0 1) ((hc g k').intervalIntegrable
      0 1)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := dist k k' + L * ‖k'‖ * dist f g) (f := fun t => F t - G t) (by
      intro t ht
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      let X := Real.exp (-(p.1.2 - p.1.1) * picardRadialTail f (p, t))
      let Y := Real.exp (-(p.1.2 - p.1.1) * picardRadialTail g (p, t))
      have hx : |X| ≤ 1 := picard_damping_norm_aux f hf p ht.2
      have hxy : |X - Y| ≤ L * dist f g := picard_damping_dist_aux hL f g hf hg p ⟨ht.1.le, ht.2⟩
      have hk : |k (picardRadialPoint p t) - k' (picardRadialPoint p t)| ≤ dist k k' :=
        by simpa only [Real.dist_eq] using ContinuousMap.dist_apply_le_dist (f := k) (g := k')
             (picardRadialPoint p t)
      have hk' : |k' (picardRadialPoint p t)| ≤ ‖k'‖ := k'.norm_coe_le_norm _
      have heq : F t - G t = t ^ 2 * ((k (picardRadialPoint p t) - k' (picardRadialPoint p t)) * X +
          k' (picardRadialPoint p t) * (X - Y)) := by dsimp [F, G, X, Y];ring
      rw [heq, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ht.1.le]
      refine (mul_le_mul (pow_le_one₀ ht.1.le ht.2) ?_ (abs_nonneg _) zero_le_one).trans_eq (one_mul
          _)
      calc
        _ ≤ |(k (picardRadialPoint p t) - k' (picardRadialPoint p t)) * X| +
            |k' (picardRadialPoint p t) * (X - Y)| := abs_add_le _ _
        _ ≤ dist k k' + ‖k'‖ * (L * dist f g) := by
          rw [abs_mul, abs_mul]
          have h1 := mul_le_mul hk hx (abs_nonneg _) (dist_nonneg : 0 ≤ dist k k')
          simpa only [mul_one] using add_le_add h1
            (mul_le_mul hk' hxy (abs_nonneg _) (norm_nonneg _))
        _ = _ := by ring)
  simpa [F, G] using hb

/-- Positive candidate expansion makes the mass integrating-factor coefficient
nonnegative everywhere, including the axis. No Hawking gap is required. -/
theorem picardMassAm_nonneg (ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) : 0 ≤ picardMassAm ell he z hl p := by
  have hx : 0 ≤ p.1.2 - p.1.1 := sub_nonneg.mpr p.2.1.2.1
  have hla : 0 ≤ (z.1.1 p).1 := (he.trans_le (hl p)).le
  have hR : 0 < picardRadialAverage (picardLamValues z) p :=
    he.trans_le (picardRadialAverage_lower _ hl p)
  change 0 ≤ (p.1.2 - p.1.1) * (z.1.1 p).1 * ‖picardScalarRemainder ell he z hl p‖ ^ 2 /
    picardRadialAverage (picardLamValues z) p
  exact div_nonneg (mul_nonneg (mul_nonneg hx hla) (sq_nonneg _)) hR.le

/-- The normalized mass is exactly the damped second-moment operator. -/
theorem picardMassRemainder_eq_dampedMoment (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    picardMassRemainder e ell he z hl =
      picardDampedMoment (picardMassAm ell he z hl) (picardMassKernel e ell he z hl) := rfl

/-- The normalized mass is bounded by its normalized forcing kernel, with
universal constant one and no inverse-gap hypothesis. -/
theorem picardMassRemainder_norm_le_kernel (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    ‖picardMassRemainder e ell he z hl‖ ≤ ‖picardMassKernel e ell he z hl‖ := by
  rw [picardMassRemainder_eq_dampedMoment]
  exact picardDampedMoment_norm_le _ _ (picardMassAm_nonneg ell he z hl)

/-- The normalized mass difference is controlled by forcing and damping
coefficient differences. The displayed constants are `L` and the second
forcing norm, uniformly in cone position and strip width. To obtain the full
radial node, the two coefficient maps must still receive uniform bounds. -/
theorem picardMassRemainder_dist_le_coefficients (hL : 0 ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z w : PicardCarrier c a L (ℝ × ℂ))
    (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1) :
    dist (picardMassRemainder e ell he z hlz) (picardMassRemainder e ell he w hlw) ≤
      dist (picardMassKernel e ell he z hlz) (picardMassKernel e ell he w hlw) +
      L * ‖picardMassKernel e ell he w hlw‖ * dist (picardMassAm ell he z hlz) (picardMassAm ell he
          w hlw) := by
  rw [picardMassRemainder_eq_dampedMoment, picardMassRemainder_eq_dampedMoment]
  exact picardDampedMoment_dist_le hL _ _ _ _
    (picardMassAm_nonneg ell he z hlz) (picardMassAm_nonneg ell he w hlw)

/-- The mass damping coefficient has the displayed uniform bound depending
only on `ell,U,F,L`, when the normalized scalar remainder is bounded by `F`.
These parameters precede the candidate; no inverse-gap bound is required. -/
theorem picardMassAm_norm_le (ell U F : ℝ) (he : 0 < ell)
    (hU : 0 ≤ U) (hF : 0 ≤ F) (hL : 0 ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hu : ∀ q, (z.1.1 q).1 ≤ U) (hf : ‖picardScalarRemainder ell he z hl‖ ≤ F) :
    ‖picardMassAm ell he z hl‖ ≤ L * U * F ^ 2 / ell := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (picardMassAm_nonneg ell he z hl p)]
  have hx : 0 ≤ p.1.2 - p.1.1 := sub_nonneg.mpr p.2.1.2.1
  have hxL : p.1.2 - p.1.1 ≤ L := by linarith [p.2.1.1, p.2.1.2.2]
  have hla : 0 ≤ (z.1.1 p).1 := (he.trans_le (hl p)).le
  have hs : ‖picardScalarRemainder ell he z hl p‖ ^ 2 ≤ F ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hF).mpr (((picardScalarRemainder ell he z hl).norm_coe_le_norm
        p).trans hf)
  have hR : ell ≤ picardRadialAverage (picardLamValues z) p := picardRadialAverage_lower _ hl p
  change (p.1.2 - p.1.1) * (z.1.1 p).1 * ‖picardScalarRemainder ell he z hl p‖ ^ 2 /
    picardRadialAverage (picardLamValues z) p ≤ _
  exact (div_le_div_of_nonneg_left (by positivity) he hR).trans
    (div_le_div_of_nonneg_right (mul_le_mul (mul_le_mul hxL (hu p) hla hL) hs
      (sq_nonneg _) (mul_nonneg hL hU)) he.le)

/-- The normalized mass forcing has the displayed uniform bound depending only
on `ell,U,F,Q,L`, when normalized scalar and charge remainders have bounds `F,Q`.
All parameters precede the candidate, uniformly in cone position and strip width. -/
theorem picardMassKernel_norm_le (ell U F Q e : ℝ) (he : 0 < ell)
    (hU : 0 ≤ U) (hF : 0 ≤ F) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hu : ∀ q, (z.1.1 q).1 ≤ U) (hf : ‖picardScalarRemainder ell he z hl‖ ≤ F)
    (hq : ‖picardChargeRemainder e ell he z hl‖ ≤ Q) :
    ‖picardMassKernel e ell he z hl‖ ≤ U / 2 * (F ^ 2 + L ^ 2 * Q ^ 2 / ell ^ 2) := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  have hx : 0 ≤ p.1.2 - p.1.1 := sub_nonneg.mpr p.2.1.2.1
  have hxL : p.1.2 - p.1.1 ≤ L := by linarith [p.2.1.1, p.2.1.2.2]
  have hla : 0 ≤ (z.1.1 p).1 := (he.trans_le (hl p)).le
  have hs : ‖picardScalarRemainder ell he z hl p‖ ^ 2 ≤ F ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hF).mpr (((picardScalarRemainder ell he z hl).norm_coe_le_norm
        p).trans hf)
  have hq' : (picardChargeRemainder e ell he z hl p) ^ 2 ≤ Q ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hQ).mpr
      (((picardChargeRemainder e ell he z hl).norm_coe_le_norm p).trans hq)
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hR : ell ≤ picardRadialAverage (picardLamValues z) p := picardRadialAverage_lower _ hl p
  have hR2 : ell ^ 2 ≤ (picardRadialAverage (picardLamValues z) p) ^ 2 :=
    (sq_le_sq₀ he.le (he.trans_le hR).le).mpr hR
  have hn : (p.1.2 - p.1.1) ^ 2 * (picardChargeRemainder e ell he z hl p) ^ 2 /
      (picardRadialAverage (picardLamValues z) p) ^ 2 ≤ L ^ 2 * Q ^ 2 / ell ^ 2 :=
    (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos he) hR2).trans
      (div_le_div_of_nonneg_right (mul_le_mul ((sq_le_sq₀ hx hL).mpr hxL) hq'
        (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
  have hkn : 0 ≤ picardMassKernel e ell he z hl p := by
    change 0 ≤ ((z.1.1 p).1 / 2) * (‖picardScalarRemainder ell he z hl p‖ ^ 2 +
      (p.1.2 - p.1.1) ^ 2 * (picardChargeRemainder e ell he z hl p) ^ 2 /
        (picardRadialAverage (picardLamValues z) p) ^ 2)
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hkn]
  change ((z.1.1 p).1 / 2) * (‖picardScalarRemainder ell he z hl p‖ ^ 2 +
    (p.1.2 - p.1.1) ^ 2 * (picardChargeRemainder e ell he z hl p) ^ 2 /
      (picardRadialAverage (picardLamValues z) p) ^ 2) ≤ _
  exact mul_le_mul (div_le_div_of_nonneg_right (hu p) (by norm_num)) (add_le_add hs hn)
    (by positivity) (div_nonneg hU (by norm_num))

/-- The complete mass carrier difference is bounded by its normalized damping
and forcing coefficient differences. The displayed constants depend only on
`L`, the first damping norm and the second forcing norm, uniformly in `c,a`.
This preserves both vanishing orders and requires no candidate second derivative. -/
theorem picardMassRecon_dist_le_coefficients (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell : ℝ) (he : 0 < ell) (z w : PicardCarrier c a L (ℝ × ℂ))
    (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1) :
    let α := dist (picardMassAm ell he z hlz) (picardMassAm ell he w hlw)
    let β := dist (picardMassKernel e ell he z hlz) (picardMassKernel e ell he w hlw)
    let A := ‖picardMassAm ell he z hlz‖
    let K := ‖picardMassKernel e ell he w hlw‖
    dist (picardMassRecon ha haL e ell he z hlz) (picardMassRecon ha haL e ell he w hlw) ≤
      (L ^ 3 + L ^ 3 * A) * (β + L * K * α) + L ^ 2 * β + L ^ 3 * K * α := by
  let am := picardMassAm ell he z hlz
  let an := picardMassAm ell he w hlw
  let bm := picardMassKernel e ell he z hlz
  let bn := picardMassKernel e ell he w hlw
  let α := dist am an
  let β := dist bm bn
  let A := ‖am‖
  let K := ‖bn‖
  let D := β + L * K * α
  have hL : 0 ≤ L := ha.trans haL
  have hα : 0 ≤ α := dist_nonneg
  have hβ : 0 ≤ β := dist_nonneg
  have hA : 0 ≤ A := norm_nonneg _
  have hK : 0 ≤ K := norm_nonneg _
  have hD : 0 ≤ D := by dsimp [D];positivity
  have hx (p : PicardDomain c a L) : 0 ≤ p.1.2 - p.1.1 := sub_nonneg.mpr p.2.1.2.1
  have hxL (p : PicardDomain c a L) : p.1.2 - p.1.1 ≤ L := by linarith [p.2.1.1, p.2.1.2.2]
  let M := picardMassRecon ha haL e ell he z hlz
  let N := picardMassRecon ha haL e ell he w hlw
  have hV (p : PicardDomain c a L) : |M.1.1 p - N.1.1 p| ≤ L ^ 3 * D := by
    rw [picardMassRecon_normalized, picardMassRecon_normalized, ←mul_sub, abs_mul,
      abs_pow, abs_of_nonneg (hx p)]
    have hd : |picardMassRemainder e ell he z hlz p - picardMassRemainder e ell he w hlw p| ≤ D :=
      by simpa only [Real.dist_eq] using (ContinuousMap.dist_apply_le_dist (f := picardMassRemainder
           e ell he z hlz)
        (g := picardMassRemainder e ell he w hlw) p).trans
          (picardMassRemainder_dist_le_coefficients hL e ell he z w hlz hlw)
    exact mul_le_mul (pow_le_pow_left₀ (hx p) (hxL p) 3) hd (abs_nonneg _) (pow_nonneg hL 3)
  have hN (p : PicardDomain c a L) : |N.1.1 p| ≤ L ^ 3 * K := by
    rw [picardMassRecon_normalized, abs_mul, abs_pow, abs_of_nonneg (hx p)]
    have hdM0 : |picardMassRemainder e ell he w hlw p| ≤ K := by
      have hh := ((picardMassRemainder e ell he w hlw).norm_coe_le_norm p).trans
        (picardMassRemainder_norm_le_kernel e ell he w hlw)
      simpa only [Real.norm_eq_abs] using hh
    exact mul_le_mul (pow_le_pow_left₀ (hx p) (hxL p) 3) hdM0 (abs_nonneg _) (pow_nonneg hL 3)
  have hC : 0 ≤ (L ^ 3 + L ^ 3 * A) * D + L ^ 2 * β + L ^ 3 * K * α := by positivity
  change max (dist M.1.1 N.1.1) (dist M.1.2 N.1.2) ≤ _
  apply max_le
  · apply (ContinuousMap.dist_le hC).mpr
    intro p
    change |M.1.1 p - N.1.1 p| ≤ _
    have h1 : 0 ≤ L ^ 3 * A * D := by positivity
    have h2 : 0 ≤ L ^ 2 * β := by positivity
    have h3 : 0 ≤ L ^ 3 * K * α := by positivity
    exact (hV p).trans (by linarith only [h1, h2, h3])
  · apply (ContinuousMap.dist_le hC).mpr
    intro p
    change |M.1.2 p - N.1.2 p| ≤ _
    rw [picardMassRecon_jet, picardMassRecon_jet]
    have hB : |picardMassBm e ell he z hlz p - picardMassBm e ell he w hlw p| ≤ L ^ 2 * β := by
      change |(p.1.2 - p.1.1) ^ 2 * bm p - (p.1.2 - p.1.1) ^ 2 * bn p| ≤ _
      rw [←mul_sub, abs_mul, abs_pow, abs_of_nonneg (hx p)]
      exact mul_le_mul (pow_le_pow_left₀ (hx p) (hxL p) 2)
        (by simpa only [Real.dist_eq] using ContinuousMap.dist_apply_le_dist (f := bm) (g := bn) p)
            (abs_nonneg _) (sq_nonneg L)
    have hAm : |am p| ≤ A := by simpa only [Real.norm_eq_abs] using am.norm_coe_le_norm p
    have hdAm : |am p - an p| ≤ α :=
        by simpa only [Real.dist_eq] using ContinuousMap.dist_apply_le_dist (f := am) (g := an) p
    have heq : picardMassBm e ell he z hlz p - am p * M.1.1 p -
        (picardMassBm e ell he w hlw p - an p * N.1.1 p) =
        (picardMassBm e ell he z hlz p - picardMassBm e ell he w hlw p) -
          (am p * (M.1.1 p - N.1.1 p) + (am p - an p) * N.1.1 p) := by ring
    change |picardMassBm e ell he z hlz p - am p * M.1.1 p -
      (picardMassBm e ell he w hlw p - an p * N.1.1 p)| ≤ _
    rw [heq]
    calc
      _ ≤ |picardMassBm e ell he z hlz p - picardMassBm e ell he w hlw p| +
          |am p * (M.1.1 p - N.1.1 p) + (am p - an p) * N.1.1 p| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le
          (picardMassBm e ell he z hlz p - picardMassBm e ell he w hlw p)
          (am p * (M.1.1 p - N.1.1 p) + (am p - an p) * N.1.1 p)
      _ ≤ L ^ 2 * β + (A * (L ^ 3 * D) + α * (L ^ 3 * K)) := by
        apply add_le_add hB
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul hAm (hV p) (abs_nonneg _) hA)
          (mul_le_mul hdAm (hN p) (abs_nonneg _) hα)
      _ ≤ _ := by
        have h0 : 0 ≤ L ^ 3 * D := by positivity
        linarith only [h0]

end EmcsfAcExtension.Local
