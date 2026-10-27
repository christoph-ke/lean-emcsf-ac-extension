module

public import EmcsfAcExtension.Local.Construction.PicardUniformBasic
public import EmcsfAcExtension.Local.Construction.PicardUniformQuotients
public import EmcsfAcExtension.Local.Construction.PicardUniformCoefficients

/-! # Complete radial C1 bounds and local Lipschitz comparison

The finite families below list the literal compatible reconstruction carriers.
Their metric is the maximum of the value and outgoing first-jet sup norms.
The final estimate sums all those complete carrier sizes and differences.
-/

public section

open scoped BigOperators

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- The real radial reconstruction family, in order:
`r,Q,m,mu,q,z,nu,B,C_A,G,A,(1-mu)⁻¹`. -/
@[expose] noncomputable def picardRadialRealCarriers (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q) : Fin 12 → PicardCarrier c a L ℝ :=
  ![picardRadiusRecon ha haL z, picardChargeRecon ha haL e ell he z hl,
    picardMassRecon ha haL e ell he z hl, picardMuRecon ha haL e ell he z hl,
    picardQSquareRecon ha haL e ell he z hl, picardZRecon ha haL e ell κ he hκ z hl hg,
    picardNuRecon ha haL e ell κ he hκ z hl hg, picardBRecon ha haL e ell κ he hκ z hl hg,
    picardCARecon ha haL e ell κ he hκ z hl hg, picardGRecon ha haL e ell κ he hκ z hl hg,
    picardARecon ha haL e ell κ he hκ z hl hg, picardGapInv ha haL e ell κ he hκ z hl hg]

/-- The complex radial reconstruction family, in order:
`phi,h-phi,W,P,-ie*A*h+P`. -/
@[expose] noncomputable def picardRadialComplexCarriers (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q) : Fin 5 → PicardCarrier c a L ℂ :=
  ![picardScalarRecon ha haL ell he z hl, picardScalarDifferenceRecon ha haL ell he z hl,
    picardWRecon ha haL e ell κ he hκ z hl hg, picardPRecon ha haL e ell κ he hκ z hl hg,
    picardOrdinarySourceRecon ha haL e ell κ he hκ z hl hg]

private theorem picard_enlarge_carrier_bounds_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {C K Δ : ℝ} (hCK : C ≤ K) (hΔ : 0 ≤ Δ)
    {F G : PicardCarrier c a L E}
    (h : picardCarrierSize F ≤ C ∧ dist F G ≤ C * Δ) :
    picardCarrierSize F ≤ K ∧ dist F G ≤ K * Δ :=
  ⟨h.1.trans hCK, h.2.trans (mul_le_mul_of_nonneg_right hCK hΔ)⟩

/-- Uniform complete radial reconstruction estimates in the maximum carrier
norm. The positive constant depends only on `ell,B,R,κ,|e|`, before cone
position, incoming width and every actual cone length at most `R`.
Every real and complex reconstruction and coefficient is included in the sums. -/
theorem picard_radial_carriers_uniform (ell B R κ e : ℝ) (he : 0 < ell)
    (hκ : 0 < κ) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
        (hgz : ∀ q, κ ≤ 1 - picardMuValues e ell he z hlz q)
        (hgw : ∀ q, κ ≤ 1 - picardMuValues e ell he w hlw q),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      (∑ i, picardCarrierSize (picardRadialRealCarriers ha haL e ell κ he hκ z hlz hgz i)) +
        (∑ i, picardCarrierSize (picardRadialComplexCarriers ha haL e ell κ he hκ z hlz hgz i)) ≤ C
            ∧
      (∑ i, dist (picardRadialRealCarriers ha haL e ell κ he hκ z hlz hgz i)
          (picardRadialRealCarriers ha haL e ell κ he hκ w hlw hgw i)) +
        (∑ i, dist (picardRadialComplexCarriers ha haL e ell κ he hκ z hlz hgz i)
          (picardRadialComplexCarriers ha haL e ell κ he hκ w hlw hgw i)) ≤ C * dist z w := by
  obtain ⟨Cr, hCr, hr⟩ := picardRadiusRecon_uniform B R hB hR
  obtain ⟨Cp, hCp, hp⟩ := picardScalarRecon_uniform ell B R he hB hR
  obtain ⟨CQ, hCQ, hQ⟩ := picardChargeRecon_uniform ell B R e he hB hR
  obtain ⟨Cm, hCm, hm⟩ := picardMassRecon_uniform ell B R e he hB hR
  obtain ⟨Cmu, hCmu, hmu⟩ := picardMuQRecon_uniform ell B R e he hB hR
  obtain ⟨Cg, hCg, hg⟩ := picardGapCarriers_uniform ell B R κ e he hκ hB hR
  obtain ⟨Cn, hCn, hn⟩ := picardNuRecon_uniform ell B R κ e he hκ hB hR
  obtain ⟨Cs, hCs, hs⟩ := picardSourceCarriers_uniform ell B R κ e he hκ hB hR
  obtain ⟨CA, hCA, hA⟩ := picardARecon_uniform ell B R κ e he hκ hB hR
  obtain ⟨CF, hCF, hF⟩ := picardOrdinarySourceRecon_uniform ell B R κ e he hκ hB hR
  obtain ⟨Cf, hCf, hf⟩ := picardScalarDifferenceRecon_uniform ell B R he hB hR
  let K := 1 + Cr + Cp + CQ + Cm + Cmu + Cg + Cn + Cs + CA + CF + Cf
  have hK : 0 < K := by dsimp [K]; positivity
  have hCrK : Cr ≤ K :=
      by dsimp [K]; linarith only [hCp, hCQ, hCm, hCmu, hCg, hCn, hCs, hCA, hCF, hCf]
  have hCpK : Cp ≤ K :=
      by dsimp [K]; linarith only [hCr, hCQ, hCm, hCmu, hCg, hCn, hCs, hCA, hCF, hCf]
  have hCQK : CQ ≤ K :=
      by dsimp [K]; linarith only [hCr, hCp, hCm, hCmu, hCg, hCn, hCs, hCA, hCF, hCf]
  have hCmK : Cm ≤ K :=
      by dsimp [K]; linarith only [hCr, hCp, hCQ, hCmu, hCg, hCn, hCs, hCA, hCF, hCf]
  have hCmuK : Cmu ≤ K :=
      by dsimp [K]; linarith only [hCr, hCp, hCQ, hCm, hCg, hCn, hCs, hCA, hCF, hCf]
  have hCgK : Cg ≤ K :=
      by dsimp [K]; linarith only [hCr, hCp, hCQ, hCm, hCmu, hCn, hCs, hCA, hCF, hCf]
  have hCnK : Cn ≤ K :=
      by dsimp [K]; linarith only [hCr, hCp, hCQ, hCm, hCmu, hCg, hCs, hCA, hCF, hCf]
  have hCsK : Cs ≤ K :=
      by dsimp [K]; linarith only [hCr, hCp, hCQ, hCm, hCmu, hCg, hCn, hCA, hCF, hCf]
  have hCAK : CA ≤ K :=
      by dsimp [K]; linarith only [hCr, hCp, hCQ, hCm, hCmu, hCg, hCn, hCs, hCF, hCf]
  have hCFK : CF ≤ K :=
      by dsimp [K]; linarith only [hCr, hCp, hCQ, hCm, hCmu, hCg, hCn, hCs, hCA, hCf]
  have hCfK : Cf ≤ K :=
      by dsimp [K]; linarith only [hCr, hCp, hCQ, hCm, hCmu, hCg, hCn, hCs, hCA, hCF]
  refine ⟨17 * K, by positivity, ?_⟩
  intro c a L ha haL hLR z w hlz hlw hgz hgw hz hw
  have hreal (i : Fin 12) :
      picardCarrierSize (picardRadialRealCarriers ha haL e ell κ he hκ z hlz hgz i) ≤ K ∧
      dist (picardRadialRealCarriers ha haL e ell κ he hκ z hlz hgz i)
        (picardRadialRealCarriers ha haL e ell κ he hκ w hlw hgw i) ≤ K * dist z w := by
    fin_cases i <;> simp only [picardRadialRealCarriers, Matrix.cons_val_zero',
        Matrix.cons_val_succ']
    · exact picard_enlarge_carrier_bounds_aux hCrK dist_nonneg (hr c a L ha haL hLR z w hz hw)
    · exact picard_enlarge_carrier_bounds_aux hCQK dist_nonneg (hQ c a L ha haL hLR z w hlz hlw hz
        hw)
    · exact picard_enlarge_carrier_bounds_aux hCmK dist_nonneg (hm c a L ha haL hLR z w hlz hlw hz
        hw)
    · simpa [picardMuQCarriers] using picard_enlarge_carrier_bounds_aux hCmuK dist_nonneg
        (hmu c a L ha haL hLR z w hlz hlw hz hw 0)
    · simpa [picardMuQCarriers] using picard_enlarge_carrier_bounds_aux hCmuK dist_nonneg
        (hmu c a L ha haL hLR z w hlz hlw hz hw 1)
    · simpa [picardGapCarriers] using picard_enlarge_carrier_bounds_aux hCgK dist_nonneg
        (hg c a L ha haL hLR z w hlz hlw hgz hgw hz hw 0)
    · exact picard_enlarge_carrier_bounds_aux hCnK dist_nonneg
        (hn c a L ha haL hLR z w hlz hlw hgz hgw hz hw)
    · simpa [picardGapCarriers] using picard_enlarge_carrier_bounds_aux hCgK dist_nonneg
        (hg c a L ha haL hLR z w hlz hlw hgz hgw hz hw 1)
    · have h := hs c a L ha haL hLR z w hlz hlw hgz hgw hz hw 1
      simpa [picardRealSourceCarriers] using picard_enlarge_carrier_bounds_aux hCsK dist_nonneg
          ⟨h.1, h.2.1⟩
    · have h := hs c a L ha haL hLR z w hlz hlw hgz hgw hz hw 0
      simpa [picardRealSourceCarriers] using picard_enlarge_carrier_bounds_aux hCsK dist_nonneg
          ⟨h.1, h.2.1⟩
    · exact picard_enlarge_carrier_bounds_aux hCAK dist_nonneg
        (hA c a L ha haL hLR z w hlz hlw hgz hgw hz hw)
    · simpa [picardGapCarriers] using picard_enlarge_carrier_bounds_aux hCgK dist_nonneg
        (hg c a L ha haL hLR z w hlz hlw hgz hgw hz hw 2)
  have hcomplex (i : Fin 5) :
      picardCarrierSize (picardRadialComplexCarriers ha haL e ell κ he hκ z hlz hgz i) ≤ K ∧
      dist (picardRadialComplexCarriers ha haL e ell κ he hκ z hlz hgz i)
        (picardRadialComplexCarriers ha haL e ell κ he hκ w hlw hgw i) ≤ K * dist z w := by
    fin_cases i <;> simp only [picardRadialComplexCarriers, Matrix.cons_val_zero',
        Matrix.cons_val_succ']
    · exact picard_enlarge_carrier_bounds_aux hCpK dist_nonneg (hp c a L ha haL hLR z w hlz hlw hz
        hw)
    · exact picard_enlarge_carrier_bounds_aux hCfK dist_nonneg (hf c a L ha haL hLR z w hlz hlw hz
        hw)
    · have h := hs c a L ha haL hLR z w hlz hlw hgz hgw hz hw 0
      simpa [picardComplexSourceCarriers] using picard_enlarge_carrier_bounds_aux hCsK dist_nonneg
          ⟨h.2.2.1, h.2.2.2⟩
    · have h := hs c a L ha haL hLR z w hlz hlw hgz hgw hz hw 1
      simpa [picardComplexSourceCarriers] using picard_enlarge_carrier_bounds_aux hCsK dist_nonneg
          ⟨h.2.2.1, h.2.2.2⟩
    · exact picard_enlarge_carrier_bounds_aux hCFK dist_nonneg
        (hF c a L ha haL hLR z w hlz hlw hgz hgw hz hw)
  constructor
  · calc
      _ ≤ (∑ _i : Fin 12, K) + (∑ _i : Fin 5, K) := add_le_add
        (Finset.sum_le_sum (fun i _ => (hreal i).1))
        (Finset.sum_le_sum (fun i _ => (hcomplex i).1))
      _ = _ := by simp; ring
  · calc
      _ ≤ (∑ _i : Fin 12, K * dist z w) + (∑ _i : Fin 5, K * dist z w) := add_le_add
        (Finset.sum_le_sum (fun i _ => (hreal i).2))
        (Finset.sum_le_sum (fun i _ => (hcomplex i).2))
      _ = _ := by simp; ring

/-- [node restart-sec-independent-null-construction#radial-c1-lipschitz]
All radial reconstructions and coefficients, with their continuous outgoing
first jets, are uniformly bounded and locally Lipschitz on the S1 domain.
The constant depends only on `ell,U,H,D,E,R,κ,|e|`, before cone position,
incoming width, actual length and candidates. The maximum carrier norm is
equivalent to the blueprint's sum norm. No candidate second derivative is used. -/
theorem radial_c1_lipschitz (ell U H D E R κ e : ℝ) (he : 0 < ell)
    (hκ : 0 < κ) (hR : 0 < R) :
    ∃ C > 0, ∀ (c a L : ℝ) (ha : 0 < a) (haL : a ≤ L), L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
        (hgz : ∀ q, κ ≤ 1 - picardMuValues e ell he z hlz q)
        (hgw : ∀ q, κ ≤ 1 - picardMuValues e ell he w hlw q),
      (∀ q, (z.1.1 q).1 ≤ U) → (∀ q, (w.1.1 q).1 ≤ U) →
      (∀ q, ‖(z.1.1 q).2‖ ≤ H) → (∀ q, ‖(w.1.1 q).2‖ ≤ H) →
      (∀ q, ‖(z.1.2 q).2‖ ≤ D) → (∀ q, ‖(w.1.2 q).2‖ ≤ D) →
      (∀ q, |(z.1.2 q).1| ≤ E) → (∀ q, |(w.1.2 q).1| ≤ E) →
      (∑ i, picardCarrierSize (picardRadialRealCarriers ha.le haL e ell κ he hκ z hlz hgz i)) +
        (∑ i, picardCarrierSize (picardRadialComplexCarriers ha.le haL e ell κ he hκ z hlz hgz i)) ≤
            C ∧
      (∑ i, dist (picardRadialRealCarriers ha.le haL e ell κ he hκ z hlz hgz i)
          (picardRadialRealCarriers ha.le haL e ell κ he hκ w hlw hgw i)) +
        (∑ i, dist (picardRadialComplexCarriers ha.le haL e ell κ he hκ z hlz hgz i)
          (picardRadialComplexCarriers ha.le haL e ell κ he hκ w hlw hgw i)) ≤ C * dist z w := by
  let B := 1 + |U| + |H| + |D| + |E|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hUB : U ≤ B :=
      by dsimp [B]; linarith [le_abs_self U, abs_nonneg H, abs_nonneg D, abs_nonneg E]
  have hHB : H ≤ B :=
      by dsimp [B]; linarith [le_abs_self H, abs_nonneg U, abs_nonneg D, abs_nonneg E]
  have hDB : D ≤ B :=
      by dsimp [B]; linarith [le_abs_self D, abs_nonneg U, abs_nonneg H, abs_nonneg E]
  have hEB : E ≤ B :=
      by dsimp [B]; linarith [le_abs_self E, abs_nonneg U, abs_nonneg H, abs_nonneg D]
  obtain ⟨C, hC, hc⟩ := picard_radial_carriers_uniform ell B R κ e he hκ hB hR.le
  refine ⟨C, hC, ?_⟩
  intro c a L ha haL hLR z w hlz hlw hgz hgw hzu hwu hzh hwh hzD hwD hzE hwE
  have hsize (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
      (hu : ∀ q, (z.1.1 q).1 ≤ U) (hh : ∀ q, ‖(z.1.1 q).2‖ ≤ H)
      (hD : ∀ q, ‖(z.1.2 q).2‖ ≤ D) (hE : ∀ q, |(z.1.2 q).1| ≤ E) :
      picardCarrierSize z ≤ B := by
    apply picardCarrierSize_le_of_pointwise B hB z
    · intro p
      apply max_le
      · rw [Real.norm_eq_abs, abs_of_nonneg (he.trans_le (hl p)).le]
        exact (hu p).trans hUB
      · exact (hh p).trans hHB
    · intro p
      exact max_le ((hE p).trans hEB) ((hD p).trans hDB)
  exact hc c a L ha.le haL hLR z w hlz hlw hgz hgw
    (hsize z hlz hzu hzh hzD hzE) (hsize w hlw hwu hwh hwD hwE)

end EmcsfAcExtension.Local
