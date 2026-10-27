module

public import EmcsfAcExtension.Local.Construction.PicardGap
public import EmcsfAcExtension.Local.Construction.PicardAlgebra

/-! # Radius division with continuous vanishing profiles

A quadratic numerator and its linear outgoing jet admit a regular radius
quotient. Iteration handles cubic numerators divided by radius squared. The
construction uses the first jet and never differentiates a normalized profile.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The continuous radius-quotient values for a quadratically vanishing numerator. -/
@[expose] noncomputable def picardDivisionValues (ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (F0 : C(PicardDomain c a L, E)) : C(PicardDomain c a L, E) where
  toFun p := (p.1.2 - p.1.1) • ((picardRadialAverage ⟨fun q => (z.1.1 q).1, z.1.1.continuous.fst⟩
      p)⁻¹ • F0 p)
  continuous_toFun := by
    let R : C(PicardDomain c a L, ℝ) := picardRadialAverage ⟨fun q => (z.1.1 q).1,
        z.1.1.continuous.fst⟩
    have hp (p : PicardDomain c a L) : 0 < R p := he.trans_le (picardRadialAverage_lower _ hl p)
    exact ((continuous_snd.comp continuous_subtype_val).sub
      (continuous_fst.comp continuous_subtype_val)).smul
      ((R.continuous.inv₀ (fun p => (hp p).ne')).smul F0.continuous)
/-- The continuous radius-quotient jet obtained from two given vanishing profiles. -/
@[expose] noncomputable def picardDivisionJets (ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (F0 J0 : C(PicardDomain c a L, E)) : C(PicardDomain c a L, E) where
  toFun p := (picardRadialAverage ⟨fun q => (z.1.1 q).1, z.1.1.continuous.fst⟩ p)⁻¹ • J0 p -
    ((z.1.1 p).1 / (picardRadialAverage ⟨fun q => (z.1.1 q).1, z.1.1.continuous.fst⟩ p) ^ 2) • F0 p
  continuous_toFun := by
    let R : C(PicardDomain c a L, ℝ) := picardRadialAverage ⟨fun q => (z.1.1 q).1,
        z.1.1.continuous.fst⟩
    have hp (p : PicardDomain c a L) : 0 < R p := he.trans_le (picardRadialAverage_lower _ hl p)
    exact ((R.continuous.inv₀ (fun p => (hp p).ne')).smul J0.continuous).sub
      ((z.1.1.continuous.fst.div (R.continuous.pow 2)
        (fun p => pow_ne_zero 2 (hp p).ne')).smul F0.continuous)

/-- The regularized values equal division by the reconstructed radius on the full wedge. -/
theorem picardDivisionValues_eq_aux (ha : 0 ≤ a) (haL : a ≤ L) (ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (F : PicardCarrier c a L E) (F0 : C(PicardDomain c a L, E))
    (hv : ∀ p, F.1.1 p = (p.1.2 - p.1.1) ^ 2 • F0 p) (p : PicardDomain c a L) :
    picardDivisionValues ell he z hl F0 p = (Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2)⁻¹ •
      picardCarrierValue ha haL F p.1.1 p.1.2 := by
  rw [picardCarrierValue_coe, hv p, picard_recon_r_eq_radialAverage ha haL z p]
  let R : ℝ := picardRadialAverage ⟨fun q => (z.1.1 q).1, z.1.1.continuous.fst⟩ p
  have hR : 0 < R := he.trans_le (picardRadialAverage_lower _ hl p)
  rcases lt_or_eq_of_le p.2.1.2.1 with hp|hp
  · have hx : 0 < p.1.2 - p.1.1 := sub_pos.mpr hp
    change (p.1.2 - p.1.1) • (R⁻¹ • F0 p) = ((p.1.2 - p.1.1) * R)⁻¹ • ((p.1.2 - p.1.1) ^ 2 • F0 p)
    simp only [smul_smul]
    congr 1
    field_simp [hx.ne', hR.ne']
  · simp [picardDivisionValues, hp]

/-- The radius quotient has the regularized outgoing derivative in section interiors. -/
theorem picardDivision_hasDerivAt_aux (ha : 0 ≤ a) (haL : a ≤ L) (ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (F : PicardCarrier c a L E) (F0 J0 : C(PicardDomain c a L, E))
    (hv : ∀ p, F.1.1 p = (p.1.2 - p.1.1) ^ 2 • F0 p)
    (hj : ∀ p, F.1.2 p = (p.1.2 - p.1.1) • J0 p)
    (p : PicardDomain c a L) (hp : p.1.1 < p.1.2) (ht : p.1.2 < c + L) :
    HasDerivAt (fun v => (Recon.r (picardCandidateLam ha haL z) p.1.1 v)⁻¹ •
      picardCarrierValue ha haL F p.1.1 v) (picardDivisionJets ell he z hl F0 J0 p) p.1.2 := by
  have hc : Continuous (picardCandidateLam ha haL z p.1.1) :=
    (continuous_picardCandidateLam ha haL z).comp (continuous_const.prodMk continuous_id)
  have hr : HasDerivAt (Recon.r (picardCandidateLam ha haL z) p.1.1)
      (picardCandidateLam ha haL z p.1.1 p.1.2) p.1.2 :=
    (hc.integral_hasStrictDerivAt p.1.1 p.1.2).hasDerivAt
  let x := p.1.2 - p.1.1
  let R : ℝ := picardRadialAverage ⟨fun q => (z.1.1 q).1, z.1.1.continuous.fst⟩ p
  have hx : 0 < x := sub_pos.mpr hp
  have hR : 0 < R := he.trans_le (picardRadialAverage_lower _ hl p)
  have hrp : 0 < Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 := by
    rw [picard_recon_r_eq_radialAverage ha haL z p]
    exact mul_pos hx hR
  have hd := (hr.fun_inv hrp.ne').fun_smul (picardCarrierValue_hasDerivAt ha haL F p hp ht)
  convert hd using 1
  rw [picardCarrierValue_coe, hv p, hj p, picardCandidateLam_coe ha haL z p,
    picard_recon_r_eq_radialAverage ha haL z p]
  change R⁻¹ • J0 p - ((z.1.1 p).1 / R ^ 2) • F0 p =
    (x * R)⁻¹ • (x • J0 p) + (-(z.1.1 p).1 / (x * R) ^ 2) • (x ^ 2 • F0 p)
  have h1 : (x * R)⁻¹ * x = R⁻¹ := by field_simp [hx.ne', hR.ne']
  have h2 : (-(z.1.1 p).1 / (x * R) ^ 2) * x ^ 2 = -((z.1.1 p).1 / R ^ 2) := by
    field_simp [hx.ne', hR.ne']
  rw [smul_smul, smul_smul, h1, h2, neg_smul, sub_eq_add_neg]
/-- Divide a quadratic numerator carrier by the reconstructed radius.
Its continuous value and jet profiles suffice; neither profile is differentiated. -/
@[expose] noncomputable def picardDivideRadius (ha : 0 ≤ a) (haL : a ≤ L) (ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (F : PicardCarrier c a L E) (F0 J0 : C(PicardDomain c a L, E))
    (hv : ∀ p, F.1.1 p = (p.1.2 - p.1.1) ^ 2 • F0 p)
    (hj : ∀ p, F.1.2 p = (p.1.2 - p.1.1) • J0 p) : PicardCarrier c a L E :=
  picardCarrierOfRawDeriv
    (fun u v => (Recon.r (picardCandidateLam ha haL z) u v)⁻¹ • picardCarrierValue ha haL F u v)
    (picardDivisionValues ell he z hl F0) (picardDivisionJets ell he z hl F0 J0)
    (picardDivisionValues_eq_aux ha haL ell he z hl F F0 hv)
    (fun p hp ht => picardDivision_hasDerivAt_aux ha haL ell he z hl F F0 J0 hv hj p hp ht)

/-- The radius-division carrier has exactly the quotient values, including the axis. -/
theorem picardDivideRadius_value (ha : 0 ≤ a) (haL : a ≤ L) (ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (F : PicardCarrier c a L E) (F0 J0 : C(PicardDomain c a L, E))
    (hv : ∀ p, F.1.1 p = (p.1.2 - p.1.1) ^ 2 • F0 p)
    (hj : ∀ p, F.1.2 p = (p.1.2 - p.1.1) • J0 p) (p : PicardDomain c a L) :
    (picardDivideRadius ha haL ell he z hl F F0 J0 hv hj).1.1 p =
      (Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2)⁻¹ • F.1.1 p := by
  change picardDivisionValues ell he z hl F0 p = _
  simpa only [picardCarrierValue_coe] using picardDivisionValues_eq_aux ha haL ell he z hl F F0 hv p

/-- Invert a real carrier with an explicit uniform positive lower bound. -/
@[expose] noncomputable def picardCarrierInv (ha : 0 ≤ a) (haL : a ≤ L) (kappa : ℝ) (hk : 0 < kappa)
    (F : PicardCarrier c a L ℝ) (hF : ∀ p, kappa ≤ F.1.1 p) : PicardCarrier c a L ℝ :=
  picardCarrierOfRawDeriv (fun u v => (picardCarrierValue ha haL F u v)⁻¹)
    ⟨fun p => (F.1.1 p)⁻¹, F.1.1.continuous.inv₀ (fun p => (hk.trans_le (hF p)).ne')⟩
    ⟨fun p => -F.1.2 p / (F.1.1 p) ^ 2, F.1.2.continuous.neg.div (F.1.1.continuous.pow 2)
      (fun p => pow_ne_zero 2 (hk.trans_le (hF p)).ne')⟩
    (by intro p; simp only [ContinuousMap.coe_mk, picardCarrierValue_coe])
    (by
      intro p hp ht
      have hr : picardCarrierValue ha haL F p.1.1 p.1.2 ≠ 0 := by
        rw [picardCarrierValue_coe]
        exact (hk.trans_le (hF p)).ne'
      simpa only [ContinuousMap.coe_mk, picardCarrierValue_coe] using
        (picardCarrierValue_hasDerivAt ha haL F p hp ht).fun_inv hr)

/-- Multiply a continuous profile by the distance to the axis. -/
@[expose] noncomputable def picardWidthSmul (F : C(PicardDomain c a L, E)) : C(PicardDomain c a L,
    E) where
  toFun p := (p.1.2 - p.1.1) • F p
  continuous_toFun := ((continuous_snd.comp continuous_subtype_val).sub
    (continuous_fst.comp continuous_subtype_val)).smul F.continuous
/-- Divide a continuous profile by the positive radial average of the candidate expansion. -/
@[expose] noncomputable def picardAverageInvSmul (ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (F0 : C(PicardDomain c a L, E)) : C(PicardDomain c a L, E) where
  toFun p := (picardRadialAverage ⟨fun q => (z.1.1 q).1, z.1.1.continuous.fst⟩ p)⁻¹ • F0 p
  continuous_toFun := ((picardRadialAverage ⟨fun q => (z.1.1 q).1,
      z.1.1.continuous.fst⟩).continuous.inv₀
    (fun p => (he.trans_le (picardRadialAverage_lower _ hl p)).ne')).smul F0.continuous
/-- Divide a cubic numerator carrier by radius squared through two regularized
radius divisions. Only the supplied value and first-jet profiles are used. -/
@[expose] noncomputable def picardDivideRadiusSq (ha : 0 ≤ a) (haL : a ≤ L) (ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (F : PicardCarrier c a L E) (F0 J0 : C(PicardDomain c a L, E))
    (hv : ∀ p, F.1.1 p = (p.1.2 - p.1.1) ^ 3 • F0 p)
    (hj : ∀ p, F.1.2 p = (p.1.2 - p.1.1) ^ 2 • J0 p) : PicardCarrier c a L E := by
  have hv' (p : PicardDomain c a L) : F.1.1 p = (p.1.2 - p.1.1) ^ 2 • picardWidthSmul F0 p := by
    rw [hv p]
    change (p.1.2 - p.1.1) ^ 3 • F0 p = (p.1.2 - p.1.1) ^ 2 • ((p.1.2 - p.1.1) • F0 p)
    rw [smul_smul]
    congr 1
  have hj' (p : PicardDomain c a L) : F.1.2 p = (p.1.2 - p.1.1) • picardWidthSmul J0 p := by
    rw [hj p]
    change (p.1.2 - p.1.1) ^ 2 • J0 p = (p.1.2 - p.1.1) • ((p.1.2 - p.1.1) • J0 p)
    rw [smul_smul]
    congr 1; ring
  let F1 := picardDivideRadius ha haL ell he z hl F (picardWidthSmul F0) (picardWidthSmul J0) hv'
      hj'
  refine picardDivideRadius ha haL ell he z hl F1 (picardAverageInvSmul ell he z hl F0)
    (picardDivisionJets ell he z hl F0 J0) ?_ ?_
  · intro p
    let x := p.1.2 - p.1.1
    let R : ℝ := picardRadialAverage ⟨fun q => (z.1.1 q).1, z.1.1.continuous.fst⟩ p
    change x • (R⁻¹ • (x • F0 p)) = x ^ 2 • (R⁻¹ • F0 p)
    simp only [smul_smul]
    congr 1; ring
  · intro p
    let x := p.1.2 - p.1.1
    let R : ℝ := picardRadialAverage ⟨fun q => (z.1.1 q).1, z.1.1.continuous.fst⟩ p
    change R⁻¹ • (x • J0 p) - ((z.1.1 p).1 / R ^ 2) • (x • F0 p) =
      x • (R⁻¹ • J0 p - ((z.1.1 p).1 / R ^ 2) • F0 p)
    simp only [smul_sub, smul_smul, mul_comm]

/-- Real carrier multiplication has the pointwise product values. -/
@[simp] theorem picardCarrierMul_value (ha : 0 ≤ a) (haL : a ≤ L)
    (F G : PicardCarrier c a L ℝ) (p : PicardDomain c a L) :
    (picardCarrierMul ha haL F G).1.1 p = F.1.1 p * G.1.1 p := rfl
/-- Real carrier multiplication has the product-rule outgoing jet. -/
@[simp] theorem picardCarrierMul_jet (ha : 0 ≤ a) (haL : a ≤ L)
    (F G : PicardCarrier c a L ℝ) (p : PicardDomain c a L) :
    (picardCarrierMul ha haL F G).1.2 p = F.1.2 p * G.1.1 p + F.1.1 p * G.1.2 p := rfl
/-- Complex carrier multiplication has the pointwise product values. -/
@[simp] theorem picardCarrierCMul_value (ha : 0 ≤ a) (haL : a ≤ L)
    (F G : PicardCarrier c a L ℂ) (p : PicardDomain c a L) :
    (picardCarrierCMul ha haL F G).1.1 p = F.1.1 p * G.1.1 p := rfl
/-- Complex carrier multiplication has the product-rule outgoing jet. -/
@[simp] theorem picardCarrierCMul_jet (ha : 0 ≤ a) (haL : a ≤ L)
    (F G : PicardCarrier c a L ℂ) (p : PicardDomain c a L) :
    (picardCarrierCMul ha haL F G).1.2 p = F.1.2 p * G.1.1 p + F.1.1 p * G.1.2 p := rfl
/-- A continuous linear carrier map acts pointwise on values. -/
@[simp] theorem picardCarrierLinear_value {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y]
    (ha : 0 ≤ a) (haL : a ≤ L) (T : E →L[ℝ] Y) (F : PicardCarrier c a L E)
    (p : PicardDomain c a L) : (picardCarrierLinear ha haL T F).1.1 p = T (F.1.1 p) := rfl
/-- A continuous linear carrier map acts pointwise on outgoing jets. -/
@[simp] theorem picardCarrierLinear_jet {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y]
    (ha : 0 ≤ a) (haL : a ≤ L) (T : E →L[ℝ] Y) (F : PicardCarrier c a L E)
    (p : PicardDomain c a L) : (picardCarrierLinear ha haL T F).1.2 p = T (F.1.2 p) := rfl
/-- Carrier negation negates values. -/
@[simp] theorem picardCarrierNeg_value (ha : 0 ≤ a) (haL : a ≤ L) (F : PicardCarrier c a L E)
    (p : PicardDomain c a L) : (picardCarrierNeg ha haL F).1.1 p = -F.1.1 p := rfl
/-- Carrier negation negates outgoing jets. -/
@[simp] theorem picardCarrierNeg_jet (ha : 0 ≤ a) (haL : a ≤ L) (F : PicardCarrier c a L E)
    (p : PicardDomain c a L) : (picardCarrierNeg ha haL F).1.2 p = -F.1.2 p := rfl
/-- Carrier addition adds values. -/
@[simp] theorem picardCarrierAdd_value (ha : 0 ≤ a) (haL : a ≤ L) (F G : PicardCarrier c a L E)
    (p : PicardDomain c a L) : (picardCarrierAdd ha haL F G).1.1 p = F.1.1 p + G.1.1 p := rfl
/-- Carrier addition adds outgoing jets. -/
@[simp] theorem picardCarrierAdd_jet (ha : 0 ≤ a) (haL : a ≤ L) (F G : PicardCarrier c a L E)
    (p : PicardDomain c a L) : (picardCarrierAdd ha haL F G).1.2 p = F.1.2 p + G.1.2 p := rfl

/-- The twice-divided carrier has exactly the radius-square quotient values. -/
theorem picardDivideRadiusSq_value (ha : 0 ≤ a) (haL : a ≤ L) (ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (F : PicardCarrier c a L E) (F0 J0 : C(PicardDomain c a L, E))
    (hv : ∀ p, F.1.1 p = (p.1.2 - p.1.1) ^ 3 • F0 p)
    (hj : ∀ p, F.1.2 p = (p.1.2 - p.1.1) ^ 2 • J0 p) (p : PicardDomain c a L) :
    (picardDivideRadiusSq ha haL ell he z hl F F0 J0 hv hj).1.1 p =
      (Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 ^ 2)⁻¹ • F.1.1 p := by
  simp only [picardDivideRadiusSq, picardDivideRadius_value, smul_smul, pow_two, mul_inv]

end EmcsfAcExtension.Local
