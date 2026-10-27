module

public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Complete carrier for the incoming Picard iteration

The compact domain is the wedge `W(c,a,L)` of internal project record. A candidate stores its
values and its outgoing first derivative as continuous maps. The sectional FTC
identity cuts out a closed subspace in the product of two sup norm spaces.
No derivative in the incoming coordinate is required.

This module supplies function space infrastructure; it closes no graph node.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

/-- Compact wedge `W(c,a,L)`, including its axis and both endpoint cones. -/
abbrev PicardDomain (c a L : ℝ) :=
  ↥(triangle c (c + L) ∩ {p : ℝ × ℝ | p.1 ≤ c + a})

/-- The closed wedge is compact, including when one of its lengths is zero. -/
instance picardDomainCompactSpace (c a L : ℝ) : CompactSpace (PicardDomain c a L) :=
  isCompact_iff_compactSpace.mp ((isCompact_triangle c (c + L)).inter_right
    (isClosed_le continuous_fst continuous_const))

/-- Continuous values and continuous outgoing jets, with their maximum sup norm.
For the Picard pair take `E = ℝ × ℂ`; its coordinates are `(λ,h)`. -/
abbrev PicardJet (c a L : ℝ) (E : Type*) [TopologicalSpace E] :=
  C(PicardDomain c a L, E) × C(PicardDomain c a L, E)

variable {c a L : ℝ}

/-- Clamp an outgoing coordinate to the closed section through `p`. -/
@[expose] noncomputable def picardSectionPoint
    (p : PicardDomain c a L) (v : ℝ) : PicardDomain c a L :=
  ⟨(p.1.1, projIcc p.1.1 (c + L) (p.2.1.2.1.trans p.2.1.2.2) v),
    ⟨⟨p.2.1.1, (projIcc p.1.1 (c + L)
      (p.2.1.2.1.trans p.2.1.2.2) v).2⟩, p.2.2⟩⟩

/-- Clamping along one outgoing section is continuous. -/
theorem continuous_picardSectionPoint (p : PicardDomain c a L) :
    Continuous (picardSectionPoint p) := by
  unfold picardSectionPoint
  exact (continuous_const.prodMk continuous_projIcc.subtype_val).subtype_mk _

/-- Clamping fixes coordinates already in the section. -/
theorem picardSectionPoint_of_mem (p : PicardDomain c a L) {v : ℝ}
    (hv : v ∈ Icc p.1.1 (c + L)) :
    (picardSectionPoint p v).1 = (p.1.1, v) := by
  simp [picardSectionPoint, projIcc_of_mem _ hv]

/-- The upper endpoint of the radial segment through `p` is `p` itself. -/
@[simp] theorem picardSectionPoint_self (p : PicardDomain c a L) :
    picardSectionPoint p p.1.2 = p := by
  apply Subtype.ext
  exact picardSectionPoint_of_mem p ⟨p.2.1.2.1, p.2.1.2.2⟩

/-- Successive clamps on the same outgoing section agree. -/
@[simp] theorem picardSectionPoint_sectionPoint (p : PicardDomain c a L) (v w : ℝ) :
    picardSectionPoint (picardSectionPoint p v) w = picardSectionPoint p w := rfl

/-- A continuous retraction of the ambient plane onto the nonempty wedge.
The first coordinate is clamped first, then the outgoing coordinate is clamped
to its section. This permits total representatives for `Recon` without choices. -/
@[expose] noncomputable def picardClamp (ha : 0 ≤ a) (haL : a ≤ L) (p : ℝ × ℝ) :
    PicardDomain c a L :=
  let u := projIcc c (c + a) (by linarith) p.1
  let v := projIcc (u : ℝ) (c + L) (by linarith [u.2.2]) p.2
  ⟨(u, v), ⟨⟨u.2.1, v.2⟩, u.2.2⟩⟩

/-- The ambient clamp is continuous, including where its active side changes. -/
theorem continuous_picardClamp (ha : 0 ≤ a) (haL : a ≤ L) :
    Continuous (picardClamp (c := c) ha haL) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : ℝ × ℝ =>
    (max c (min (c + a) p.1), max (max c (min (c + a) p.1)) (min (c + L) p.2)))
  fun_prop

/-- The clamp is the identity on the wedge. -/
@[simp] theorem picardClamp_coe (ha : 0 ≤ a) (haL : a ≤ L)
    (p : PicardDomain c a L) : picardClamp ha haL p.1 = p := by
  apply Subtype.ext
  change (max c (min (c + a) p.1.1),
    max (max c (min (c + a) p.1.1)) (min (c + L) p.1.2)) = p.1
  rw [min_eq_right p.2.2, max_eq_right p.2.1.1,
    min_eq_right p.2.1.2.2, max_eq_right p.2.1.2.1]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Sectional FTC compatibility for a value and its outgoing jet. Only clamped
values inside the wedge occur in the integral. -/
@[expose] def picardCompatible (c a L : ℝ) : Set (PicardJet c a L E) :=
  {z | ∀ p : PicardDomain c a L,
    z.1 p = z.1 (picardSectionPoint p p.1.1) +
      ∫ s in p.1.1..p.1.2, z.2 (picardSectionPoint p s)}

/-- The integral of an outgoing jet on a fixed segment depends continuously on
that jet in the sup topology. -/
theorem continuous_picardSectionIntegral (p : PicardDomain c a L) :
    Continuous (fun z : PicardJet c a L E =>
      ∫ s in p.1.1..p.1.2, z.2 (picardSectionPoint p s)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact continuous_eval.comp
    ((continuous_snd.comp continuous_fst).prodMk
      ((continuous_picardSectionPoint p).comp continuous_snd))

/-- The FTC identities define a closed set. This is the uniform-limit argument
for values and their first outgoing derivatives, expressed as closed equalizers. -/
theorem isClosed_picardCompatible : IsClosed (picardCompatible c a L (E := E)) := by
  simp only [picardCompatible, ofPred_forall]
  apply isClosed_iInter
  intro p
  exact isClosed_eq ((continuous_eval_const p).comp continuous_fst)
    (((continuous_eval_const _).comp continuous_fst).add
      (continuous_picardSectionIntegral p))

/-- Continuous pairs whose stored outgoing jets satisfy the sectional FTC.
The inherited metric is the maximum of the two sup distances. -/
abbrev PicardCarrier (c a L : ℝ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] :=
  ↥(picardCompatible c a L (E := E))

/-- Uniform limits preserve both continuity and the outgoing FTC identities. -/
instance picardCarrierCompleteSpace [CompleteSpace E] :
    CompleteSpace (PicardCarrier c a L E) :=
  isClosed_picardCompatible.completeSpace_coe

/-- The stored jet integrates to the difference of the stored values. -/
theorem picardCarrier_integral (z : PicardCarrier c a L E) (p : PicardDomain c a L) :
    (∫ s in p.1.1..p.1.2, z.1.2 (picardSectionPoint p s)) =
      z.1.1 p - z.1.1 (picardSectionPoint p p.1.1) := by
  have h := z.2 p
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h.symm)

/-- FTC compatibility identifies the stored jet as the outgoing within
derivative, including both endpoints of each closed outgoing section. -/
theorem picardCarrier_hasDerivWithinAt [CompleteSpace E]
    (z : PicardCarrier c a L E) (p : PicardDomain c a L) {v : ℝ}
    (hv : v ∈ Icc p.1.1 (c + L)) :
    HasDerivWithinAt (fun w => z.1.1 (picardSectionPoint p w))
      (z.1.2 (picardSectionPoint p v)) (Icc p.1.1 (c + L)) v := by
  have hd : Continuous (fun w => z.1.2 (picardSectionPoint p w)) :=
    z.1.2.continuous.comp (continuous_picardSectionPoint p)
  have h := ((hd.integral_hasStrictDerivAt p.1.1 v).hasDerivAt.const_add
    (z.1.1 (picardSectionPoint p p.1.1))).hasDerivWithinAt
      (s := Icc p.1.1 (c + L))
  apply h.congr_of_mem _ hv
  intro w hw
  have heq := z.2 (picardSectionPoint p w)
  simpa only [picardSectionPoint_sectionPoint,
    show (picardSectionPoint p w).1.1 = p.1.1 from rfl,
    show (picardSectionPoint p w).1.2 = w from
      congrArg Prod.snd (picardSectionPoint_of_mem p hw)] using heq

/-- A total representative of a carrier value, using the continuous clamp.
Every radial and incoming integral reads this representative only on the wedge. -/
noncomputable def picardCarrierValue (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L E) (u v : ℝ) : E := z.1.1 (picardClamp ha haL (u, v))

/-- The total clamped representative is jointly continuous. -/
theorem continuous_picardCarrierValue (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L E) :
    Continuous (Function.uncurry (picardCarrierValue ha haL z)) :=
  z.1.1.continuous.comp (continuous_picardClamp ha haL)

/-- The total representative agrees with the carrier at every domain point. -/
@[simp] theorem picardCarrierValue_coe (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L E) (p : PicardDomain c a L) :
    picardCarrierValue ha haL z p.1.1 p.1.2 = z.1.1 p := by
  simp [picardCarrierValue]

/-- Evaluation of values costs at most the carrier distance. The constant one
is universal and independent of the domain and the candidates. -/
theorem picardCarrier_dist_value_le (z w : PicardCarrier c a L E)
    (p : PicardDomain c a L) : dist (z.1.1 p) (w.1.1 p) ≤ dist z w :=
  (ContinuousMap.dist_apply_le_dist p).trans (le_max_left _ _)

/-- Evaluation of outgoing jets costs at most the carrier distance. The
constant one is universal and independent of the domain and the candidates. -/
theorem picardCarrier_dist_jet_le (z w : PicardCarrier c a L E)
    (p : PicardDomain c a L) : dist (z.1.2 p) (w.1.2 p) ≤ dist z w :=
  (ContinuousMap.dist_apply_le_dist p).trans (le_max_right _ _)

/-- The stored jet integrates to the value difference between any two points
of the same closed outgoing section, with the oriented-integral convention. -/
theorem picardCarrier_integral_between [CompleteSpace E]
    (z : PicardCarrier c a L E) (p : PicardDomain c a L) {v w : ℝ}
    (hv : v ∈ Icc p.1.1 (c + L)) (hw : w ∈ Icc p.1.1 (c + L)) :
    (∫ s in w..v, z.1.2 (picardSectionPoint p s)) =
      z.1.1 (picardSectionPoint p v) - z.1.1 (picardSectionPoint p w) := by
  have hc : Continuous (fun s => z.1.2 (picardSectionPoint p s)) :=
    z.1.2.continuous.comp (continuous_picardSectionPoint p)
  have hiV := picardCarrier_integral z (picardSectionPoint p v)
  have hiW := picardCarrier_integral z (picardSectionPoint p w)
  have hV := congrArg Prod.snd (picardSectionPoint_of_mem p hv)
  have hW := congrArg Prod.snd (picardSectionPoint_of_mem p hw)
  simp only [picardSectionPoint_sectionPoint,
    show (picardSectionPoint p v).1.1 = p.1.1 from rfl, hV] at hiV
  simp only [picardSectionPoint_sectionPoint,
    show (picardSectionPoint p w).1.1 = p.1.1 from rfl, hW] at hiW
  rw [← intervalIntegral.integral_interval_sub_left
    (hc.intervalIntegrable (μ := volume) p.1.1 v)
    (hc.intervalIntegrable (μ := volume) p.1.1 w), hiV, hiW]
  abel

/-- The real expansion component of a carrier's total clamped representative.
The clamp affects no argument read by the radial or incoming integrals. -/
noncomputable def picardCandidateLam (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) (u v : ℝ) : ℝ :=
  (picardCarrierValue ha haL z u v).1

/-- The complex normalized scalar component of a carrier's total representative. -/
noncomputable def picardCandidateH (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) (u v : ℝ) : ℂ :=
  (picardCarrierValue ha haL z u v).2

/-- The expansion representative supplied to `Recon` is jointly continuous. -/
theorem continuous_picardCandidateLam (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) :
    Continuous (Function.uncurry (picardCandidateLam ha haL z)) :=
  (continuous_picardCarrierValue ha haL z).fst

/-- The normalized scalar representative supplied to `Recon` is jointly continuous. -/
theorem continuous_picardCandidateH (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) :
    Continuous (Function.uncurry (picardCandidateH ha haL z)) :=
  (continuous_picardCarrierValue ha haL z).snd

/-- Candidate expansion evaluation agrees with its domain value. -/
@[simp] theorem picardCandidateLam_coe (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) (p : PicardDomain c a L) :
    picardCandidateLam ha haL z p.1.1 p.1.2 = (z.1.1 p).1 := by
  simp [picardCandidateLam]

/-- Candidate scalar evaluation agrees with its domain value. -/
@[simp] theorem picardCandidateH_coe (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) (p : PicardDomain c a L) :
    picardCandidateH ha haL z p.1.1 p.1.2 = (z.1.1 p).2 := by
  simp [picardCandidateH]

/-- A radial point at the clamped fraction `t` of the segment from the axis to
`p`. This normalizes every outgoing section to the fixed interval `[0,1]`. -/
@[expose] noncomputable def picardRadialPoint (p : PicardDomain c a L) (t : ℝ) :
    PicardDomain c a L := by
  let τ := projIcc (0 : ℝ) 1 (by norm_num) t
  refine ⟨(p.1.1, p.1.1 + (τ : ℝ) * (p.1.2 - p.1.1)), ⟨⟨p.2.1.1, ?_, ?_⟩, p.2.2⟩⟩
  · have h := mul_nonneg τ.2.1 (sub_nonneg.mpr p.2.1.2.1)
    linarith
  · have h := mul_le_mul_of_nonneg_right τ.2.2 (sub_nonneg.mpr p.2.1.2.1)
    linarith [p.2.1.2.2]
/-- Radial rescaling is jointly continuous, including at the axis. -/
theorem continuous_picardRadialPoint :
    Continuous (fun q : PicardDomain c a L × ℝ => picardRadialPoint q.1 q.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun q : PicardDomain c a L × ℝ =>
    (q.1.1.1, q.1.1.1 + max 0 (min 1 q.2) * (q.1.1.2 - q.1.1.1)))
  fun_prop
/-- On `[0,1]`, radial rescaling has its exact affine coordinate formula. -/
theorem picardRadialPoint_of_mem (p : PicardDomain c a L) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (picardRadialPoint p t).1 = (p.1.1, p.1.1 + t * (p.1.2 - p.1.1)) := by
  simp [picardRadialPoint, projIcc_of_mem _ ht]
/-- Average a continuous field along the normalized outgoing segment. -/
@[expose] noncomputable def picardRadialAverage (f : C(PicardDomain c a L, E)) :
    C(PicardDomain c a L, E) where
  toFun p := ∫ t in (0 : ℝ)..1, f (picardRadialPoint p t)
  continuous_toFun := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact f.continuous.comp continuous_picardRadialPoint
/-- Radial averaging has Lipschitz constant one in sup distance, universally
in `c,a,L,E` and both fields. -/
theorem picardRadialAverage_dist_le (f g : C(PicardDomain c a L, E)) :
    dist (picardRadialAverage f) (picardRadialAverage g) ≤ dist f g := by
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro p
  have hc (f : C(PicardDomain c a L, E)) : Continuous (fun t => f (picardRadialPoint p t)) :=
    f.continuous.comp (continuous_picardRadialPoint.comp (continuous_const.prodMk continuous_id))
  change dist (∫ t in (0 : ℝ)..1, f (picardRadialPoint p t))
    (∫ t in (0 : ℝ)..1, g (picardRadialPoint p t)) ≤ dist f g
  rw [dist_eq_norm, ← intervalIntegral.integral_sub
    ((hc f).intervalIntegrable (μ := volume) 0 1) ((hc g).intervalIntegrable (μ := volume) 0 1)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => f (picardRadialPoint p t) - g (picardRadialPoint p t))
    (a := 0) (b := 1) (C := dist f g) (fun t _ => by
      rw [← dist_eq_norm]
      exact ContinuousMap.dist_apply_le_dist _)
  simpa using hb
/-- Radial averaging preserves every pointwise real lower bound; its weights
are nonnegative and have total mass one. -/
theorem picardRadialAverage_lower (f : C(PicardDomain c a L, ℝ)) {ℓ : ℝ} (hl : ∀ q, ℓ ≤ f q)
    (p : PicardDomain c a L) : ℓ ≤ picardRadialAverage f p := by
  have hc : Continuous (fun t => f (picardRadialPoint p t)) :=
    f.continuous.comp (continuous_picardRadialPoint.comp (continuous_const.prodMk continuous_id))
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const (μ := volume)) (hc.intervalIntegrable (μ := volume) 0 1)
    (fun t _ => hl (picardRadialPoint p t))
  simpa [picardRadialAverage] using hi

private theorem picard_hJet_integral_between_aux (z : PicardCarrier c a L (ℝ × ℂ))
    (p : PicardDomain c a L) {v w : ℝ} (hv : v ∈ Icc p.1.1 (c + L))
    (hw : w ∈ Icc p.1.1 (c + L)) :
    (∫ s in w..v, (z.1.2 (picardSectionPoint p s)).2) =
      (z.1.1 (picardSectionPoint p v)).2 - (z.1.1 (picardSectionPoint p w)).2 := by
  have hi : IntervalIntegrable (fun s => z.1.2 (picardSectionPoint p s)) volume w v :=
    (z.1.2.continuous.comp (continuous_picardSectionPoint p)).intervalIntegrable w v
  have h := (ContinuousLinearMap.snd ℝ ℝ ℂ).intervalIntegral_comp_comm hi
  have h' := congrArg (fun q : ℝ × ℂ => q.2) (picardCarrier_integral_between z p hv hw)
  change (∫ s in w..v, (z.1.2 (picardSectionPoint p s)).2) =
    (∫ s in w..v, z.1.2 (picardSectionPoint p s)).2 at h
  exact h.trans h'

private theorem picard_section_radial_aux (p : PicardDomain c a L) {s : ℝ} (hs : s ∈ Icc 0 1) :
    picardSectionPoint p ((p.1.2 - p.1.1) * s + p.1.1) = picardRadialPoint p s := by
  have hx : 0 ≤ p.1.2 - p.1.1 := sub_nonneg.mpr p.2.1.2.1
  have hxs := mul_nonneg hx hs.1
  have hxupper := mul_le_mul_of_nonneg_left hs.2 hx
  have hmem : (p.1.2 - p.1.1) * s + p.1.1 ∈ Icc p.1.1 (c + L) := by
    constructor <;> linarith [p.2.1.2.2]
  apply Subtype.ext
  rw [picardSectionPoint_of_mem p hmem, picardRadialPoint_of_mem p hs]
  congr 1
  ring
/-- The rescaled FTC identity for scalar increments. It holds on the whole
closed wedge, including zero width, with no incoming derivative assumption. -/
theorem picardCarrier_h_increment_radial (z : PicardCarrier c a L (ℝ × ℂ)) (p : PicardDomain c a L)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    (z.1.1 p).2 - (z.1.1 (picardRadialPoint p t)).2 =
      (p.1.2 - p.1.1) • ∫ s in t..1, (z.1.2 (picardRadialPoint p s)).2 := by
  let x := p.1.2 - p.1.1
  have hx : 0 ≤ x := sub_nonneg.mpr p.2.1.2.1
  have hScaled := intervalIntegral.smul_integral_comp_mul_add
    (f := fun w => (z.1.2 (picardSectionPoint p w)).2) (a := t) (b := 1) x p.1.1
  have hI : (∫ s in t..1, (z.1.2 (picardSectionPoint p (x * s + p.1.1))).2) =
      ∫ s in t..1, (z.1.2 (picardRadialPoint p s)).2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.2] at hs
    dsimp only [x]
    exact congrArg (fun q : PicardDomain c a L => (z.1.2 q).2)
      (picard_section_radial_aux p ⟨ht.1.trans hs.1, hs.2⟩)
  have hu : x * 1 + p.1.1 = p.1.2 := by dsimp [x]; ring
  have hmem : x * t + p.1.1 ∈ Icc p.1.1 (c + L) := by
    have hlower := mul_nonneg hx ht.1
    have hupper := mul_le_mul_of_nonneg_left ht.2 hx
    constructor <;> linarith [p.2.1.2.2]
  rw [hu, hI, picard_hJet_integral_between_aux z p ⟨p.2.1.2.1, p.2.1.2.2⟩ hmem,
    picardSectionPoint_self] at hScaled
  dsimp only [x] at hScaled
  rw [picard_section_radial_aux p ht] at hScaled
  exact hScaled.symm


/-- Construct a compatible carrier from continuous values and jets whose raw
outgoing derivatives agree in section interiors. FTC determines the closed
section derivatives; no exterior derivative is imposed at the axis or top. -/
@[expose] noncomputable def picardCarrierOfRawDeriv [CompleteSpace E] (raw : ℝ → ℝ → E)
    (F J : C(PicardDomain c a L, E))
    (hF : ∀ p : PicardDomain c a L, F p = raw p.1.1 p.1.2)
    (hD : ∀ p : PicardDomain c a L, p.1.1 < p.1.2 → p.1.2 < c + L →
      HasDerivAt (raw p.1.1) (J p) p.1.2) : PicardCarrier c a L E := by
  refine ⟨(F, J), ?_⟩
  intro p
  have hc : Continuous (fun v => F (picardSectionPoint p v)) :=
    F.continuous.comp (continuous_picardSectionPoint p)
  have hj : Continuous (fun v => J (picardSectionPoint p v)) :=
    J.continuous.comp (continuous_picardSectionPoint p)
  have hd (v : ℝ) (hv : v ∈ Ioo p.1.1 p.1.2) :
      HasDerivAt (fun t => F (picardSectionPoint p t)) (J (picardSectionPoint p v)) v := by
    let q := picardSectionPoint p v
    have hvtop : v < c + L := hv.2.trans_le p.2.1.2.2
    have hq : q.1 = (p.1.1, v) := picardSectionPoint_of_mem p ⟨hv.1.le, hvtop.le⟩
    have hqlo : q.1.1 < q.1.2 := by rw [hq]; exact hv.1
    have hqhi : q.1.2 < c + L := by rw [hq]; exact hvtop
    have heq : (fun t => F (picardSectionPoint p t)) =ᶠ[𝓝 v] raw p.1.1 := by
      filter_upwards [Ioo_mem_nhds hv.1 hvtop] with t ht
      rw [hF (picardSectionPoint p t), picardSectionPoint_of_mem p ⟨ht.1.le, ht.2.le⟩]
    have hqd := hD q hqlo hqhi
    rw [hq] at hqd
    exact hqd.congr_of_eventuallyEq heq
  have hi : (∫ s in p.1.1..p.1.2, J (picardSectionPoint p s)) =
      F (picardSectionPoint p p.1.2) - F (picardSectionPoint p p.1.1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le p.2.1.2.1 hc.continuousOn hd
      (hj.intervalIntegrable p.1.1 p.1.2)
  change F p = F (picardSectionPoint p p.1.1) + ∫ s in p.1.1..p.1.2, J (picardSectionPoint p s)
  rw [hi, picardSectionPoint_self]
  abel

/-- At a valid incoming coordinate the ambient clamp equals the sectional clamp. -/
theorem picardClamp_sectionPoint (ha : 0 ≤ a) (haL : a ≤ L) (p : PicardDomain c a L) (v : ℝ) :
    picardClamp ha haL (p.1.1, v) = picardSectionPoint p v := by
  apply Subtype.ext
  change (max c (min (c + a) p.1.1), max (max c (min (c + a) p.1.1)) (min (c + L) v)) =
    (p.1.1, max p.1.1 (min (c + L) v))
  rw [min_eq_right p.2.2, max_eq_right p.2.1.1]
/-- The total representative has the stored outgoing derivative in section
interiors. Endpoint derivatives remain the within derivatives of the carrier. -/
theorem picardCarrierValue_hasDerivAt [CompleteSpace E] (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L E) (p : PicardDomain c a L)
    (hp : p.1.1 < p.1.2) (ht : p.1.2 < c + L) :
    HasDerivAt (picardCarrierValue ha haL z p.1.1) (z.1.2 p) p.1.2 := by
  have hd := picardCarrier_hasDerivWithinAt z p ⟨hp.le, ht.le⟩
  have hd' := hd.hasDerivAt (Icc_mem_nhds hp ht)
  change HasDerivAt (fun v => z.1.1 (picardClamp ha haL (p.1.1, v))) (z.1.2 p) p.1.2
  simp only [picardClamp_sectionPoint]
  simpa only [picardSectionPoint_self] using hd'

end EmcsfAcExtension.Local
