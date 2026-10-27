module

public import EmcsfAcExtension.Local.Broad.Setup
public import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Infra.HardyBV

/-! # Broad scalar averages and cancellation of constant backgrounds

These are identities in the frozen AC class, including complete characteristic
sections ending at the axis. The difference identity is charged_SF_new_version.tex:L5633–5672
and internal project record's endpoint-calculus repair.
-/

public section

open Set MeasureTheory Filter Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- The outgoing scalar equation is an ordinary derivative in the relative
interior of a complete outgoing segment of a frozen solution. -/
theorem hasDerivAt_phi_out {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v s : ℝ} (hseg : outSeg u u v ⊆ D)
    (hs : s ∈ Ioo u v) : HasDerivAt (S.phi u) (S.phiV u s) s := by
  have cr := (continuousOn_out_section hS.cont_r hseg).mono Ioo_subset_Icc_self
  have ct := (continuousOn_out_section hS.cont_theta hseg).mono Ioo_subset_Icc_self
  apply hasDerivAt_of_integralForm_interior hs
    (ct.div (continuous_ofReal.comp_continuousOn cr) (fun x hx => by
      change (S.r u x : ℂ) ≠ 0
      exact_mod_cast (hS.r_pos (u, x) (hseg ⟨rfl, hx.1.le, hx.2.le⟩) hx.1).ne'))
  intro c d hc hcd hd
  exact (hS.eq_out u c d hc hcd (by
    rintro p ⟨rfl, hp⟩
    exact hseg ⟨rfl, hc.le.trans hp.1, hp.2.trans hd.le⟩)).2.2.2.2.2.1

/-- Broad outgoing reconstruction: `r φ = ∫ λ a` on every complete outgoing
segment. No classical regularity or derivative envelope is required. -/
theorem outgoing_scalar_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) :
    (S.r u v : ℂ) * S.phi u v = ∫ x in u..v, (S.lam u x : ℂ) * S.a u x := by
  have cr := continuousOn_out_section hS.cont_r hseg
  have cp := continuousOn_out_section hS.cont_phi hseg
  have cl := continuousOn_out_section hS.cont_lam hseg
  have ca := continuousOn_out_section (IsSolution.cont_a hS) hseg
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv
    ((continuous_ofReal.comp_continuousOn cl).mul ca)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    ((continuous_ofReal.comp_continuousOn cr).mul cp)
    (f' := fun x => (S.lam u x : ℂ) * S.a u x) (fun x hx => ?_) hi
  · simpa [(hS.axis u (hseg ⟨rfl, le_rfl, huv⟩)).1] using hftc.symm
  · have hr := IsSolution.hasDerivAt_radius_out hS hseg hx
    have hp := hasDerivAt_phi_out hS hseg hx
    have hrC : (S.r u x : ℂ) ≠ 0 := by
      exact_mod_cast (hS.r_pos (u, x) (hseg ⟨rfl, hx.1.le, hx.2.le⟩) hx.1).ne'
    have hlC : (S.lam u x : ℂ) ≠ 0 := by
      exact_mod_cast (hS.lam_pos (u, x) (hseg ⟨rfl, hx.1.le, hx.2.le⟩)).ne'
    apply (hr.ofReal_comp.mul hp).congr_deriv
    dsimp [Fields.a, Fields.phiV]
    field_simp [hrC, hlC]

/-- The complete outgoing radius is exactly the integral of its positive
expansion, including the zero-length segment. -/
theorem outgoing_radius_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) :
    (∫ x in u..v, S.lam u x) = S.r u v := by
  simpa using outgoing_radius_moment hS huv hseg 0

/-- The incoming radius equation is an ordinary derivative in the interior of
a complete incoming segment in the frozen class. -/
theorem hasDerivAt_radius_in {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v x : ℝ} (hseg : inSeg u v v ⊆ D)
    (hx : x ∈ Ioo u v) : HasDerivAt (fun y => S.r y v) (S.nu x v) x := by
  apply hasDerivAt_of_integralForm_interior hx
    ((continuousOn_in_section hS.cont_nu hseg).mono Ioo_subset_Icc_self)
  intro a b ha hab hb
  exact (hS.eq_in a b v hab hb (by
    rintro p ⟨hp₁, hp₂, rfl⟩
    exact hseg ⟨ha.le.trans hp₁, hp₂.trans hb.le, rfl⟩)).1

/-- Exact incoming polynomial moments in the original null labels, with
Jacobian `-ν`. The coefficient is `1/(n+1)` uniformly in the solution and
segment. In particular `n=0` reconstructs the incoming radius. -/
theorem incoming_radius_moment {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : inSeg u v v ⊆ D) (n : ℕ) :
    (∫ x in u..v, (-S.nu x v) * S.r x v ^ n) = S.r u v ^ (n + 1) / (n + 1) := by
  have cr := continuousOn_in_section hS.cont_r hseg
  have cn := continuousOn_in_section hS.cont_nu hseg
  have hd : ∀ x ∈ Ioo u v, HasDerivAt
      (fun x => -(S.r x v ^ (n + 1) / (n + 1)))
      ((-S.nu x v) * S.r x v ^ n) x := by
    intro x hx
    convert (((hasDerivAt_radius_in hS hseg hx).pow (n + 1)).div_const
      (n + 1 : ℝ)).neg using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  have hi : IntervalIntegrable (fun x => (-S.nu x v) * S.r x v ^ n) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv (cn.neg.mul (cr.pow n))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    (((cr.pow (n + 1)).div_const _).neg) hd hi
  simpa [(hS.axis v (hseg ⟨huv, le_rfl, rfl⟩)).1] using hftc

/-- The incoming radius is the integral of `-ν` from the point to its axis
endpoint. This exact identity has no estimate constants. -/
theorem incoming_radius_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : inSeg u v v ⊆ D) : (∫ x in u..v, -S.nu x v) = S.r u v := by
  simpa using incoming_radius_moment hS huv hseg 0

/-- The incoming scalar equation is an ordinary interior derivative. The real
connection enters with its literal frozen covariant sign. -/
theorem hasDerivAt_phi_in {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v x : ℝ} (hseg : inSeg u v v ⊆ D)
    (hx : x ∈ Ioo u v) : HasDerivAt (fun y => S.phi y v) (S.phiU e x v) x := by
  have cr := (continuousOn_in_section hS.cont_r hseg).mono Ioo_subset_Icc_self
  have cx := (continuousOn_in_section hS.cont_xi hseg).mono Ioo_subset_Icc_self
  have cp := (continuousOn_in_section hS.cont_phi hseg).mono Ioo_subset_Icc_self
  have cA := (continuousOn_in_section hS.cont_A hseg).mono Ioo_subset_Icc_self
  have cf : ContinuousOn (fun y => S.phiU e y v) (Ioo u v) :=
    (cx.div (continuous_ofReal.comp_continuousOn cr) (fun y hy => by
      change (S.r y v : ℂ) ≠ 0
      exact_mod_cast (hS.r_pos (y, v) (hseg ⟨hy.1.le, hy.2.le, rfl⟩) hy.2).ne')).sub
        (((continuousOn_const.mul continuousOn_const).mul
          (continuous_ofReal.comp_continuousOn cA)).mul cp)
  apply hasDerivAt_of_integralForm_interior hx cf
  intro a b ha hab hb
  exact (hS.eq_in a b v hab hb (by
    rintro p ⟨hp₁, hp₂, rfl⟩
    exact hseg ⟨ha.le.trans hp₁, hp₂.trans hb.le, rfl⟩)).2.2.2.2.1

/-- Broad incoming scalar reconstruction in a parallel frame based at any
point of the complete section. The integrating factor has unit norm; no covariant or
ordinary variation bound is required for this exact identity. -/
theorem incoming_parallel_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v c : ℝ} (huv : u ≤ v)
    (hseg : inSeg u v v ⊆ D) (hc : c ∈ Icc u v) :
    (S.r u v : ℂ) * Complex.exp (I * e * (∫ y in c..u, S.A y v : ℝ)) * S.phi u v =
      ∫ x in u..v, (-S.nu x v : ℂ) *
        Complex.exp (I * e * (∫ y in c..x, S.A y v : ℝ)) * S.b x v := by
  have cr := continuousOn_in_section hS.cont_r hseg
  have cp := continuousOn_in_section hS.cont_phi hseg
  have cn := continuousOn_in_section hS.cont_nu hseg
  have cA := continuousOn_in_section hS.cont_A hseg
  have cb := continuousOn_in_section (IsSolution.cont_b hS) hseg
  have iA := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cA
  have cI := iA.absolutelyContinuousOnInterval_intervalIntegral (Icc_subset_uIcc hc) |>.continuousOn
  rw [uIcc_of_le huv] at cI
  let P := fun x => Complex.exp (I * e * (∫ y in c..x, S.A y v : ℝ))
  have cP : ContinuousOn P (Icc u v) := Complex.continuous_exp.comp_continuousOn
    ((continuousOn_const.mul continuousOn_const).mul (continuous_ofReal.comp_continuousOn cI))
  have hd : ∀ x ∈ Ioo u v, HasDerivAt
      (fun y => (S.r y v : ℂ) * P y * S.phi y v)
      ((S.nu x v : ℂ) * P x * S.b x v) x := by
    intro x hx
    have hr := hasDerivAt_radius_in hS hseg hx
    have hp := hasDerivAt_phi_in hS hseg hx
    have cAo := cA.mono Ioo_subset_Icc_self
    have hI := intervalIntegral.integral_hasDerivAt_right
      (iA.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc hc)
        (Icc_subset_uIcc ⟨hx.1.le, hx.2.le⟩)))
      (cAo.stronglyMeasurableAtFilter isOpen_Ioo x hx)
      (cAo.continuousAt (isOpen_Ioo.mem_nhds hx))
    have hP := (hI.ofReal_comp.const_mul (I * (e : ℂ))).cexp
    have hrC : (S.r x v : ℂ) ≠ 0 := by
      exact_mod_cast (hS.r_pos (x, v) (hseg ⟨hx.1.le, hx.2.le, rfl⟩) hx.2).ne'
    have hnC : (S.nu x v : ℂ) ≠ 0 := by
      exact_mod_cast (hS.nu_neg (x, v) (hseg ⟨hx.1.le, hx.2.le, rfl⟩)).ne
    apply ((hr.ofReal_comp.mul hP).mul hp).congr_deriv
    dsimp [Fields.b, Fields.phiU, P]
    field_simp [hrC, hnC]
    ring
  have hi : IntervalIntegrable (fun x => (S.nu x v : ℂ) * P x * S.b x v) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv
      (((continuous_ofReal.comp_continuousOn cn).mul cP).mul cb)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    (((continuous_ofReal.comp_continuousOn cr).mul cP).mul cp) hd hi
  have hneg : (∫ x in u..v, (-S.nu x v : ℂ) * P x * S.b x v) =
      -(∫ x in u..v, (S.nu x v : ℂ) * P x * S.b x v) := by
    simp only [neg_mul, intervalIntegral.integral_neg]
  rw [hneg, hftc]
  simp [P, (hS.axis v (hseg ⟨huv, le_rfl, rfl⟩)).1]

/-- A positive lower expansion bound gives the matching linear lower radius
bound. The numerical coefficient is exactly the specified box constant. -/
theorem outgoing_radius_lower {e c : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) (hc : ∀ x ∈ Icc u v, c ≤ S.lam u x) :
    c * (v - u) ≤ S.r u v := by
  rw [← outgoing_radius_reconstruction hS huv hseg]
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv
    (continuousOn_out_section hS.cont_lam hseg)
  simpa [mul_comm] using intervalIntegral.integral_mono_on huv
    (intervalIntegrable_const (c := c)) hi hc

/-- An upper expansion bound gives the matching linear upper radius bound,
with the exact specified box coefficient, uniformly in the section. -/
theorem outgoing_radius_upper {e C : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) (hC : ∀ x ∈ Icc u v, S.lam u x ≤ C) :
    S.r u v ≤ C * (v - u) := by
  rw [← outgoing_radius_reconstruction hS huv hseg]
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv
    (continuousOn_out_section hS.cont_lam hseg)
  simpa [mul_comm] using intervalIntegral.integral_mono_on huv hi
    (intervalIntegrable_const (c := C)) hC

/-- The geometric distance is finite for two frozen solutions on a compact
triangle with positive lower expansion bound `c`. The relative-radius term is
controlled by integrating the expansion difference, including at the axis. -/
theorem geometry_distance_ne_top {s t e c : ℝ} {S₁ S₂ : Fields}
    (hS₁ : IsSolution e S₁ (triangle s t)) (hS₂ : IsSolution e S₂ (triangle s t))
    (hc : 0 < c) (hl : ∀ p ∈ triangle s t, c ≤ S₁.lam p.1 p.2) :
    geometry_distance s t S₁ S₂ ≠ ⊤ := by
  have hcont := ((hS₁.cont_lam.sub hS₂.cont_lam).abs).add
    (hS₁.cont_nu.sub hS₂.cont_nu).abs
  obtain ⟨B, hB⟩ := (isCompact_triangle s t).bddAbove_image hcont
  let K := max B 0
  have hK : 0 ≤ K := le_max_right _ _
  have hbound p (hp : p ∈ triangle s t) :
      |S₁.lam p.1 p.2 - S₂.lam p.1 p.2| + |S₁.nu p.1 p.2 - S₂.nu p.1 p.2| ≤ K :=
    (hB (mem_image_of_mem _ hp)).trans (le_max_left _ _)
  apply ne_top_of_le_ne_top (show ENNReal.ofReal (K + K / c) ≠ ⊤ from
    ENNReal.ofReal_ne_top)
  apply iSup₂_le
  rintro ⟨u, v⟩ hp
  apply ENNReal.ofReal_le_ofReal
  apply add_le_add (hbound (u, v) hp)
  rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
  · subst v
    simp only [(hS₁.axis u hp).1, div_zero]
    exact div_nonneg hK hc.le
  · have seg : outSeg u u v ⊆ triangle s t := by
      rintro p ⟨rfl, hx⟩
      exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
    have hr := hS₁.r_pos (u, v) hp huv
    have hlower := outgoing_radius_lower hS₁ huv.le seg (fun x hx => hl (u, x) (seg ⟨rfl, hx⟩))
    have hdiff : |S₁.r u v - S₂.r u v| ≤ K * (v - u) := by
      rw [← outgoing_radius_reconstruction hS₁ huv.le seg,
        ← outgoing_radius_reconstruction hS₂ huv.le seg,
        ← intervalIntegral.integral_sub
          (ContinuousOn.intervalIntegrable_of_Icc huv.le
            (continuousOn_out_section hS₁.cont_lam seg))
          (ContinuousOn.intervalIntegrable_of_Icc huv.le
            (continuousOn_out_section hS₂.cont_lam seg)), ← Real.norm_eq_abs]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := u) (b := v) (C := K) (f := fun x => S₁.lam u x - S₂.lam u x) (fun x hx => by
          rw [uIoc_of_le huv.le] at hx
          rw [Real.norm_eq_abs]
          exact (le_add_of_nonneg_right (abs_nonneg _)).trans
            (hbound (u, x) (seg ⟨rfl, hx.1.le, hx.2⟩)))
      simpa [abs_of_nonneg (sub_nonneg.mpr huv.le)] using h
    apply (div_le_iff₀ hr).mpr
    calc
      _ ≤ K * (v - u) := hdiff
      _ = (K / c) * (c * (v - u)) := by field_simp
      _ ≤ (K / c) * S₁.r u v :=
        mul_le_mul_of_nonneg_left hlower (div_nonneg hK hc.le)

/-- The expansion difference is bounded by the finite real geometric distance.
Only the positive-radius sign is used to compare its summand to the distance. -/
theorem abs_lam_sub_le_geometry_distance {s t e u v : ℝ} {S₁ S₂ : Fields}
    (hS₁ : IsSolution e S₁ (triangle s t))
    (hfin : geometry_distance s t S₁ S₂ ≠ ⊤) (hp : (u, v) ∈ triangle s t) :
    |S₁.lam u v - S₂.lam u v| ≤ (geometry_distance s t S₁ S₂).toReal := by
  have hr : 0 ≤ S₁.r u v := by
    rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
    · subst v; rw [(hS₁.axis u hp).1]
    · exact (hS₁.r_pos (u, v) hp huv).le
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
  calc
    _ ≤ ENNReal.ofReal (|S₁.lam u v - S₂.lam u v| +
        |S₁.nu u v - S₂.nu u v| + |S₁.r u v - S₂.r u v| / S₁.r u v) :=
      ENNReal.ofReal_le_ofReal (by
        linarith [abs_nonneg (S₁.nu u v - S₂.nu u v),
          div_nonneg (abs_nonneg (S₁.r u v - S₂.r u v)) hr])
    _ ≤ _ := le_iSup₂_of_le (u, v) hp le_rfl

/-- The incoming expansion difference is bounded by the finite geometric
distance, with exact universal coefficient one, including on the axis. -/
theorem abs_nu_sub_le_geometry_distance {s t e u v : ℝ} {S₁ S₂ : Fields}
    (hS₁ : IsSolution e S₁ (triangle s t))
    (hfin : geometry_distance s t S₁ S₂ ≠ ⊤) (hp : (u, v) ∈ triangle s t) :
    |S₁.nu u v - S₂.nu u v| ≤ (geometry_distance s t S₁ S₂).toReal := by
  have hr : 0 ≤ S₁.r u v := by
    rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
    · subst v; rw [(hS₁.axis u hp).1]
    · exact (hS₁.r_pos (u, v) hp huv).le
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
  calc
    _ ≤ ENNReal.ofReal (|S₁.lam u v - S₂.lam u v| +
        |S₁.nu u v - S₂.nu u v| + |S₁.r u v - S₂.r u v| / S₁.r u v) :=
      ENNReal.ofReal_le_ofReal (by
        linarith [abs_nonneg (S₁.lam u v - S₂.lam u v),
          div_nonneg (abs_nonneg (S₁.r u v - S₂.r u v)) hr])
    _ ≤ _ := le_iSup₂_of_le (u, v) hp le_rfl

/-- At positive radius, the relative radius difference is bounded by the
finite geometric distance. Its coefficient is exactly one, uniformly in all
parameters. The zero-axis case follows from the two regular-axis conditions. -/
theorem abs_radius_sub_le_geometry_distance_mul_radius {s t e u v : ℝ} {S₁ S₂ : Fields}
    (hS₁ : IsSolution e S₁ (triangle s t)) (hS₂ : IsSolution e S₂ (triangle s t))
    (hfin : geometry_distance s t S₁ S₂ ≠ ⊤) (hp : (u, v) ∈ triangle s t) :
    |S₁.r u v - S₂.r u v| ≤ (geometry_distance s t S₁ S₂).toReal * S₁.r u v := by
  rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
  · subst v
    simp [(hS₁.axis u hp).1, (hS₂.axis u hp).1]
  · have hr := hS₁.r_pos (u, v) hp huv
    apply (div_le_iff₀ hr).mp
    apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
    calc
      _ ≤ ENNReal.ofReal (|S₁.lam u v - S₂.lam u v| +
          |S₁.nu u v - S₂.nu u v| + |S₁.r u v - S₂.r u v| / S₁.r u v) :=
        ENNReal.ofReal_le_ofReal (by
          linarith [abs_nonneg (S₁.lam u v - S₂.lam u v),
            abs_nonneg (S₁.nu u v - S₂.nu u v)])
      _ ≤ _ := le_iSup₂_of_le (u, v) hp le_rfl

/-- [node restart-stab-broad-uniqueness#scalar-average-difference-identity]
Exact subtraction of two broad radial averages, charged_SF_new_version.tex:L5633–5672.
The constant scalar background cancels before any norm is taken. This identity
has no constants and needs only the two complete outgoing segments. -/
theorem scalar_average_difference_identity {e : ℝ} {S₁ S₂ : Fields}
    {D₁ D₂ : Set (ℝ × ℝ)} (hS₁ : IsSolution e S₁ D₁) (hS₂ : IsSolution e S₂ D₂)
    {u v : ℝ} (huv : u < v) (hseg₁ : outSeg u u v ⊆ D₁)
    (hseg₂ : outSeg u u v ⊆ D₂) :
    S₁.phi u v - S₂.phi u v =
      (S₁.r u v : ℂ)⁻¹ *
        (∫ x in u..v, (S₁.lam u x : ℂ) * (S₁.a u x - S₂.a u x)) +
      (S₁.r u v : ℂ)⁻¹ *
        ∫ x in u..v, ((S₁.lam u x - S₂.lam u x : ℝ) : ℂ) *
          (S₂.a u x - S₂.phi u v) := by
  have cl₁ := continuous_ofReal.comp_continuousOn
    (continuousOn_out_section hS₁.cont_lam hseg₁)
  have cl₂ := continuous_ofReal.comp_continuousOn
    (continuousOn_out_section hS₂.cont_lam hseg₂)
  have ca₁ := continuousOn_out_section (IsSolution.cont_a hS₁) hseg₁
  have ca₂ := continuousOn_out_section (IsSolution.cont_a hS₂) hseg₂
  have i₁ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le (cl₁.mul ca₁)
  have i₂ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le (cl₂.mul ca₂)
  have i₁₂ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le (cl₁.mul ca₂)
  have il := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le (cl₁.sub cl₂)
  have il₁ : IntervalIntegrable (fun x => (S₁.lam u x : ℂ)) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv.le cl₁
  have il₂ : IntervalIntegrable (fun x => (S₂.lam u x : ℂ)) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv.le cl₂
  change IntervalIntegrable (fun x => (S₁.lam u x : ℂ) * S₁.a u x) volume u v at i₁
  change IntervalIntegrable (fun x => (S₂.lam u x : ℂ) * S₂.a u x) volume u v at i₂
  change IntervalIntegrable (fun x => (S₁.lam u x : ℂ) * S₂.a u x) volume u v at i₁₂
  change IntervalIntegrable (fun x => (S₁.lam u x : ℂ) - (S₂.lam u x : ℂ)) volume u v at il
  have idiff : IntervalIntegrable (fun x =>
      (S₁.lam u x : ℂ) * S₂.a u x - (S₂.lam u x : ℂ) * S₂.a u x) volume u v := i₁₂.sub i₂
  have ic : IntervalIntegrable (fun x => ((S₁.lam u x : ℂ) - (S₂.lam u x : ℂ)) *
      S₂.phi u v) volume u v := il.mul_const _
  have heq :
      (∫ x in u..v, (S₁.lam u x : ℂ) * (S₁.a u x - S₂.a u x)) +
        (∫ x in u..v, ((S₁.lam u x - S₂.lam u x : ℝ) : ℂ) *
          (S₂.a u x - S₂.phi u v)) =
      (S₁.r u v : ℂ) * (S₁.phi u v - S₂.phi u v) := by
    simp_rw [Complex.ofReal_sub, mul_sub]
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub i₁ i₁₂,
      intervalIntegral.integral_sub idiff (by simpa only [sub_mul] using ic),
      intervalIntegral.integral_sub i₁₂ i₂,
      intervalIntegral.integral_sub (il₁.mul_const _) (il₂.mul_const _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      outgoing_radius_reconstruction hS₁ huv.le hseg₁,
      outgoing_radius_reconstruction hS₂ huv.le hseg₂,
      ← outgoing_scalar_reconstruction hS₁ huv.le hseg₁,
      ← outgoing_scalar_reconstruction hS₂ huv.le hseg₂]
    ring
  have hr : (S₁.r u v : ℂ) ≠ 0 := by
    exact_mod_cast (hS₁.r_pos (u, v) (hseg₁ ⟨rfl, huv.le, le_rfl⟩) huv).ne'
  rw [← mul_add, heq, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]

private theorem norm_weighted_integral_le {u v M : ℝ} {w : ℝ → ℝ} {f : ℝ → ℂ}
    (huv : u ≤ v) (hw : ContinuousOn w (Icc u v))
    (hw0 : ∀ x ∈ Icc u v, 0 ≤ w x) (hf : ContinuousOn f (Icc u v))
    (hM : ∀ x ∈ Icc u v, ‖f x‖ ≤ M) :
    ‖∫ x in u..v, (w x : ℂ) * f x‖ ≤ (∫ x in u..v, w x) * M := by
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv
    ((continuous_ofReal.comp_continuousOn hw).mul hf)
  have hwi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv hw
  calc
    _ ≤ ∫ x in u..v, ‖(w x : ℂ) * f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm huv
    _ ≤ ∫ x in u..v, w x * M := by
      apply intervalIntegral.integral_mono_on huv hi.norm (hwi.mul_const M)
      intro x hx
      change ‖(w x : ℂ) * f x‖ ≤ w x * M
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x hx)]
      exact mul_le_mul_of_nonneg_left (hM x hx) (hw0 x hx)
    _ = _ := intervalIntegral.integral_mul_const M w

/-- The parenthesis in the scalar comparison formula is bounded by the
outgoing oscillation, independently of the scalar background. Its coefficient
is exactly one, uniformly in the solution, interval, and positive weight. -/
theorem scalar_average_bracket_bound {e ε : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v x : ℝ} (huv : u < v)
    (hseg : outSeg u u v ⊆ D) (hx : x ∈ Icc u v)
    (hosc : ∀ y ∈ Icc u v, ∀ z ∈ Icc u v, ‖S.a u y - S.a u z‖ ≤ ε) :
    ‖S.a u x - S.phi u v‖ ≤ ε := by
  have cl := continuousOn_out_section hS.cont_lam hseg
  have ca := continuousOn_out_section (IsSolution.cont_a hS) hseg
  have hr : 0 < S.r u v := hS.r_pos (u, v) (hseg ⟨rfl, huv.le, le_rfl⟩) huv
  have hrC : (S.r u v : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have il : IntervalIntegrable (fun y => (S.lam u y : ℂ)) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv.le (continuous_ofReal.comp_continuousOn cl)
  have ila : IntervalIntegrable (fun y => (S.lam u y : ℂ) * S.a u y) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv.le ((continuous_ofReal.comp_continuousOn cl).mul ca)
  have heq : (∫ y in u..v, (S.lam u y : ℂ) * (S.a u x - S.a u y)) =
      (S.r u v : ℂ) * (S.a u x - S.phi u v) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (il.mul_const _) ila,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      outgoing_radius_reconstruction hS huv.le hseg,
      ← outgoing_scalar_reconstruction hS huv.le hseg]
  have hb := norm_weighted_integral_le (f := fun y => S.a u x - S.a u y) huv.le cl
    (fun y hy => (hS.lam_pos (u, y) (hseg ⟨rfl, hy⟩)).le)
    (continuousOn_const.sub ca) (fun y hy => hosc x hx y hy)
  rw [outgoing_radius_reconstruction hS huv.le hseg, heq, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hb
  exact (mul_le_mul_iff_right₀ hr).mp hb

/-- [node restart-stab-broad-uniqueness#scalar-average-difference-bound]
Uniform scalar comparison with geometric coefficient `ε`,
charged_SF_new_version.tex:L5635–5672. For each fixed positive lower box constant `c`,
`K` depends only on `c`, independently of the triangle, coupling, scalar size,
BV budget, oscillation size, and competing frozen solutions. -/
theorem scalar_average_difference_bound (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e ε : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      0 ≤ ε → (∀ p ∈ triangle s t, c ≤ S₁.lam p.1 p.2) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      ∀ u v, (u, v) ∈ triangle s t →
        ‖S₁.phi u v - S₂.phi u v‖ ≤ K *
          ((normalized_field_distance s t S₁ S₂).toReal +
            ε * (geometry_distance s t S₁ S₂).toReal) := by
  refine ⟨1 + c⁻¹, by positivity, ?_⟩
  intro s t e ε S₁ S₂ hS₁ hS₂ hε hl hosc u v hp
  let d := (normalized_field_distance s t S₁ S₂).toReal
  let g := (geometry_distance s t S₁ S₂).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hg : 0 ≤ g := ENNReal.toReal_nonneg
  have hfin := geometry_distance_ne_top hS₁ hS₂ hc hl
  have hcoef : 1 ≤ 1 + c⁻¹ := le_add_of_nonneg_right (inv_nonneg.mpr hc.le)
  rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
  · subst v
    rw [← (hS₁.axis u hp).2.2.2.2.1, ← (hS₂.axis u hp).2.2.2.2.1]
    exact (norm_a_sub_le_distance hS₁ hS₂ hp).trans
      ((le_add_of_nonneg_right (mul_nonneg hε hg)).trans
        (le_mul_of_one_le_left (by positivity) hcoef))
  · have seg : outSeg u u v ⊆ triangle s t := by
      rintro p ⟨rfl, hx⟩
      exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
    have hr := hS₁.r_pos (u, v) hp huv
    have hrC : (S₁.r u v : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hi₁ : ‖∫ x in u..v, (S₁.lam u x : ℂ) * (S₁.a u x - S₂.a u x)‖ ≤
        S₁.r u v * d := by
      rw [← outgoing_radius_reconstruction hS₁ huv.le seg]
      exact norm_weighted_integral_le huv.le
        (continuousOn_out_section hS₁.cont_lam seg)
        (fun x hx => (hS₁.lam_pos (u, x) (seg ⟨rfl, hx⟩)).le)
        ((continuousOn_out_section (IsSolution.cont_a hS₁) seg).sub
          (continuousOn_out_section (IsSolution.cont_a hS₂) seg))
        (fun x hx => norm_a_sub_le_distance hS₁ hS₂ (seg ⟨rfl, hx⟩))
    have hi₂ : ‖∫ x in u..v, ((S₁.lam u x - S₂.lam u x : ℝ) : ℂ) *
        (S₂.a u x - S₂.phi u v)‖ ≤ g * ε * (v - u) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := u) (b := v) (C := g * ε)
        (f := fun x => ((S₁.lam u x - S₂.lam u x : ℝ) : ℂ) *
          (S₂.a u x - S₂.phi u v)) (fun x hx => by
          rw [uIoc_of_le huv.le] at hx
          have hx' : x ∈ Icc u v := ⟨hx.1.le, hx.2⟩
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul
            (abs_lam_sub_le_geometry_distance hS₁ hfin (seg ⟨rfl, hx'⟩))
            (scalar_average_bracket_bound hS₂ huv seg hx' (hosc u v hp))
            (norm_nonneg _) hg)
      simpa [abs_of_nonneg (sub_nonneg.mpr huv.le)] using h
    have hlower := outgoing_radius_lower hS₁ huv.le seg (fun x hx => hl (u, x) (seg ⟨rfl, hx⟩))
    have hratio : (v - u) / S₁.r u v ≤ c⁻¹ := by
      apply (div_le_iff₀ hr).mpr
      calc
        _ = c⁻¹ * (c * (v - u)) := by field_simp
        _ ≤ c⁻¹ * S₁.r u v := mul_le_mul_of_nonneg_left hlower (inv_nonneg.mpr hc.le)
    calc
      _ ≤ ‖(S₁.r u v : ℂ)⁻¹ *
            (∫ x in u..v, (S₁.lam u x : ℂ) * (S₁.a u x - S₂.a u x))‖ +
          ‖(S₁.r u v : ℂ)⁻¹ *
            (∫ x in u..v, ((S₁.lam u x - S₂.lam u x : ℝ) : ℂ) *
              (S₂.a u x - S₂.phi u v))‖ := by
        rw [scalar_average_difference_identity hS₁ hS₂ huv seg seg]
        exact norm_add_le _ _
      _ ≤ (S₁.r u v)⁻¹ * (S₁.r u v * d) +
          (S₁.r u v)⁻¹ * (g * ε * (v - u)) := by
        simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        exact add_le_add (mul_le_mul_of_nonneg_left hi₁ (inv_nonneg.mpr hr.le))
          (mul_le_mul_of_nonneg_left hi₂ (inv_nonneg.mpr hr.le))
      _ = d + (ε * g) * ((v - u) / S₁.r u v) := by field_simp
      _ ≤ d + (ε * g) * c⁻¹ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hratio (mul_nonneg hε hg))
      _ ≤ (1 + c⁻¹) * (d + ε * g) := by
        have : 0 ≤ c⁻¹ * d + ε * g := by positivity
        nlinarith only [this]

/-- The two oscillatory ratio differences are controlled by the normalized
distance and scalar difference, with exact universal coefficient one. This
uses only the literal frozen definitions of `a,b`, without derivatives. -/
theorem norm_ratio_sub_le_distance_add_scalar {s t e u v : ℝ} {S₁ S₂ : Fields}
    (hS₁ : IsSolution e S₁ (triangle s t)) (hS₂ : IsSolution e S₂ (triangle s t))
    (hp : (u, v) ∈ triangle s t) :
    ‖S₁.theta u v / S₁.lam u v - S₂.theta u v / S₂.lam u v‖ ≤
        (normalized_field_distance s t S₁ S₂).toReal + ‖S₁.phi u v - S₂.phi u v‖ ∧
      ‖S₁.xi u v / S₁.nu u v - S₂.xi u v / S₂.nu u v‖ ≤
        (normalized_field_distance s t S₁ S₂).toReal + ‖S₁.phi u v - S₂.phi u v‖ := by
  constructor
  · have heq : S₁.theta u v / S₁.lam u v - S₂.theta u v / S₂.lam u v =
        (S₁.a u v - S₂.a u v) - (S₁.phi u v - S₂.phi u v) := by
      dsimp [Fields.a]
      abel
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add (norm_a_sub_le_distance hS₁ hS₂ hp) le_rfl)
  · have heq : S₁.xi u v / S₁.nu u v - S₂.xi u v / S₂.nu u v =
        (S₁.b u v - S₂.b u v) - (S₁.phi u v - S₂.phi u v) := by
      dsimp [Fields.b]
      abel
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add (norm_b_sub_le_distance hS₁ hS₂ hp) le_rfl)

end EmcsfAcExtension.Local.Broad
