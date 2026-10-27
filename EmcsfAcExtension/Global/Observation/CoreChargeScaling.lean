module

public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Global.Observation.CoreCharge

/-! # Core estimates retaining the physical scale

The original solution is kept throughout. A positive scale `s` converts
the physical mass bound to `2s`; the normalized radius is `r/s`.
This split keeps the core development below 600 lines per module.
Source: charged_SF_new_version.tex:L2110–2144; internal project record (C1)–(C3).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

private theorem scale_over_boundary_le_sqrt_ratio {s r b : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hb : 0 < b) (hsb : s ≤ b) (hrb : r ≤ b) :
    s / b ≤ Real.sqrt s / Real.sqrt r := by
  have hprod : s * r ≤ b ^ 2 := by
    simpa only [pow_two] using mul_le_mul hsb hrb hr.le hb.le
  have hsq : (s / b) ^ 2 ≤ s / r := by
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hb) hr).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hprod hs.le]
  have he := Real.le_sqrt_of_sq_le hsq
  rwa [Real.sqrt_div hs.le] at he

/-- [internal]
The original physical solution obeys the normalized core scalar estimate
with coefficient `2+2/sqrt δ`, depending only on the gap and uniformly in
scale, radius, coupling, background and solution. No chart `IsSolution`
or supremum at the regular axis is used. -/
theorem co_scalar_core_of_physical_boundary_bound
    {e δ s b : ℝ} {H : ℂ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hδ : 0 < δ) (hs : 0 < s) (hsb : s ≤ b)
    {u a v : ℝ} (hua : u < a) (hav : a ≤ v) (hseg : outSeg u u v ⊆ D)
    (hrb : S.r u v = b) (hm : S.m u v ≤ 2 * s)
    (hgap : ∀ x ∈ Icc u v, δ ≤ 1 - S.mu u x)
    (hφb : ‖S.phi u v‖ ≤ ‖H‖ + 2 * s / b) :
    ‖S.phi u a‖ ≤ ‖H‖ + (2 + 2 / Real.sqrt δ) / Real.sqrt (S.r u a / s) := by
  have hb : 0 < b := hs.trans_le hsb
  have hr := hS.r_pos (u, a) (hseg ⟨rfl, hua.le, hav⟩) hua
  have hrb' : S.r u a ≤ b := by
    rw [← hrb]
    exact Observation.radius_le_boundary hS hseg ⟨hua.le, hav⟩
  have hroot := scale_over_boundary_le_sqrt_ratio hs hr hb hsb hrb'
  have hm0 := (Observation.mass_bounds_on_full_section hS (hua.trans_le hav).le hseg
    ⟨(hua.trans_le hav).le, le_rfl⟩).1
  have henergy : Real.sqrt (2 * S.m u v / δ) ≤ 2 * Real.sqrt s / Real.sqrt δ := by
    calc
      _ ≤ Real.sqrt (4 * s / δ) := Real.sqrt_le_sqrt
        (div_le_div_of_nonneg_right (by linarith only [hm]) hδ.le)
      _ = _ := by
        rw [Real.sqrt_div (by positivity : 0 ≤ 4 * s), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
  have he := Observation.physical_radial_scalar_bound hS hδ hua hav hseg hgap
  calc
    _ ≤ ‖S.phi u v‖ + Real.sqrt (2 * S.m u v / δ) / Real.sqrt (S.r u a) := he
    _ ≤ (‖H‖ + 2 * s / b) +
        (2 * Real.sqrt s / Real.sqrt δ) / Real.sqrt (S.r u a) :=
      add_le_add hφb (div_le_div_of_nonneg_right henergy (Real.sqrt_nonneg _))
    _ ≤ (‖H‖ + 2 * (Real.sqrt s / Real.sqrt (S.r u a))) +
        (2 * Real.sqrt s / Real.sqrt δ) / Real.sqrt (S.r u a) := by
      have hh : 2 * s / b ≤ 2 * (Real.sqrt s / Real.sqrt (S.r u a)) := by
        simpa only [mul_div_assoc] using!
          mul_le_mul_of_nonneg_left hroot (show (0 : ℝ) ≤ 2 by norm_num)
      linarith only [hh]
    _ = _ := by
      rw [Real.sqrt_div hr.le]
      field_simp
      ring

/-- [internal]
The dimensionless charged radial factor is at most twice the square of
the physical charged parameter. Its coefficient two is universal; the
scale and radius are only required to be at most the outer radius. -/
theorem Observation.charged_radial_factor_of_physical_scale
    (e b s r : ℝ) (H : ℂ) (hb : 0 ≤ b) (_hs : 0 ≤ s) (hr : 0 ≤ r)
    (hsb : s ≤ b) (hrb : r ≤ b) :
    e ^ 2 * (‖H‖ ^ 2 * r ^ 2 + s * r) ≤ 2 * (|e| * b * (1 + ‖H‖)) ^ 2 := by
  have hsr : s * r ≤ b ^ 2 := by simpa only [pow_two] using mul_le_mul hsb hrb hr hb
  have hr2 : r ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hr hrb 2
  have hH : ‖H‖ ^ 2 ≤ (1 + ‖H‖) ^ 2 := by nlinarith only [norm_nonneg H]
  have hH1 : 1 ≤ (1 + ‖H‖) ^ 2 := by nlinarith only [norm_nonneg H]
  have h₁ := mul_le_mul hH hr2 (sq_nonneg r) (sq_nonneg (1 + ‖H‖))
  have h₂ : s * r ≤ b ^ 2 * (1 + ‖H‖) ^ 2 :=
    hsr.trans (by simpa using mul_le_mul_of_nonneg_left hH1 (sq_nonneg b))
  have he := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (sq_nonneg e)
  convert he using 1
  simp only [mul_pow, sq_abs]
  ring

/-- [internal]
The core-charge constant depends only on the positive gap. It is chosen
before all physical data; the estimate keeps the original solution and
the explicit physical scale. -/
theorem co_core_charge_of_physical_boundary_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (e s b : ℝ) (H : ℂ) (S : Fields) (D : Set (ℝ × ℝ)),
        IsSolution e S D → 0 < s → s ≤ b →
      ∀ u v, u < v → outSeg u u v ⊆ D → S.r u v = b →
        (∀ x ∈ Icc u v, δ ≤ 1 - S.mu u x) → S.m u v ≤ 2 * s →
        ‖S.phi u v‖ ≤ ‖H‖ + 2 * s / b →
      ∀ x ∈ Ioc u v, S.Q u x ^ 2 ≤
        C * e ^ 2 * S.m u x * (‖H‖ ^ 2 * S.r u x ^ 3 + s * S.r u x ^ 2) := by
  let B := 2 + 2 / Real.sqrt δ
  let A := 4 / (3 * δ)
  let K := 2 * B ^ 2 / δ
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨A + K, add_pos_of_pos_of_nonneg hA hK, ?_⟩
  intro e s b H S D hS hs hsb u v huv hseg hrb hgap hm hboundary x hx
  have hxseg : outSeg u u x ⊆ D := fun p hp => hseg ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩
  have hφ : ∀ y ∈ Ioc u x, ‖S.phi u y‖ ≤
      ‖H‖ + (B * Real.sqrt s) / Real.sqrt (S.r u y) := by
    intro y hy
    have hr := hS.r_pos (u, y) (hseg ⟨rfl, hy.1.le, hy.2.trans hx.2⟩) hy.1
    have hh := co_scalar_core_of_physical_boundary_bound hS hδ hs hsb
      hy.1 (hy.2.trans hx.2) hseg hrb hm hgap hboundary
    convert hh using 1
    rw [Real.sqrt_div hr.le]
    dsimp [B]
    field_simp
  have hq := Observation.core_charge_of_scalar_envelope hS hδ (norm_nonneg H)
    (show 0 ≤ B * Real.sqrt s by dsimp [B]; positivity) hx.1 hxseg
    (fun y hy => hgap y ⟨hy.1, hy.2.trans hx.2⟩) hφ
  rw [mul_pow, Real.sq_sqrt hs.le] at hq
  have hm0 := (Observation.mass_bounds_on_full_section hS hx.1.le hxseg ⟨hx.1.le, le_rfl⟩).1
  have hr := hS.r_pos (u, x) (hseg ⟨rfl, hx.1.le, hx.2⟩) hx.1
  have hf₁ : 0 ≤ ‖H‖ ^ 2 * S.r u x ^ 3 := mul_nonneg (sq_nonneg _) (pow_nonneg hr.le _)
  have hf₂ : 0 ≤ s * S.r u x ^ 2 := mul_nonneg hs.le (sq_nonneg _)
  have hsum : A * (‖H‖ ^ 2 * S.r u x ^ 3) + K * (s * S.r u x ^ 2) ≤
      (A + K) * (‖H‖ ^ 2 * S.r u x ^ 3 + s * S.r u x ^ 2) := by
    nlinarith only [mul_nonneg hK hf₁, mul_nonneg hA.le hf₂]
  have he := mul_le_mul_of_nonneg_left hsum (mul_nonneg (sq_nonneg e) hm0)
  apply hq.trans
  convert he using 1 <;> dsimp [A, K] <;> ring

/-- [internal]
The relative-charge constant depends only on the gap, uniformly in the
physical scale, outer radius, coupling, scalar background and solution.
The charged parameter is the physical invariant `|e| b (1+‖H‖)`. -/
theorem co_charge_relative_of_physical_boundary_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (e s b : ℝ) (H : ℂ) (S : Fields) (D : Set (ℝ × ℝ)),
        IsSolution e S D → 0 < s → s ≤ b →
      ∀ u v, u < v → outSeg u u v ⊆ D → S.r u v = b →
        (∀ x ∈ Icc u v, δ ≤ 1 - S.mu u x) → S.m u v ≤ 2 * s →
        ‖S.phi u v‖ ≤ ‖H‖ + 2 * s / b →
      ∀ x ∈ Ioc u v, S.Q u x ^ 2 / S.r u x ^ 2 ≤
        C * (|e| * b * (1 + ‖H‖)) ^ 2 * S.mu u x := by
  obtain ⟨C, hC, hcore⟩ := co_core_charge_of_physical_boundary_bound hδ
  refine ⟨C, hC, ?_⟩
  intro e s b H S D hS hs hsb u v huv hseg hrb hgap hm hboundary x hx
  have hq := hcore e s b H S D hS hs hsb u v huv hseg hrb hgap hm hboundary x hx
  have hr := hS.r_pos (u, x) (hseg ⟨rfl, hx.1.le, hx.2⟩) hx.1
  have hm0 := (Observation.mass_bounds_on_full_section hS huv.le hseg ⟨hx.1.le, hx.2⟩).1
  have hμ : 0 ≤ S.mu u x := by dsimp [Fields.mu]; positivity
  have hrb' : S.r u x ≤ b := by
    rw [← hrb]
    exact Observation.radius_le_boundary hS hseg ⟨hx.1.le, hx.2⟩
  have hf := Observation.charged_radial_factor_of_physical_scale e b s (S.r u x) H
    (hs.le.trans hsb) hs.le hr.le hsb hrb'
  calc
    _ ≤ (C / 2) * S.mu u x *
        (e ^ 2 * (‖H‖ ^ 2 * S.r u x ^ 2 + s * S.r u x)) := by
      apply (div_le_div_of_nonneg_right hq (sq_nonneg _)).trans_eq
      dsimp [Fields.mu]
      field_simp
    _ ≤ (C / 2) * S.mu u x * (2 * (|e| * b * (1 + ‖H‖)) ^ 2) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by ring

/-- [internal]
A charged threshold is chosen using only the gap, before all physical
data. Below it, the original signed optical coefficient is nonnegative
and at most the uncharged coefficient. No bound on the scalar background
or the coupling separately is required. -/
theorem co_positive_k_of_physical_boundary_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ ηc : ℝ, 0 < ηc ∧
      ∀ (e s b : ℝ) (H : ℂ) (S : Fields) (D : Set (ℝ × ℝ)),
        IsSolution e S D → 0 < s → s ≤ b →
      ∀ u v, u < v → outSeg u u v ⊆ D → S.r u v = b →
        (∀ x ∈ Icc u v, δ ≤ 1 - S.mu u x) → S.m u v ≤ 2 * s →
        ‖S.phi u v‖ ≤ ‖H‖ + 2 * s / b →
        |e| * b * (1 + ‖H‖) ≤ ηc →
      ∀ x ∈ Ioc u v,
        0 ≤ (S.mu u x - S.Q u x ^ 2 / S.r u x ^ 2) / (1 - S.mu u x) ∧
        (S.mu u x - S.Q u x ^ 2 / S.r u x ^ 2) / (1 - S.mu u x) ≤
          S.mu u x / (1 - S.mu u x) := by
  obtain ⟨C, hC, hrelative⟩ := co_charge_relative_of_physical_boundary_bound hδ
  let ηc := min 1 (1 / (2 * C))
  have hηc : 0 < ηc := lt_min (by norm_num) (by positivity)
  have hη1 : ηc ≤ 1 := min_le_left _ _
  have hCη : C * ηc ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right 1 (1 / (2 * C))) hC.le
    dsimp [ηc]
    convert hh using 1
    field_simp
  have hCη2 : C * ηc ^ 2 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hη1 (mul_nonneg hC.le hηc.le)
    nlinarith only [hh, hCη]
  refine ⟨ηc, hηc, ?_⟩
  intro e s b H S D hS hs hsb u v huv hseg hrb hgap hm hboundary hsmall x hx
  have hη0 : 0 ≤ |e| * b * (1 + ‖H‖) := by
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (hs.le.trans hsb)) (by positivity)
  have hsq := (sq_le_sq₀ hη0 hηc.le).mpr hsmall
  have hc := (mul_le_mul_of_nonneg_left hsq hC.le).trans hCη2
  have hm0 := (Observation.mass_bounds_on_full_section hS huv.le hseg ⟨hx.1.le, hx.2⟩).1
  have hr := hS.r_pos (u, x) (hseg ⟨rfl, hx.1.le, hx.2⟩) hx.1
  have hμ : 0 ≤ S.mu u x := by dsimp [Fields.mu]; positivity
  have hq := (hrelative e s b H S D hS hs hsb u v huv hseg hrb hgap hm hboundary x hx).trans
    (by simpa using mul_le_mul_of_nonneg_right hc hμ)
  have hg := hS.one_sub_mu_pos (u, x) (hseg ⟨rfl, hx.1.le, hx.2⟩)
  exact ⟨div_nonneg (sub_nonneg.mpr hq) hg.le,
    div_le_div_of_nonneg_right (sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))) hg.le⟩

end EmcsfAcExtension.Global
