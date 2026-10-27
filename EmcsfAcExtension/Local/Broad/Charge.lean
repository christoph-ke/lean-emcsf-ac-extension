module

public import EmcsfAcExtension.Local.Broad.ScalarAverage
public import EmcsfAcExtension.Local.Broad.BVHardy
public import EmcsfAcExtension.Local.Calculus.RelativeCharge
public import EmcsfAcExtension.Infra.AC.Quotient
public import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Local.Broad.ChargeAlgebra

/-! # Broad charge and parallel-frame variation

The Maxwell constraint bounds the undifferenced charge without derivative
envelopes. A varying unit phase preserves norms, while its variation contributes
to the transported BV budget (internal project record).
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- The undifferenced part of charged_SF_new_version.tex:L5779–5785, with exact universal
coefficient `1/2`. This is the outgoing Maxwell estimate in the broad frozen
class; its constants are independent of every field, datum and box parameter. -/
theorem charge_bound {e M ε : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D)
    (hM : ∀ x ∈ Icc u v, ‖S.phi u x‖ ≤ M)
    (hε : ∀ x ∈ Icc u v, ‖S.theta u x / S.lam u x‖ ≤ ε) :
    |S.Q u v| ≤ |e| * M * ε * S.r u v ^ 2 / 2 :=
  Stab.oscillatory_charge_bound hS huv hseg hM hε

private theorem im_current_difference_le {p₁ p₂ z₁ z₂ : ℂ} {M ε d₁ d₂ : ℝ}
    (hM : 0 ≤ M) (hp : ‖p₂‖ ≤ M) (hz : ‖z₁‖ ≤ ε)
    (hd₁ : ‖p₁ - p₂‖ ≤ d₁) (hd₂ : ‖z₁ - z₂‖ ≤ d₂) :
    |(star p₁ * z₁).im - (star p₂ * z₂).im| ≤ d₁ * ε + M * d₂ := by
  have heq : star p₁ * z₁ - star p₂ * z₂ =
      star (p₁ - p₂) * z₁ + star p₂ * (z₁ - z₂) := by
    rw [star_sub]
    ring
  calc
    _ ≤ ‖star p₁ * z₁ - star p₂ * z₂‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (star p₁ * z₁ - star p₂ * z₂)
    _ ≤ ‖p₁ - p₂‖ * ‖z₁‖ + ‖p₂‖ * ‖z₁ - z₂‖ := by
      rw [heq]
      simpa only [norm_mul, norm_star] using norm_add_le (star (p₁ - p₂) * z₁)
        (star p₂ * (z₁ - z₂))
    _ ≤ _ := add_le_add (mul_le_mul hd₁ hz (norm_nonneg _) (by
      exact (norm_nonneg _).trans hd₁)) (mul_le_mul hp hd₂ (norm_nonneg _) hM)

private theorem weighted_current_difference_le {l₁ l₂ r₁ r₂ j₁ j₂ : ℝ}
    (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hr₁ : 0 ≤ r₁) :
    |l₁ * r₁ * j₁ - l₂ * r₂ * j₂| ≤ l₁ * r₁ * |j₁ - j₂| +
      |l₁ - l₂| * r₁ * |j₂| + l₂ * |r₁ - r₂| * |j₂| := by
  have heq : l₁ * r₁ * j₁ - l₂ * r₂ * j₂ =
      (l₁ * r₁ * (j₁ - j₂) + (l₁ - l₂) * r₁ * j₂) + l₂ * (r₁ - r₂) * j₂ := by ring
  rw [heq]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact (abs_add_le _ _).trans_eq (by
      simp only [abs_mul, abs_of_nonneg hl₁, abs_of_nonneg hr₁])
  · simp only [abs_mul, abs_of_nonneg hl₂]
    exact le_rfl

/-- [node restart-stab-broad-uniqueness#charge-comparison]
Broad charge comparison, charged_SF_new_version.tex:L5779–5785 and internal project record (Q).
For each fixed positive lower box constant `c` and nonnegative upper box
constant `C`, the positive comparison constant depends only on `c,C`, uniformly
in the triangle, coupling, scalar size, ratio size and competing solutions.
No characteristic derivative envelope or common-data assumption is needed. -/
theorem charge_comparison (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
          ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      ∀ u v, (u, v) ∈ triangle s t →
        (|S₁.Q u v| ≤ |e| * M * ε * S₁.r u v ^ 2 / 2 ∧
          |S₂.Q u v| ≤ |e| * M * ε * S₂.r u v ^ 2 / 2) ∧
        |S₁.Q u v - S₂.Q u v| ≤ K * |e| * M * S₁.r u v ^ 2 *
          ((normalized_field_distance s t S₁ S₂).toReal +
            ε * (geometry_distance s t S₁ S₂).toReal) := by
  obtain ⟨A, hA, hscalar⟩ := scalar_average_difference_bound c hc
  let K₀ := 1 + 2 * A + (1 + C) / c
  refine ⟨K₀ / 2, by dsimp [K₀]; positivity, ?_⟩
  intro s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hbox hosc u v hp
  have hmem₁ : S₁ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hmem₂ : S₂ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM
  have hl p hp := (hbox S₁ hmem₁ p hp).1
  have hfin := geometry_distance_ne_top hS₁ hS₂ hc hl
  let d := (normalized_field_distance s t S₁ S₂).toReal
  let g := (geometry_distance s t S₁ S₂).toReal
  let E := d + ε * g
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hg : 0 ≤ g := ENNReal.toReal_nonneg
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hdE : d ≤ E := le_add_of_nonneg_right (mul_nonneg hε hg)
  have hegE : ε * g ≤ E := le_add_of_nonneg_left hd
  have hphi p (hp : p ∈ triangle s t) :
      ‖S₁.phi p.1 p.2 - S₂.phi p.1 p.2‖ ≤ A * E :=
    hscalar s t e ε S₁ S₂ hS₁ hS₂ hε hl hosc p.1 p.2 hp
  have hseg : outSeg u u v ⊆ triangle s t := by
    rintro p ⟨rfl, hx⟩
    exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
  refine ⟨⟨charge_bound hS₁ hp.2.1 hseg
    (fun x hx => (hbox S₁ hmem₁ (u, x) (hseg ⟨rfl, hx⟩)).2.2.1)
    (fun x hx => (hbox S₁ hmem₁ (u, x) (hseg ⟨rfl, hx⟩)).2.2.2),
    charge_bound hS₂ hp.2.1 hseg
      (fun x hx => (hbox S₂ hmem₂ (u, x) (hseg ⟨rfl, hx⟩)).2.2.1)
      (fun x hx => (hbox S₂ hmem₂ (u, x) (hseg ⟨rfl, hx⟩)).2.2.2)⟩, ?_⟩
  let z₁ := fun x => S₁.theta u x / (S₁.lam u x : ℂ)
  let z₂ := fun x => S₂.theta u x / (S₂.lam u x : ℂ)
  let J₁ := fun x => S₁.lam u x * S₁.r u x * (star (S₁.phi u x) * z₁ x).im
  let J₂ := fun x => S₂.lam u x * S₂.r u x * (star (S₂.phi u x) * z₂ x).im
  have hr₁ x (hx : x ∈ Icc u v) : 0 ≤ S₁.r u x := by
    rcases eq_or_lt_of_le hx.1 with hx0 | hx0
    · subst x; rw [(hS₁.axis u (hseg ⟨rfl, le_rfl, hp.2.1⟩)).1]
    · exact (hS₁.r_pos (u, x) (hseg ⟨rfl, hx⟩) hx0).le
  have hcurrent x (hx : x ∈ Icc u v) :
      |J₁ x - J₂ x| ≤ K₀ * M * E * (S₁.lam u x * S₁.r u x) := by
    have hpx : (u, x) ∈ triangle s t := hseg ⟨rfl, hx⟩
    have hb₁ := hbox S₁ hmem₁ (u, x) hpx
    have hb₂ := hbox S₂ hmem₂ (u, x) hpx
    have hlam₁ := hS₁.lam_pos (u, x) hpx
    have hlam₂ := hS₂.lam_pos (u, x) hpx
    have hrnonneg := hr₁ x hx
    have hlamupper₂ := hb₂.2.1
    have hz : ‖z₁ x - z₂ x‖ ≤ (1 + A) * E := by
      have heq : z₁ x - z₂ x =
          (S₁.a u x - S₂.a u x) - (S₁.phi u x - S₂.phi u x) := by
        dsimp [z₁, z₂, Fields.a]
        abel
      rw [heq]
      calc
        _ ≤ ‖S₁.a u x - S₂.a u x‖ + ‖S₁.phi u x - S₂.phi u x‖ := norm_sub_le _ _
        _ ≤ d + A * E := add_le_add (norm_a_sub_le_distance hS₁ hS₂ hpx) (hphi _ hpx)
        _ ≤ (1 + A) * E := by nlinarith only [hdE]
    have hj := im_current_difference_le hM0 hb₂.2.2.1 hb₁.2.2.2 (hphi _ hpx) hz
    have hj' : |(star (S₁.phi u x) * z₁ x).im - (star (S₂.phi u x) * z₂ x).im| ≤
        M * (1 + 2 * A) * E := by
      apply hj.trans
      have hεM : ε ≤ M := hε1.trans hM
      have hh := mul_le_mul_of_nonneg_right hεM (mul_nonneg hA.le hE)
      nlinarith only [hh]
    have hj₂ : |(star (S₂.phi u x) * z₂ x).im| ≤ M * ε := by
      apply (Complex.abs_im_le_norm _).trans
      rw [norm_mul, norm_star]
      exact mul_le_mul hb₂.2.2.1 hb₂.2.2.2 (norm_nonneg _) hM0
    have hδl := abs_lam_sub_le_geometry_distance hS₁ hfin hpx
    have hδr := abs_radius_sub_le_geometry_distance_mul_radius hS₁ hS₂ hfin hpx
    have hweight : 1 + C ≤ ((1 + C) / c) * S₁.lam u x := by
      calc
        _ = ((1 + C) / c) * c := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hb₁.1 (by positivity)
    calc
      _ ≤ S₁.lam u x * S₁.r u x * (M * (1 + 2 * A) * E) +
          g * S₁.r u x * (M * ε) + C * (g * S₁.r u x) * (M * ε) := by
        apply (weighted_current_difference_le hlam₁.le hlam₂.le (hr₁ x hx)).trans
        gcongr
      _ = S₁.lam u x * S₁.r u x * (M * (1 + 2 * A) * E) +
          (1 + C) * S₁.r u x * M * (ε * g) := by ring
      _ ≤ S₁.lam u x * S₁.r u x * (M * (1 + 2 * A) * E) +
          (((1 + C) / c) * S₁.lam u x) * S₁.r u x * M * E := by
        gcongr
      _ = _ := by dsimp [K₀]; ring
  have continuousJ {S : Fields} (hS : IsSolution e S (triangle s t)) :
      ContinuousOn (fun x => S.lam u x * S.r u x *
        (star (S.phi u x) * (S.theta u x / S.lam u x)).im) (Icc u v) := by
    have cl := continuousOn_out_section hS.cont_lam hseg
    have cr := continuousOn_out_section hS.cont_r hseg
    have cp := continuousOn_out_section hS.cont_phi hseg
    have ct := continuousOn_out_section hS.cont_theta hseg
    have cz := ct.div (continuous_ofReal.comp_continuousOn cl) (fun x hx => by
      change (S.lam u x : ℂ) ≠ 0
      exact_mod_cast (hS.lam_pos (u, x) (hseg ⟨rfl, hx⟩)).ne')
    exact (cl.mul cr).mul (continuous_im.comp_continuousOn (cp.star.mul cz))
  have i₁ : IntervalIntegrable J₁ volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc hp.2.1 (continuousJ hS₁)
  have i₂ : IntervalIntegrable J₂ volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc hp.2.1 (continuousJ hS₂)
  have ib : IntervalIntegrable (fun x => K₀ * M * E * (S₁.lam u x * S₁.r u x)) volume u v :=
    (ContinuousOn.intervalIntegrable_of_Icc hp.2.1
      ((continuousOn_out_section hS₁.cont_lam hseg).mul
        (continuousOn_out_section hS₁.cont_r hseg))).const_mul _
  have hint := (intervalIntegral.norm_integral_le_integral_norm hp.2.1).trans
    (intervalIntegral.integral_mono_on hp.2.1 (i₁.sub i₂).norm ib (by
      intro x hx
      simpa only [Real.norm_eq_abs] using hcurrent x hx))
  calc
    _ = |e| * ‖∫ x in u..v, J₁ x - J₂ x‖ := by
      rw [Stab.oscillatory_charge_constraint hS₁ hp.2.1 hseg,
        Stab.oscillatory_charge_constraint hS₂ hp.2.1 hseg]
      change |(-e) * (∫ x in u..v, J₁ x) - (-e) * (∫ x in u..v, J₂ x)| = _
      rw [← mul_sub, ← intervalIntegral.integral_sub i₁ i₂, abs_mul, abs_neg, Real.norm_eq_abs]
    _ ≤ |e| * ∫ x in u..v, K₀ * M * E * (S₁.lam u x * S₁.r u x) :=
      mul_le_mul_of_nonneg_left hint (abs_nonneg e)
    _ = _ := by
      have hm : (∫ x in u..v, S₁.lam u x * S₁.r u x) = S₁.r u v ^ 2 / 2 := by
        simpa only [pow_one, Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two] using
          outgoing_radius_moment (u := u) (v := v) hS₁ hp.2.1 hseg 1
      rw [intervalIntegral.integral_const_mul, hm]
      dsimp [E, d, g]
      ring

/-- The electric-square part of charged_SF_new_version.tex:L5718–5726. The positive
coefficient depends only on the fixed box `c,C`, uniformly in all triangle,
coupling, scalar and competing-solution parameters. Both charge and radial
denominator differences are included. -/
theorem charged_square_difference (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ Kq : ℝ, 0 < Kq ∧ ∀ (s t e M ε : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
          ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      ∀ u v, (u, v) ∈ triangle s t →
        |S₁.Q u v ^ 2 / S₁.r u v ^ 2 - S₂.Q u v ^ 2 / S₂.r u v ^ 2| ≤
          Kq * e ^ 2 * M ^ 2 * ε * S₁.r u v ^ 2 *
            ((normalized_field_distance s t S₁ S₂).toReal +
              ε * (geometry_distance s t S₁ S₂).toReal) := by
  obtain ⟨K, hK, hcharge⟩ := charge_comparison c C hc hC
  let k := C / c
  refine ⟨K * (1 + k ^ 2) + k ^ 2 * (1 + k), by dsimp [k]; positivity, ?_⟩
  intro s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hbox hosc u v hp
  have hmem₁ : S₁ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hmem₂ : S₂ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM
  have hq := hcharge s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hbox hosc u v hp
  rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
  · subst v
    simp [(hS₁.axis u hp).1, (hS₂.axis u hp).1,
      (hS₁.axis u hp).2.2.1, (hS₂.axis u hp).2.2.1]
  · have hs : outSeg u u v ⊆ triangle s t := by
      rintro p ⟨rfl, hx⟩
      exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
    have hr₁ := hS₁.r_pos (u, v) hp huv
    have hr₂ := hS₂.r_pos (u, v) hp huv
    have hlo := outgoing_radius_lower hS₁ huv.le hs
      (fun x hx => (hbox S₁ hmem₁ (u, x) (hs ⟨rfl, hx⟩)).1)
    have hup : S₂.r u v ≤ C * (v - u) := by
      rw [← outgoing_radius_reconstruction hS₂ huv.le hs]
      have h := intervalIntegral.integral_mono_on huv.le
        (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le
          (continuousOn_out_section hS₂.cont_lam hs))
        (intervalIntegrable_const (μ := volume) (c := C))
        (fun x hx => (hbox S₂ hmem₂ (u, x) (hs ⟨rfl, hx⟩)).2.1)
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
    have hratio : S₂.r u v ≤ k * S₁.r u v := by
      apply hup.trans
      calc
        C * (v - u) = k * (c * (v - u)) := by dsimp [k]; field_simp
        _ ≤ k * S₁.r u v := mul_le_mul_of_nonneg_left hlo (div_nonneg hC hc.le)
    have hfin := geometry_distance_ne_top hS₁ hS₂ hc
      (fun p hp => (hbox S₁ hmem₁ p hp).1)
    let g := (geometry_distance s t S₁ S₂).toReal
    let E := (normalized_field_distance s t S₁ S₂).toReal + ε * g
    have hg : 0 ≤ g := ENNReal.toReal_nonneg
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hQ₁ : |S₁.Q u v| ≤ (|e| * M) * ε * S₁.r u v ^ 2 := by
      have h0 : 0 ≤ |e| * M * ε * S₁.r u v ^ 2 := by positivity
      exact hq.1.1.trans (by linarith)
    have hQ₂ : |S₂.Q u v| ≤ (|e| * M) * ε * S₂.r u v ^ 2 := by
      have h0 : 0 ≤ |e| * M * ε * S₂.r u v ^ 2 := by positivity
      exact hq.1.2.trans (by linarith)
    have hδQ : |S₁.Q u v - S₂.Q u v| ≤ K * (|e| * M) * S₁.r u v ^ 2 * E := by
      simpa only [E, g, mul_assoc] using hq.2
    have h := electric_square_difference_of_bounds hr₁ hr₂ (mul_nonneg (abs_nonneg e) hM0)
      hε hE hg (div_nonneg hC hc.le) hK.le hratio hQ₁ hQ₂ hδQ
      (abs_radius_sub_le_geometry_distance_mul_radius hS₁ hS₂ hfin hp)
      (le_add_of_nonneg_left ENNReal.toReal_nonneg)
    convert h using 1
    dsimp only [E, g]
    rw [mul_pow, sq_abs]
    ring

/-- A continuous real trace with an interior derivative bounded by `K` has
endpoint increment at most `K` times the interval length. The coefficient is
exactly one; no derivative is required at either endpoint. -/
theorem abs_sub_le_of_interior_deriv_bound {a b K : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hdf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Ioo a b, |f' x| ≤ K) :
    |f b - f a| ≤ K * (b - a) := by
  have hplus : MonotoneOn (fun x => K * x + f x) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      ((continuousOn_const.mul continuousOn_id).add hf)
    · intro x hx
      rw [interior_Icc] at hx
      exact (((hasDerivAt_id x).const_mul K).add (hdf x hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      change 0 ≤ deriv (fun y => K * y + f y) x
      have hdx := ((hasDerivAt_id x).const_mul K).add (hdf x hx)
      change HasDerivAt (fun y => K * y + f y) (K * 1 + f' x) x at hdx
      rw [hdx.deriv]
      have h := (abs_le.mp (hbound x hx)).1
      linarith
  have hminus : MonotoneOn (fun x => K * x - f x) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      ((continuousOn_const.mul continuousOn_id).sub hf)
    · intro x hx
      rw [interior_Icc] at hx
      exact (((hasDerivAt_id x).const_mul K).sub (hdf x hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      change 0 ≤ deriv (fun y => K * y - f y) x
      have hdx := ((hasDerivAt_id x).const_mul K).sub (hdf x hx)
      change HasDerivAt (fun y => K * y - f y) (K * 1 - f' x) x at hdx
      rw [hdx.deriv]
      have h := (abs_le.mp (hbound x hx)).2
      linarith
  have hp := hplus (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have hm := hminus (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The zero-axis potential is bounded without any incoming Hardy estimate.
The displayed coefficient `C²/c²` depends only on the geometric box, uniformly
in coupling, scalar size, ratio bound, solution, and outgoing segment. This is
the noncircular potential input in internal project record (QA0); optimizing its coefficient
is unnecessary. -/
theorem potential_bound (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    {e M ε : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) (haxis : S.A u u = 0)
    (hM0 : 0 ≤ M) (hε0 : 0 ≤ ε)
    (hM : ∀ x ∈ Icc u v, ‖S.phi u x‖ ≤ M)
    (hε : ∀ x ∈ Icc u v, ‖S.theta u x / S.lam u x‖ ≤ ε)
    (hl : ∀ x ∈ Icc u v, c ≤ S.lam u x ∧ S.lam u x ≤ C)
    (hn : ∀ x ∈ Icc u v, -S.nu u x ≤ C)
    (hg : ∀ x ∈ Icc u v, c ≤ 1 - S.mu u x) :
    |S.A u v| ≤ (C ^ 2 / c ^ 2) * |e| * M * ε * S.r u v := by
  rcases eq_or_lt_of_le huv with huv | huv
  · subst v
    simp [haxis, (hS.axis u (hseg ⟨rfl, le_rfl, le_rfl⟩)).1]
  have cr := continuousOn_out_section hS.cont_r hseg
  have cn := continuousOn_out_section hS.cont_nu hseg
  have cl := continuousOn_out_section hS.cont_lam hseg
  have cQ := continuousOn_out_section hS.cont_Q hseg
  have cA := continuousOn_out_section hS.cont_A hseg
  have cg : ContinuousOn (fun x => 1 - S.mu u x) (Icc u v) :=
    continuousOn_const.sub (continuousOn_mu_out hS huv hseg)
  have nr x (hx : x ∈ Ioo u v) : S.r u x ≠ 0 :=
    (hS.r_pos (u, x) (hseg ⟨rfl, hx.1.le, hx.2.le⟩) hx.1).ne'
  have cd : ContinuousOn (S.AV u) (Ioo u v) := by
    apply ((((continuousOn_const.mul (cn.mono Ioo_subset_Icc_self)).mul
      (cl.mono Ioo_subset_Icc_self)).mul (cQ.mono Ioo_subset_Icc_self)).div
        ((cg.mono Ioo_subset_Icc_self).mul ((cr.mono Ioo_subset_Icc_self).pow 2)))
    intro x hx
    exact mul_ne_zero (hc.trans_le (hg x ⟨hx.1.le, hx.2.le⟩)).ne'
      (pow_ne_zero 2 (nr x hx))
  have hd x (hx : x ∈ Ioo u v) : HasDerivAt (S.A u) (S.AV u x) x := by
    apply hasDerivAt_of_integralForm_interior hx cd
    intro a b ha hab hb
    exact (hS.eq_out u a b ha hab (by
      rintro p ⟨rfl, hp⟩
      exact hseg ⟨rfl, ha.le.trans hp.1, hp.2.trans hb.le⟩)).2.2.2.2.1
  have hbound x (hx : x ∈ Ioo u v) :
      |S.AV u x| ≤ (C ^ 2 / c) * |e| * M * ε := by
    have hx' : x ∈ Icc u v := ⟨hx.1.le, hx.2.le⟩
    have hr := hS.r_pos (u, x) (hseg ⟨rfl, hx'⟩) hx.1
    have hnu := hS.nu_neg (u, x) (hseg ⟨rfl, hx'⟩)
    have hlam := hS.lam_pos (u, x) (hseg ⟨rfl, hx'⟩)
    have hgap := hc.trans_le (hg x hx')
    have hs : outSeg u u x ⊆ D := by
      rintro p ⟨rfl, hp⟩
      exact hseg ⟨rfl, hp.1, hp.2.trans hx.2.le⟩
    have hq := charge_bound hS hx.1.le hs
      (fun y hy => hM y ⟨hy.1, hy.2.trans hx.2.le⟩)
      (fun y hy => hε y ⟨hy.1, hy.2.trans hx.2.le⟩)
    calc
      _ = 2 * (-S.nu u x) * S.lam u x * |S.Q u x| /
          ((1 - S.mu u x) * S.r u x ^ 2) := by
        simp only [Fields.AV, abs_div, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_neg hnu,
          abs_of_pos hlam, abs_of_pos hgap, abs_of_nonneg (sq_nonneg (S.r u x))]
      _ ≤ 2 * C * C * (|e| * M * ε * S.r u x ^ 2 / 2) /
          (c * S.r u x ^ 2) := by
        gcongr
        · exact hn x hx'
        · exact (hl x hx').2
        · exact hg x hx'
      _ = _ := by field_simp [hr.ne']
  have hA := abs_sub_le_of_interior_deriv_bound huv.le cA hd hbound
  rw [haxis, sub_zero] at hA
  have hrlower := outgoing_radius_lower hS huv.le hseg (fun x hx => (hl x hx).1)
  calc
    _ ≤ (C ^ 2 / c) * |e| * M * ε * (v - u) := hA
    _ = ((C ^ 2 / c) * |e| * M * ε / c) * (c * (v - u)) := by field_simp
    _ ≤ ((C ^ 2 / c) * |e| * M * ε / c) * S.r u v :=
      mul_le_mul_of_nonneg_left hrlower (by positivity)
    _ = _ := by field_simp

/-- Multiplication by a unit phase costs its variation times a uniform trace
bound. Both displayed coefficients are exactly one, independent of the trace,
phase, interval and bound. This estimate does not identify ordinary and
parallel-frame variation. -/
theorem parallel_frame_variation_le {s : Set ℝ} {P b : ℝ → ℂ} {B : ℝ}
    (hP : ∀ x ∈ s, ‖P x‖ = 1) (hb : ∀ x ∈ s, ‖b x‖ ≤ B) :
    eVariationOn (fun x => P x * b x) s ≤
      eVariationOn b s + ENNReal.ofReal B * eVariationOn P s := by
  have h := eVariationOn.mul_le (C := 1) (D := ENNReal.ofReal B)
    (f := P) (g := b) (s := s)
    (fun x hx => by rw [← ofReal_norm, hP x hx, ENNReal.ofReal_one])
    (fun x hx => by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hb x hx))
  simpa only [one_mul] using h

/-- A phase formed from a real angle increases the trace variation by at most
the angle variation times the trace bound. The coefficients are universal and
exactly one. No differentiability or AC hypothesis enters this BV inequality. -/
theorem parallel_frame_variation_le_angle {s : Set ℝ} {θ : ℝ → ℝ}
    {b : ℝ → ℂ} {B : ℝ} (hb : ∀ x ∈ s, ‖b x‖ ≤ B) :
    eVariationOn (fun x => Complex.exp (I * (θ x : ℂ)) * b x) s ≤
      eVariationOn b s + ENNReal.ofReal B * eVariationOn θ s := by
  apply (parallel_frame_variation_le
    (P := fun x => Complex.exp (I * (θ x : ℂ)))
    (fun x _ => Complex.norm_exp_I_mul_ofReal (θ x)) hb).trans
  gcongr
  exact eVariationOn.unit_phase_le θ s

/-- The internal project record variation bridge for a continuous connection on one incoming
section. The explicit additional cost is `B |e| ∫ |A|`, with universal
coefficient one; no varying phase is treated as variation preserving. -/
theorem parallel_frame_variation_le_integral {a v c e B : ℝ} {A : ℝ → ℝ} {b : ℝ → ℂ}
    (hav : a ≤ v) (hc : c ∈ Icc a v) (hA : ContinuousOn A (Icc a v))
    (hb : ∀ x ∈ Icc a v, ‖b x‖ ≤ B) :
    eVariationOn (fun x => Complex.exp (I * (e * ∫ y in c..x, A y : ℝ)) * b x) (Icc a v) ≤
      eVariationOn b (Icc a v) +
        ENNReal.ofReal B * ENNReal.ofReal (|e| * ∫ x in a..v, |A x|) := by
  have hAi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hav hA
  have hθ := (hAi.const_mul e).eVariationOn_eq_integral_norm_of_eq_integral
    (f := fun x => e * ∫ y in c..x, A y) hav (by
      intro x hx
      rw [intervalIntegral.integral_const_mul, ← mul_add,
        intervalIntegral.integral_add_adjacent_intervals
          (hAi.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc hc) left_mem_uIcc))
          (hAi.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hx)))])
  have heq : (∫ x in a..v, ‖e * A x‖) = |e| * ∫ x in a..v, |A x| := by
    simp only [Real.norm_eq_abs, abs_mul, intervalIntegral.integral_const_mul]
  rw [heq] at hθ
  simpa only [hθ] using (parallel_frame_variation_le_angle
    (θ := fun x => e * ∫ y in c..x, A y) hb)

/-- [node restart-stab-broad-uniqueness#incoming-BV-Hardy]
Discharge the parallel-frame variation from the frozen ordinary BV budgets,
as required by internal project record internal project record. For fixed box constants `c,C`, `K`
depends only
on that box, independently of `s,t,e,M,L`, the solution and the incoming label.
There is no smallness assumption on `L` and no derivative envelope. -/
theorem incoming_bv_hardy_of_ordinary_variation (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M L : ℝ) (S : Fields),
      IsSolution e S (triangle s t) → 1 ≤ M → 0 ≤ L →
      (∀ p ∈ triangle s t, c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
        -S.nu p.1 p.2 ≤ C ∧ c ≤ 1 - S.mu p.1 p.2 ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ 1) →
      (∀ u v, (u, v) ∈ triangle s t →
        eVariationOn (S.a u) (Icc u v) ≤ ENNReal.ofReal L) →
      (∀ v ∈ Icc s t,
        eVariationOn (fun x => S.b x v) (Icc s v) ≤ ENNReal.ofReal L) →
      (∀ x ∈ Icc s t, S.A x x = 0) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      ∀ v ∈ Icc s t,
        IntervalIntegrable (fun x => (-S.nu x v) / S.r x v *
          ‖S.xi x v / S.nu x v‖) volume s v ∧
        (∫ x in s..v, (-S.nu x v) / S.r x v * ‖S.xi x v / S.nu x v‖) ≤ K * L := by
  let A₀ := C ^ 2 / c ^ 2
  refine ⟨1 + 8 * A₀ * C, by dsimp [A₀]; positivity, ?_⟩
  intro s t e M L S hS hM hL hbox hvarA hvarB haxis hσ v hv
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM
  have hst : 0 ≤ t - s := by linarith [hv.1, hv.2]
  have hz (u w : ℝ) (hp : (u, w) ∈ triangle s t) :
      ‖S.theta u w / S.lam u w‖ ≤ L := by
    have hs : outSeg u u w ⊆ triangle s t := by
      rintro p ⟨rfl, hx⟩
      exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
    apply (norm_outgoing_ratio_le_variation hS hp.2.1 hs).trans
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvarA u w hp)
    simpa only [ENNReal.toReal_ofReal hL] using h
  have hAsmall (u w : ℝ) (hp : (u, w) ∈ triangle s t) :
      |S.A u w| ≤ A₀ * |e| * M * L * C * (t - s) := by
    have hs : outSeg u u w ⊆ triangle s t := by
      rintro p ⟨rfl, hx⟩
      exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
    have hpot := potential_bound c C hc hC hS hp.2.1 hs
      (haxis u ⟨hp.1, hp.2.1.trans hp.2.2⟩) hM0 hL
      (fun x hx => (hbox (u, x) (hs ⟨rfl, hx⟩)).2.2.2.2.1)
      (fun x hx => hz u x (hs ⟨rfl, hx⟩))
      (fun x hx => ⟨(hbox (u, x) (hs ⟨rfl, hx⟩)).1,
        (hbox (u, x) (hs ⟨rfl, hx⟩)).2.1⟩)
      (fun x hx => (hbox (u, x) (hs ⟨rfl, hx⟩)).2.2.1)
      (fun x hx => (hbox (u, x) (hs ⟨rfl, hx⟩)).2.2.2.1)
    have hrup : S.r u w ≤ C * (w - u) := by
      rw [← outgoing_radius_reconstruction hS hp.2.1 hs]
      have h := intervalIntegral.integral_mono_on hp.2.1
        (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hp.2.1
          (continuousOn_out_section hS.cont_lam hs))
        (intervalIntegrable_const (μ := volume) (c := C))
        (fun x hx => (hbox (u, x) (hs ⟨rfl, hx⟩)).2.1)
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
    calc
      _ ≤ A₀ * |e| * M * L * S.r u w := hpot
      _ ≤ A₀ * |e| * M * L * (C * (w - u)) := by gcongr
      _ ≤ A₀ * |e| * M * L * C * (t - s) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (by linarith [hp.1, hp.2.2])
          (by dsimp [A₀]; positivity)
  have hs : inSeg s v v ⊆ triangle s t := by
    rintro p ⟨hp₁, hp₂, rfl⟩
    exact ⟨hp₁, hp₂, hv.2⟩
  have cA := continuousOn_in_section hS.cont_A hs
  let N := A₀ * |e| * M * L * C * (t - s)
  have hN : 0 ≤ N := by dsimp [N, A₀]; positivity
  have hAi : (∫ x in s..v, |S.A x v|) ≤ N * (t - s) := by
    have h := intervalIntegral.integral_mono_on hv.1
      (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hv.1 cA.abs)
      (intervalIntegrable_const (μ := volume) (c := N))
      (fun x hx => hAsmall x v ⟨hx.1, hx.2, hv.2⟩)
    have h' : (∫ x in s..v, |S.A x v|) ≤ N * (v - s) := by
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (by linarith [hv.2]) hN)
  have hcost : (M + 1) * (|e| * ∫ x in s..v, |S.A x v|) ≤ 8 * A₀ * C * L := by
    have hint0 : 0 ≤ ∫ x in s..v, |S.A x v| :=
      intervalIntegral.integral_nonneg hv.1 (fun _ _ => abs_nonneg _)
    calc
      _ ≤ (2 * M) * (|e| * (N * (t - s))) := by
        gcongr
        linarith
      _ = (8 * A₀ * C * L) * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) := by
        dsimp [N]
        ring_nf
        rw [sq_abs]
        ring
      _ ≤ (8 * A₀ * C * L) * 1 :=
        mul_le_mul_of_nonneg_left hσ (by dsimp [A₀]; positivity)
      _ = _ := mul_one _
  have hb x (hx : x ∈ Icc s v) : ‖S.b x v‖ ≤ M + 1 := by
    calc
      _ ≤ ‖S.phi x v‖ + ‖S.xi x v / S.nu x v‖ := by
        exact norm_add_le _ _
      _ ≤ M + 1 := add_le_add (hbox (x, v) (hs ⟨hx.1, hx.2, rfl⟩)).2.2.2.2.1
        (hbox (x, v) (hs ⟨hx.1, hx.2, rfl⟩)).2.2.2.2.2
  have hphase := parallel_frame_variation_le_integral (e := e) hv.1
    (right_mem_Icc.mpr hv.1) cA hb
  have hPB : eVariationOn (fun x => Complex.exp (I * e * (∫ y in v..x, S.A y v : ℝ)) *
      S.b x v) (Icc s v) ≤ ENNReal.ofReal ((1 + 8 * A₀ * C) * L) := by
    have hphase' := hphase.trans (add_le_add (hvarB v hv) le_rfl)
    rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ M + 1)] at hphase'
    have hbnd := hphase'.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hcost))
    rw [← ENNReal.ofReal_add hL (by dsimp [A₀]; positivity)] at hbnd
    calc
      _ ≤ ENNReal.ofReal (L + 8 * A₀ * C * L) := by
        simpa only [Complex.ofReal_mul, mul_assoc] using hbnd
      _ = _ := by congr 1; ring
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hPB
  rw [ENNReal.toReal_ofReal (by dsimp [A₀]; positivity)] at hreal
  have hHardy := incoming_bv_hardy_solution hS hv.1 hs
  exact ⟨hHardy.1, hHardy.2.trans hreal⟩

end EmcsfAcExtension.Local.Broad
