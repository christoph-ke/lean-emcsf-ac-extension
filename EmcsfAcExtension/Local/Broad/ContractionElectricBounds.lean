module

public import EmcsfAcExtension.Local.Broad.GeometryWeights
public import EmcsfAcExtension.Local.Broad.ContractionElectricAlgebra
public import EmcsfAcExtension.Local.Broad.MassComparison
public import EmcsfAcExtension.Local.Broad.Charge
import EmcsfAcExtension.Local.Broad.PotentialAlgebra
import EmcsfAcExtension.Local.Broad.ChargeAlgebra

/-! # Electric scalar-source comparison with its integrable radial factor

The charge ratio is `Q/r²`; one factor of radius is left outside. This
keeps the electric term integrable at the axis in either orientation.
-/

public section

open Set Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- Electric scalar forcing has a difference majorant proportional to
`e² M² (D+εG) w₁ r₁`. The positive constant depends only on `c,C`, before
all triangle, coupling, scalar and solution parameters. The weight can
be either positive expansion; both expansion and radius errors are kept. -/
theorem electric_scalar_source_difference (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → ε ^ 2 ≤ 1 / 2 →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
        ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t, c ≤ 1 - S.mu p.1 p.2) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      ∀ u v, (u, v) ∈ triangle s t → ∀ w₁ w₂ : ℝ,
      c ≤ w₁ → w₁ ≤ C → c ≤ w₂ → w₂ ≤ C →
      |w₁ - w₂| ≤ (geometry_distance s t S₁ S₂).toReal →
      ‖I * e * (((w₁ : ℂ) / S₁.r u v) * S₁.Q u v * S₁.phi u v / (1 - S₁.mu u v) -
        ((w₂ : ℂ) / S₂.r u v) * S₂.Q u v * S₂.phi u v / (1 - S₂.mu u v))‖ ≤
        K * e ^ 2 * M ^ 2 *
          ((normalized_field_distance s t S₁ S₂).toReal +
            ε * (geometry_distance s t S₁ S₂).toReal) *
          (w₁ * S₁.r u v) := by
  obtain ⟨Kq, hKq, hcharge⟩ := charge_comparison c C hc hC
  obtain ⟨Kφ, hKφ, hscalar⟩ := scalar_average_difference_bound c hc
  obtain ⟨KM, hKM, hmass⟩ := Local.stab_broad_mu_sup c C hc hC
  let k := C / c
  let Cb := C + k + 1
  let P0 := Cb ^ 2 / c
  let PG := 2 * Cb / c
  let PX := Cb ^ 2 / c ^ 2
  let QK := Kq + (1 + k)
  let K0 := P0 * Kφ + P0 * QK + PG + PX * (2 * KM)
  have hk : 0 ≤ k := div_nonneg hC hc.le
  have hCb : 0 < Cb := by dsimp [Cb]; positivity
  have hP0 : 0 ≤ P0 := by dsimp [P0]; positivity
  have hPG : 0 < PG := by dsimp [PG]; positivity
  have hPX : 0 ≤ PX := by dsimp [PX]; positivity
  have hQK : 0 ≤ QK := by dsimp [QK]; positivity
  have hK0 : 0 < K0 := by dsimp [K0]; positivity
  refine ⟨K0 / c, div_pos hK0 hc, ?_⟩
  intro s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hbox hgap hosc hσ u v hp w₁ w₂
    hw₁ hw₁C hw₂ hw₂C hδw
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
  · subst v
    simp only [(hS₁.axis u hp).1, (hS₂.axis u hp).1, Complex.ofReal_zero,
      div_zero, zero_mul, zero_div,
      sub_self, norm_zero, mul_zero, le_refl]
  have hr₁ := hS₁.r_pos (u, v) hp huv
  have hr₂ := hS₂.r_pos (u, v) hp huv
  let r₁ := S₁.r u v
  let r₂ := S₂.r u v
  let g₁ := 1 - S₁.mu u v
  let g₂ := 1 - S₂.mu u v
  let G := (geometry_distance s t S₁ S₂).toReal
  let E := (normalized_field_distance s t S₁ S₂).toReal + ε * G
  let α := |e| * M
  let X := 2 * KM * ε * E
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hεG : ε * G ≤ E := le_add_of_nonneg_left ENNReal.toReal_nonneg
  have hlo : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C :=
    fun S hS p hp => ⟨(hbox S hS p hp).1, (hbox S hS p hp).2.1⟩
  have hfin := geometry_distance_ne_top hS₁ hS₂ hc (fun p hp => (hlo S₁ (by simp) p hp).1)
  have hrr := radius_comparison_of_solution_box hc hC hS₁ hS₂ hlo hp
  have hδr : |r₁ - r₂| ≤ G * r₁ :=
    abs_radius_sub_le_geometry_distance_mul_radius hS₁ hS₂ hfin hp
  have hQ := hcharge s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hbox hosc u v hp
  have hraw₁ : |S₁.Q u v| ≤ α * ε * r₁ ^ 2 := by
    apply hQ.1.1.trans
    have hh : 0 ≤ α * ε * r₁ ^ 2 := by positivity
    change α * ε * r₁ ^ 2 / 2 ≤ α * ε * r₁ ^ 2
    linarith
  have hraw₂ : |S₂.Q u v| ≤ α * ε * r₂ ^ 2 := by
    apply hQ.1.2.trans
    have hh : 0 ≤ α * ε * r₂ ^ 2 := by positivity
    change α * ε * r₂ ^ 2 / 2 ≤ α * ε * r₂ ^ 2
    linarith
  have hq₁ : |S₁.Q u v / r₁ ^ 2| ≤ α * ε := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hr₁)]
    exact (div_le_iff₀ (sq_pos_of_pos hr₁)).mpr hraw₁
  have hq₂ : |S₂.Q u v / r₂ ^ 2| ≤ α * ε := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hr₂)]
    exact (div_le_iff₀ (sq_pos_of_pos hr₂)).mpr hraw₂
  have hδq : |S₁.Q u v / r₁ ^ 2 - S₂.Q u v / r₂ ^ 2| ≤ QK * α * E := by
    apply charge_quotient_difference_of_bounds hr₁ hr₂ hα hε hE hG hk hKq.le hrr.2 hraw₂
      (by simpa only [α, mul_assoc] using hQ.2) hδr hεG
  have hMu := hmass s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hbox hosc
  have hmu : |S₁.mu u v - S₂.mu u v| ≤ X := by
    apply (abs_mu_sub_le_mass_ratio_distance hS₁ hS₂ hp).trans
    apply hMu.trans
    calc
      _ = KM * ε * E + KM * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε * E := by dsimp [E, G]; ring
      _ ≤ KM * ε * E + KM * 1 * ε * E := by gcongr
      _ = X := by dsimp [X]; ring
  have hδg : |g₁ - g₂| ≤ X := by
    rw [show g₁ - g₂ = -(S₁.mu u v - S₂.mu u v) by dsimp [g₁, g₂]; ring, abs_neg]
    exact hmu
  have hl₂ : |r₂ / r₁| ≤ Cb := by
    rw [abs_of_pos (div_pos hr₂ hr₁)]
    exact ((div_le_iff₀ hr₁).mpr hrr.2).trans (by dsimp [Cb]; linarith)
  have hδl : |1 - r₂ / r₁| ≤ G := by
    rw [show 1 - r₂ / r₁ = (r₁ - r₂) / r₁ by field_simp [show r₁ ≠ 0 from hr₁.ne'],
      abs_div, abs_of_pos hr₁]
    exact (div_le_iff₀ hr₁).mpr hδr
  have hP := potential_factor_difference_of_bounds (n₁ := w₁) (n₂ := w₂) (l₁ := 1)
    (l₂ := r₂ / r₁) (g₁ := g₁) (g₂ := g₂) (C := Cb) hc hCb.le hG hX
    (by rw [abs_of_pos (hc.trans_le hw₁)]; exact hw₁C.trans (by dsimp [Cb]; linarith))
    (by rw [abs_of_pos (hc.trans_le hw₂)]; exact hw₂C.trans (by dsimp [Cb]; linarith))
    (by rw [abs_one]; dsimp [Cb]; linarith) hl₂
    (hgap S₁ (by simp) (u, v) hp) (hgap S₂ (by simp) (u, v) hp) hδw hδl hδg
  have hφ := hscalar s t e ε S₁ S₂ hS₁ hS₂ hε (fun p hp => (hlo S₁ (by simp) p hp).1) hosc u v hp
  have hprod := electric_product_difference_of_bounds hP0 hPG.le hPX hα hε hE hG hX hQK
    (by positivity : 0 ≤ Kφ * E) hM0
    (by simpa only [mul_one] using hP.1) (by simpa only [mul_one] using hP.2)
    hq₁ hq₂ hδq (hbox S₂ (by simp) (u, v) hp).2.2.1 hφ
  have hprod' := hprod.trans (electric_error_polynomial_le hP0 hPG.le hPX hα hε hε1 hE hG
    hQK hKφ.le (by positivity : 0 ≤ 2 * KM) hM hεG (le_rfl : X ≤ 2 * KM * ε * E))
  have hr₁C : (r₁ : ℂ) ≠ 0 := by exact_mod_cast hr₁.ne'
  have hr₂C : (r₂ : ℂ) ≠ 0 := by exact_mod_cast hr₂.ne'
  have hg₁C : (g₁ : ℂ) ≠ 0 := by exact_mod_cast (hc.trans_le (hgap S₁ (by simp) (u, v) hp)).ne'
  have hg₂C : (g₂ : ℂ) ≠ 0 := by exact_mod_cast (hc.trans_le (hgap S₂ (by simp) (u, v) hp)).ne'
  have heq : I * e * (((w₁ : ℂ) / r₁) * S₁.Q u v * S₁.phi u v / (g₁ : ℂ) -
      ((w₂ : ℂ) / r₂) * S₂.Q u v * S₂.phi u v / (g₂ : ℂ)) =
      I * e * (r₁ : ℂ) * (((w₁ / g₁ : ℝ) : ℂ) * (S₁.Q u v / r₁ ^ 2 : ℝ) * S₁.phi u v -
        ((w₂ * (r₂ / r₁) / g₂ : ℝ) : ℂ) * (S₂.Q u v / r₂ ^ 2 : ℝ) * S₂.phi u v) := by
    push_cast
    field_simp [hr₁C, hr₂C, hg₁C, hg₂C]
  simp only [g₁, g₂, Complex.ofReal_sub, Complex.ofReal_one] at heq
  rw [heq]
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (show 0 < r₁ from hr₁), one_mul]
  calc
    _ ≤ |e| * r₁ * (K0 * α * M * E) := mul_le_mul_of_nonneg_left hprod' (by positivity)
    _ = K0 * (|e| * |e|) * M ^ 2 * E * r₁ := by dsimp [α]; ring
    _ = K0 * e ^ 2 * M ^ 2 * E * r₁ := by rw [← pow_two, sq_abs]
    _ ≤ (K0 / c) * e ^ 2 * M ^ 2 * E * (w₁ * r₁) := by
      have hscale : 1 ≤ w₁ / c := (le_div_iff₀ hc).mpr (by simpa only [one_mul] using hw₁)
      have hm := mul_le_mul_of_nonneg_left hscale
        (show 0 ≤ K0 * e ^ 2 * M ^ 2 * E * r₁ by positivity)
      apply (show K0 * e ^ 2 * M ^ 2 * E * r₁ ≤
        (K0 * e ^ 2 * M ^ 2 * E * r₁) * (w₁ / c) by simpa only [mul_one] using hm).trans_eq
      ring

end EmcsfAcExtension.Local.Broad
