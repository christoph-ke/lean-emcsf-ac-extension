module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseSourceAux
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFields
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseSourcePointwise
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseNorms
import EmcsfAcExtension.Local.Apriori.Area
import EmcsfAcExtension.Local.Apriori.AreaJAux
import EmcsfAcExtension.Local.Apriori.AreaJ
import EmcsfAcExtension.Local.Apriori.AreaK
import EmcsfAcExtension.Local.Apriori.Charge

/-! # Area budgets for the full characteristic forcing

The scalar source is integrated in the order prescribed by the two area
estimates, with the opposite characteristic variation retained until its
envelope absorption. Electric errors are quadratic in the charged scale.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem plane_area_majorant {e s ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    {F G : ℝ × ℝ → ℝ≥0∞} (hset : AprioriSetting e s ε M S h) (hA : 0 ≤ A)
    (hG : Measurable ((triangle 0 s).indicator G))
    (hpoint : ∀ u v, (u, v) ∈ triangle 0 s → F (u, v) ≤
      ENNReal.ofReal 3 * G (u, v) + ENNReal.ofReal (A * (-S.nu u v) * S.lam u v)) :
    (∫⁻ p in triangle 0 s, F p ∂(volume.prod volume)) ≤
      ENNReal.ofReal 3 * (∫⁻ p in triangle 0 s, G p ∂(volume.prod volume)) +
        ENNReal.ofReal (4 * A * (s / 2) ^ 2) := by
  let G₀ := (triangle 0 s).indicator G
  let E := fun p : ℝ × ℝ => ENNReal.ofReal (A * (-S.nu p.1 p.2) * S.lam p.1 p.2)
  let E₀ := (triangle 0 s).indicator E
  have ce : ContinuousOn E (triangle 0 s) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((continuousOn_const.mul hset.c1.c1_nu.continuousOn.neg).mul
        hset.c1.c1_lam.continuousOn)
  have hEm : Measurable E₀ := by
    classical
    dsimp only [E₀]
    rw [← Set.piecewise_eq_indicator]
    exact ce.measurable_piecewise (continuousOn_const (c := (0 : ℝ≥0∞)))
      (measurableSet_triangle 0 s)
  have hE : (∫⁻ p in triangle 0 s, E p ∂(volume.prod volume)) ≤
      ENNReal.ofReal (4 * A * (s / 2) ^ 2) := by
    rw [(triangle_lintegral_orders hEm).2]
    exact Area.area_integral_in_le_of_pointwise hset hA
      (fun u v => E (u, v)) (fun _ _ _ => le_rfl)
  have hle : (∫⁻ p in triangle 0 s, F p ∂(volume.prod volume)) ≤
      ∫⁻ p in triangle 0 s, ENNReal.ofReal 3 * G₀ p + E₀ p ∂(volume.prod volume) := by
    apply setLIntegral_mono' (measurableSet_triangle 0 s)
    intro p hp
    dsimp only [G₀, E₀]
    rw [indicator_of_mem hp, indicator_of_mem hp]
    exact hpoint p.1 p.2 hp
  rw [lintegral_add_left (hG.const_mul (ENNReal.ofReal 3)),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hle
  have heG : (∫⁻ p in triangle 0 s, G₀ p ∂(volume.prod volume)) =
      ∫⁻ p in triangle 0 s, G p ∂(volume.prod volume) := by
    simp only [G₀, setLIntegral_indicator (measurableSet_triangle 0 s), inter_self]
  have heE : (∫⁻ p in triangle 0 s, E₀ p ∂(volume.prod volume)) =
      ∫⁻ p in triangle 0 s, E p ∂(volume.prod volume) := by
    simp only [E₀, setLIntegral_indicator (measurableSet_triangle 0 s), inter_self]
  rw [heG, heE] at hle
  exact hle.trans (add_le_add le_rfl hE)

private theorem scalar_area_coefficient {C D ε : ℝ} {X Y : ℝ≥0∞}
    (hD : 0 ≤ D) (hε : 0 ≤ ε) (hCD : 9 * D ≤ C) :
    ENNReal.ofReal 3 * (ENNReal.ofReal (D * ε) * (ENNReal.ofReal 3 * X) * Y) ≤
      ENNReal.ofReal (C * ε) * X * Y := by
  have he : ENNReal.ofReal 3 * (ENNReal.ofReal (D * ε) * (ENNReal.ofReal 3 * X) * Y) =
      ENNReal.ofReal (9 * D * ε) * X * Y := by
    rw [show 9 * D * ε = 3 * (D * ε) * 3 by ring,
      ENNReal.ofReal_mul (by positivity : 0 ≤ 3 * (D * ε)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ac_rfl
  rw [he]
  exact mul_le_mul' (mul_le_mul'
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCD hε)) le_rfl) le_rfl

/-- The full forcing areas in both characteristic transports have a
coupled envelope majorant plus an electric error. The same universal `C`
is chosen before all data, depending only on the fixed box and uniformly
in higher initial derivatives. The coefficient includes the implemented
area constants, rather than the blueprint's sample numerical coefficient. -/
theorem characteristic_forcing_area_budgets :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ε ≤ 1 / 8 →
    let J := ∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v
    let K := ∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u
    (∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v,
      ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
        (curv S u v + 2 * starRingEnd ℂ (curv S u v)) + emSourceJ e S u v‖ₑ) ≤
      ENNReal.ofReal (C * ε) * K * J +
        ENNReal.ofReal (C * (|e| * (s / 2) * M) ^ 2 * ε) ∧
    (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
      ‖S.lam u v * S.xi u v / S.r u v ^ 2 *
        (starRingEnd ℂ (curv S u v) + 2 * curv S u v) + emSourceK e S u v‖ₑ) ≤
      ENNReal.ofReal (C * ε) * J * K +
        ENNReal.ofReal (C * (|e| * (s / 2) * M) ^ 2 * ε) := by
  obtain ⟨Cj, hCj, hj⟩ := bv_area_j
  obtain ⟨Ck, hCk, hk⟩ := bv_area_k
  obtain ⟨Ce, hCe, he⟩ := characteristic_forcing_scalar_majorants
  let C := 9 * (Cj + Ck) + 4 * Ce
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro e s ε M S h hset hε
  dsimp only
  let J := ∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v
  let K := ∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u
  let Fj := fun p : ℝ × ℝ => ‖S.nu p.1 p.2 * S.theta p.1 p.2 / S.r p.1 p.2 ^ 2 *
    (curv S p.1 p.2 + 2 * starRingEnd ℂ (curv S p.1 p.2)) + emSourceJ e S p.1 p.2‖ₑ
  let Fk := fun p : ℝ × ℝ => ‖S.lam p.1 p.2 * S.xi p.1 p.2 / S.r p.1 p.2 ^ 2 *
    (starRingEnd ℂ (curv S p.1 p.2) + 2 * curv S p.1 p.2) + emSourceK e S p.1 p.2‖ₑ
  let Gj := fun p : ℝ × ℝ => ‖S.nu p.1 p.2 * S.theta p.1 p.2 / S.r p.1 p.2 ^ 2 *
    curvScalar (triangle 0 s) S p.1 p.2‖ₑ
  let Gk := fun p : ℝ × ℝ => ‖S.lam p.1 p.2 * S.xi p.1 p.2 / S.r p.1 p.2 ^ 2 *
    curvScalarIn e (triangle 0 s) S p.1 p.2‖ₑ
  have hε0 := hset.eps_nonneg
  have hA : 0 ≤ Ce * e ^ 2 * M ^ 2 * ε := by positivity
  have hFm := measurable_transport_forcing hset.pos hset.c1
  have hGm := measurable_scalar_transport hset.pos hset.c1
  have hp := he e s ε M S h hset (hε.trans (by norm_num))
  have hCJ : 9 * Cj ≤ C := by dsimp only [C]; linarith only [hCk, hCe]
  have hCK : 9 * Ck ≤ C := by dsimp only [C]; linarith only [hCj, hCe]
  have hCE : 4 * Ce ≤ C := by dsimp only [C]; linarith only [hCj, hCk]
  have hE : ENNReal.ofReal (4 * (Ce * e ^ 2 * M ^ 2 * ε) * (s / 2) ^ 2) ≤
      ENNReal.ofReal (C * (|e| * (s / 2) * M) ^ 2 * ε) := by
    apply ENNReal.ofReal_le_ofReal
    simp only [mul_pow, sq_abs]
    have hi := mul_le_mul_of_nonneg_right hCE
      (show 0 ≤ e ^ 2 * M ^ 2 * (s / 2) ^ 2 * ε by positivity)
    nlinarith only [hi]
  have hpointj (u v : ℝ) (hpuv : (u, v) ∈ triangle 0 s) : Fj (u, v) ≤
      ENNReal.ofReal 3 * Gj (u, v) +
        ENNReal.ofReal ((Ce * e ^ 2 * M ^ 2 * ε) * (-S.nu u v) * S.lam u v) := by
    have hi := ENNReal.ofReal_le_ofReal (hp u v hpuv).1
    have hscalar : 0 ≤ 3 * ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
        curvScalar (triangle 0 s) S u v‖ := by positivity
    have hn := (neg_pos.mpr (hset.c1.nu_neg (u, v) hpuv)).le
    have hl := (hset.c1.lam_pos (u, v) hpuv).le
    have hgeom := mul_nonneg (mul_nonneg hA hn) hl
    rw [ENNReal.ofReal_add hscalar hgeom,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] at hi
    simpa only [Fj, Gj, ofReal_norm] using hi
  have hpointk (u v : ℝ) (hpuv : (u, v) ∈ triangle 0 s) : Fk (u, v) ≤
      ENNReal.ofReal 3 * Gk (u, v) +
        ENNReal.ofReal ((Ce * e ^ 2 * M ^ 2 * ε) * (-S.nu u v) * S.lam u v) := by
    have hi := ENNReal.ofReal_le_ofReal (hp u v hpuv).2
    have hscalar : 0 ≤ 3 * ‖S.lam u v * S.xi u v / S.r u v ^ 2 *
        curvScalarIn e (triangle 0 s) S u v‖ := by positivity
    have hn := (neg_pos.mpr (hset.c1.nu_neg (u, v) hpuv)).le
    have hl := (hset.c1.lam_pos (u, v) hpuv).le
    have hgeom := mul_nonneg (mul_nonneg hA hn) hl
    rw [ENNReal.ofReal_add hscalar hgeom,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] at hi
    simpa only [Fk, Gk, ofReal_norm] using hi
  constructor
  · have hplane := plane_area_majorant hset hA hGm.1 hpointj
    rw [(triangle_lintegral_orders hFm.1).2,
      (triangle_lintegral_orders hGm.1).1] at hplane
    have hscalar := (hj e s ε M S h hset).trans
      (mul_le_mul' (mul_le_mul' le_rfl (incoming_variation_sup_le hset hε)) le_rfl)
    have hs := (mul_le_mul' le_rfl hscalar).trans
      (scalar_area_coefficient hCj.le hε0 hCJ (X := K) (Y := J))
    exact hplane.trans (add_le_add hs hE)
  · have hplane := plane_area_majorant hset hA hGm.2 hpointk
    rw [(triangle_lintegral_orders hFm.2).1,
      (triangle_lintegral_orders hGm.2).2] at hplane
    have hscalar := (hk e s ε M S h hset).trans
      (mul_le_mul' (mul_le_mul' le_rfl (outgoing_variation_sup_le hset hε)) le_rfl)
    have hs := (mul_le_mul' le_rfl hscalar).trans
      (scalar_area_coefficient hCk.le hε0 hCK (X := J) (Y := K))
    exact hplane.trans (add_le_add hs hE)

end EmcsfAcExtension.Local
