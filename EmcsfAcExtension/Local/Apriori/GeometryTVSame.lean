module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Apriori.GeometryTVAux
import EmcsfAcExtension.Local.Apriori.GeometryEnvelope
import EmcsfAcExtension.Local.Apriori.GeometryEnvelopeRegular
import EmcsfAcExtension.Local.Apriori.GeometryBoxFlux
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Same-direction expansion variations

The geometric renormalizations control the missing outgoing derivative of
`λ` and incoming derivative of `ν`. Their quadratic corrections are the
closed scalar fluxes (`charged_SF_new_version.tex:L4895–L4897`).
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

private theorem outgoing_speed_bound {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    |pdV (triangle 0 T) S.lam u v| ≤ |geomL (triangle 0 T) S u v| +
      S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2 := by
  have hl := hset.c1.lam_pos (u, v) hp
  have hq : 0 ≤ S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2 :=
    mul_nonneg (div_nonneg hl.le (hset.radius_nonneg hp)) (sq_nonneg _)
  have heq : pdV (triangle 0 T) S.lam u v = S.lam u v *
      (geomL (triangle 0 T) S u v -
        S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2) := by
    rw [geomL]
    field_simp
    ring
  rw [heq, abs_mul, abs_of_pos hl]
  calc
    _ ≤ S.lam u v * (|geomL (triangle 0 T) S u v| +
        S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by
        have hb := abs_sub (geomL (triangle 0 T) S u v)
          (S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2)
        rwa [abs_of_nonneg hq] at hb) hl.le
    _ ≤ _ := mul_le_of_le_one_left (by positivity) (hset.box (u, v) hp).2.1

private theorem incoming_speed_bound {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    |pdU (triangle 0 T) S.nu u v| ≤ |geomN (triangle 0 T) S u v| +
      -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2 := by
  have hn := hset.c1.nu_neg (u, v) hp
  have hq : 0 ≤ -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2 :=
    mul_nonneg (div_nonneg (neg_pos.mpr hn).le (hset.radius_nonneg hp)) (sq_nonneg _)
  have heq : pdU (triangle 0 T) S.nu u v = S.nu u v *
      (geomN (triangle 0 T) S u v +
        -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2) := by
    rw [geomN]
    field_simp [hn.ne]
    ring
  rw [heq, abs_mul, abs_of_neg hn]
  calc
    _ ≤ (-S.nu u v) * (|geomN (triangle 0 T) S u v| +
        -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by
        have hb := abs_add_le (geomN (triangle 0 T) S u v)
          (-S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2)
        rwa [abs_of_nonneg hq] at hb) (neg_pos.mpr hn).le
    _ ≤ _ := mul_le_of_le_one_left (by positivity) (hset.box (u, v) hp).2.2.2.1

/-- [node restart-sec-independent-area#same-direction-expansion-variation]
The outgoing variation of `λ` and incoming variation of `ν` on every
complete axis-to-point segment are at most `C ε²`. The positive thresholds
and `C` precede every datum and depend only on the fixed box, uniformly in
higher initial derivatives. The geometric envelopes control both directions. -/
theorem same_direction_expansion_variation : ∃ ε₀ δ₀ C : ℝ,
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
    ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      eVariationOn (S.lam u) (Icc u v) ≤ ENNReal.ofReal (C * ε ^ 2) ∧
      eVariationOn (fun x => S.nu x v) (Icc u v) ≤ ENNReal.ofReal (C * ε ^ 2) := by
  obtain ⟨ε₁, δ₁, Co, hε₁, hδ₁, hCo, hout⟩ := outgoing_geometric_envelope
  obtain ⟨ε₂, δ₂, Ci, hε₂, hδ₂, hCi, hin⟩ := incoming_geometric_envelope
  obtain ⟨ε₃, δ₃, hε₃, hδ₃, hflux⟩ := closed_quadratic_scalar_budgets
  refine ⟨min ε₁ (min ε₂ ε₃), min δ₁ (min δ₂ δ₃), Co + Ci + 14,
    lt_min hε₁ (lt_min hε₂ hε₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), by positivity, ?_⟩
  intro e T ε M S h hset hε hδ u v hu huv hvT
  have he1 := hε.trans (min_le_left _ _)
  have he2 := (hε.trans (min_le_right _ _)).trans (min_le_left _ _)
  have he3 := (hε.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hd1 := hδ.trans (min_le_left _ _)
  have hd2 := (hδ.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hd3 := (hδ.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hquad := hset.quadratic_scalar_integrable hu huv hvT
  have hf := hflux e T ε M S h hset he3 hd3 u v hu huv hvT
  have po (x : ℝ) (hx : x ∈ Icc u v) : (u, x) ∈ triangle 0 T :=
    ⟨hu, hx.1, hx.2.trans hvT⟩
  have pi (x : ℝ) (hx : x ∈ Icc u v) : (x, v) ∈ triangle 0 T :=
    ⟨hu.trans hx.1, hx.2, hvT⟩
  constructor
  · have cL : ContinuousOn (fun x => geomL (triangle 0 T) S u x) (Icc u v) :=
      (continuousOn_geomL hset.pos hset.c1).comp (f := fun x : ℝ => (u, x))
        (continuous_const.prodMk continuous_id).continuousOn (po · ·)
    have cg : ContinuousOn (pdV (triangle 0 T) S.lam u) (Icc u v) :=
      (continuousOn_pdV hset.c1.c1_lam (uniqueDiffOn_triangle hset.pos)).comp
        (continuous_const.prodMk continuous_id).continuousOn (po · ·)
    have cl : ContinuousOn (S.lam u) (Icc u v) :=
      hset.c1.c1_lam.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn (po · ·)
    have iL := cL.abs.intervalIntegrable_of_Icc (μ := volume) huv
    let B := fun x => |geomL (triangle 0 T) S u x| +
      S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2
    have hb := (ac_and_variation_le_of_interior_speed huv cl (cg.mono Ioo_subset_Icc_self)
      (fun x hx => (hasDerivWithinAt_pdV hset.c1.c1_lam
        (po x ⟨hx.1.le, hx.2.le⟩) (po · ·)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
      (iL.add hquad.1) (fun x hx => outgoing_speed_bound hset (po x ⟨hx.1.le, hx.2.le⟩))).2
    have hLe : ENNReal.ofReal (∫ x in u..v, |geomL (triangle 0 T) S u x|) ≤
        ∫⁻ x in Icc 0 T, outEnv 0 (geomL (triangle 0 T) S) x := by
      rw [intervalIntegral.integral_of_le huv, ← integral_Icc_eq_integral_Ioc]
      simp_rw [← Real.norm_eq_abs]
      rw [ofReal_integral_norm_eq_lintegral_enorm
          ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).mp
            (cL.intervalIntegrable_of_Icc (μ := volume) huv))]
      apply le_trans (b := ∫⁻ x in Icc u v, outEnv 0 (geomL (triangle 0 T) S) x)
      · apply setLIntegral_mono' measurableSet_Icc
        intro x hx
        exact enorm_le_normEnvelope (geomL (triangle 0 T) S) ⟨hu, hx.1⟩
      · exact lintegral_mono_set (Icc_subset_Icc hu hvT)
    have hQ0 : 0 ≤ ∫ x in u..v,
        S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2 :=
      intervalIntegral.integral_nonneg huv (fun x hx => mul_nonneg
        (div_nonneg (hset.c1.lam_pos (u, x) (po x hx)).le
          (hset.radius_nonneg (po x hx))) (sq_nonneg _))
    have hL0 : 0 ≤ ∫ x in u..v, |geomL (triangle 0 T) S u x| :=
      intervalIntegral.integral_nonneg huv (fun x _ => abs_nonneg _)
    apply hb.trans
    change ENNReal.ofReal (∫ x in u..v, B x) ≤ _
    rw [intervalIntegral.integral_add iL hquad.1, ENNReal.ofReal_add hL0 hQ0]
    apply (add_le_add (hLe.trans (hout e T ε M S h hset he1 hd1))
      (ENNReal.ofReal_le_ofReal hf.1)).trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn := mul_nonneg hCi.le (sq_nonneg ε)
    nlinarith only [hn]
  · have cN : ContinuousOn (fun x => geomN (triangle 0 T) S x v) (Icc u v) :=
      (continuousOn_geomN hset.pos hset.c1).comp (f := fun x : ℝ => (x, v))
        (continuous_id.prodMk continuous_const).continuousOn (pi · ·)
    have cg : ContinuousOn (fun x => pdU (triangle 0 T) S.nu x v) (Icc u v) :=
      (continuousOn_pdU hset.c1.c1_nu (uniqueDiffOn_triangle hset.pos)).comp
        (continuous_id.prodMk continuous_const).continuousOn (pi · ·)
    have cn : ContinuousOn (fun x => S.nu x v) (Icc u v) :=
      hset.c1.c1_nu.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn (pi · ·)
    have iN := cN.abs.intervalIntegrable_of_Icc (μ := volume) huv
    let B := fun x => |geomN (triangle 0 T) S x v| +
      -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2
    have hb := (ac_and_variation_le_of_interior_speed huv cn (cg.mono Ioo_subset_Icc_self)
      (fun x hx => (hasDerivWithinAt_pdU hset.c1.c1_nu
        (pi x ⟨hx.1.le, hx.2.le⟩) (pi · ·)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
      (iN.add hquad.2) (fun x hx => incoming_speed_bound hset (pi x ⟨hx.1.le, hx.2.le⟩))).2
    have hNe : ENNReal.ofReal (∫ x in u..v, |geomN (triangle 0 T) S x v|) ≤
        ∫⁻ x in Icc 0 T, inEnv T (geomN (triangle 0 T) S) x := by
      rw [intervalIntegral.integral_of_le huv, ← integral_Icc_eq_integral_Ioc]
      simp_rw [← Real.norm_eq_abs]
      rw [ofReal_integral_norm_eq_lintegral_enorm
          ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).mp
            (cN.intervalIntegrable_of_Icc (μ := volume) huv))]
      apply le_trans (b := ∫⁻ x in Icc u v, inEnv T (geomN (triangle 0 T) S) x)
      · apply setLIntegral_mono' measurableSet_Icc
        intro x hx
        exact le_iSup₂_of_le v (show v ∈ Icc x T from ⟨hx.2, hvT⟩) le_rfl
      · exact lintegral_mono_set (Icc_subset_Icc hu hvT)
    have hQ0 : 0 ≤ ∫ x in u..v,
        -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2 :=
      intervalIntegral.integral_nonneg huv (fun x hx => mul_nonneg
        (div_nonneg (neg_pos.mpr (hset.c1.nu_neg (x, v) (pi x hx))).le
          (hset.radius_nonneg (pi x hx))) (sq_nonneg _))
    have hN0 : 0 ≤ ∫ x in u..v, |geomN (triangle 0 T) S x v| :=
      intervalIntegral.integral_nonneg huv (fun x _ => abs_nonneg _)
    apply hb.trans
    change ENNReal.ofReal (∫ x in u..v, B x) ≤ _
    rw [intervalIntegral.integral_add iN hquad.2, ENNReal.ofReal_add hN0 hQ0]
    apply (add_le_add (hNe.trans (hin e T ε M S h hset he2 hd2))
      (ENNReal.ofReal_le_ofReal hf.2)).trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn := mul_nonneg hCo.le (sq_nonneg ε)
    nlinarith only [hn]

end EmcsfAcExtension.Local
