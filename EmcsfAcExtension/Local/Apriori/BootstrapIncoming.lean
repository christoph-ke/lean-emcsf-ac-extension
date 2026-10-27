module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFinal
import EmcsfAcExtension.Local.Apriori.Potential
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.AreaJAux
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff
import EmcsfAcExtension.Infra.AC.Variation

/-! # Ordinary incoming scalar variation in the axis gauge

The covariant derivative budget is converted to ordinary variation using
only the axis-gauge potential bound and the actual scalar background
(`charged_SF_new_version.tex:L4909–L4918`, approved internal project record (44)).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-area#ordinary-incoming-variation]
The ordinary incoming variation of the normalized scalar is at most
`C ε` on every complete incoming section. The positive thresholds and `C`
precede every datum and depend only on the fixed box, uniformly in higher
initial derivatives. The charged background remains inside the explicit
potential estimate. -/
theorem ordinary_incoming_variation : ∃ ε₀ δ₀ C : ℝ,
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
    ∀ v ∈ Icc 0 T, eVariationOn (fun u => S.b u v) (Icc 0 v) ≤ ENNReal.ofReal (C * ε) := by
  obtain ⟨ε₀, δ₁, hε₀, hδ₁, hclosed⟩ := bv_envelope_final_individual
  obtain ⟨Ca, hCa, hpotential⟩ := axis_gauge_potential_bound
  refine ⟨ε₀, min δ₁ 1, 2 + 8 * Ca, hε₀, lt_min hδ₁ (by norm_num), by positivity, ?_⟩
  intro e T ε M S h hset hε hδ v hv
  obtain ⟨_, _, _, hV⟩ := hclosed e T ε M S h hset hε (hδ.trans (min_le_left _ _))
  have hε0 := hset.eps_nonneg
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hset.one_le_M
  have h4ε : 4 * ε ≤ M := by rw [hset.M_eq]; have := norm_nonneg (h 0); linarith
  have hs : MapsTo (fun x : ℝ => (x, v)) (Icc 0 v) (triangle 0 T) :=
    fun x hx => ⟨hx.1, hx.2, hv.2⟩
  let q : ℝ → ℂ := fun x => pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v
  have cp := continuousOn_pdU hset.c1.c1_b (uniqueDiffOn_triangle hset.pos)
  have cq : ContinuousOn q (Icc 0 v) := by
    apply (cp.add (((continuousOn_const (c := I * e)).mul
      (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_A.continuousOn)).mul
        hset.c1.c1_b.continuousOn)).comp
          (continuous_id.prodMk continuous_const).continuousOn hs
  have iq := cq.intervalIntegrable_of_Icc (μ := volume) hv.1
  have heq : ENNReal.ofReal (∫ x in 0..v, ‖q x‖) = ∫⁻ x in Icc 0 v, ‖q x‖ₑ := by
    rw [intervalIntegral.integral_of_le hv.1, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_norm_eq_lintegral_enorm
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mp iq)
  have hcov : (∫ x in 0..v, ‖q x‖) ≤ 3 / 2 * ε := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 3 / 2 * ε)).mp
    rw [heq]
    exact (le_iSup₂_of_le v hv le_rfl).trans hV
  have cder : ContinuousOn (fun x => pdU (triangle 0 T) S.b x v) (Icc 0 v) :=
    cp.comp (continuous_id.prodMk continuous_const).continuousOn hs
  have cb : ContDiffOn ℝ 1 (fun x => S.b x v) (Icc 0 v) :=
    hset.c1.c1_b.comp (contDiffOn_id.prodMk contDiffOn_const) hs
  have hac : AbsolutelyContinuousOnInterval (fun x => S.b x v) 0 v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hv.1] using cb
  have hvar : eVariationOn (fun x => S.b x v) (Icc 0 v) =
      ENNReal.ofReal (∫ x in 0..v, ‖pdU (triangle 0 T) S.b x v‖) := by
    rw [hac.eVariationOn_eq_integral_norm_deriv hv.1]
    congr 1
    apply intervalIntegral.integral_congr_ae
    have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff, measure_singleton]
    have hve : ∀ᵐ x : ℝ, x ≠ v := by simp [ae_iff, measure_singleton]
    filter_upwards [h0, hve] with x hx0 hxv hx
    rw [uIoc_of_le hv.1] at hx
    have hd := (hasDerivWithinAt_pdU hset.c1.c1_b (hs ⟨hx.1.le, hx.2⟩) hs).hasDerivAt
      (Icc_mem_nhds hx.1 (lt_of_le_of_ne hx.2 hxv))
    rw [hd.deriv]
  have point (x : ℝ) (hx : x ∈ Icc 0 v) :
      ‖pdU (triangle 0 T) S.b x v‖ ≤ ‖q x‖ + 2 * Ca * e ^ 2 * M ^ 2 * ε * T := by
    have hp := hs hx
    have hb : ‖S.b x v‖ ≤ 2 * M := by
      rw [Fields.b]
      have hi := (norm_add_le (S.phi x v) (S.xi x v / S.nu x v)).trans
        (add_le_add (hset.box (x, v) hp).2.2.2.2.2.1 (hset.box (x, v) hp).2.2.2.2.2.2.2)
      linarith only [hi, h4ε]
    have hA := (hpotential e T ε M S h hset x v hp).2
    have hr0 := hset.radius_nonneg hp
    have hrT : S.r x v ≤ T := (Area.radius_bounds hset hx.1 hx.2 hv.2).2.trans
      (by linarith only [hx.1, hv.2])
    have hg : ‖I * e * S.A x v * S.b x v‖ ≤ 2 * Ca * e ^ 2 * M ^ 2 * ε * T := by
      simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ |e| * (Ca * |e| * M * ε * S.r x v) * (2 * M) := by gcongr
        _ ≤ |e| * (Ca * |e| * M * ε * T) * (2 * M) := by gcongr
        _ = _ := by rw [← sq_abs]; ring
    have hid : pdU (triangle 0 T) S.b x v = q x - I * e * S.A x v * S.b x v := by
      dsimp only [q]
      ring
    rw [hid]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hg)
  have hi := intervalIntegral.integral_mono_on hv.1
    ((cder.intervalIntegrable_of_Icc (μ := volume) hv.1).norm)
    (iq.norm.add intervalIntegrable_const) point
  rw [intervalIntegral.integral_add iq.norm intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  have hscale0 : 0 ≤ |e| * (T / 2) * M := by have := hset.pos; positivity
  have hscale2 : (|e| * (T / 2) * M) ^ 2 ≤ 1 := by
    nlinarith only [hscale0, hδ.trans (min_le_right δ₁ 1)]
  have hel : v * (2 * Ca * e ^ 2 * M ^ 2 * ε * T) ≤ 8 * Ca * ε := by
    have hvbound := mul_le_mul_of_nonneg_right hv.2
      (show 0 ≤ 2 * Ca * e ^ 2 * M ^ 2 * ε * T by have := hset.pos; positivity)
    have hsbound := mul_le_mul_of_nonneg_right hscale2 (show 0 ≤ 8 * Ca * ε by positivity)
    simp only [mul_pow, sq_abs] at hsbound
    nlinarith only [hvbound, hsbound]
  rw [hvar]
  apply ENNReal.ofReal_le_ofReal
  linarith only [hi, hcov, hel, hε0]

/-- [node restart-sec-independent-area#ordinary-incoming-variation]
The sharper ordinary/covariant incoming conversion of charged_SF_new_version.tex:L4914–4921,
on every shortened incoming segment, including degenerate ones.
The positive constant depends only on the fixed bootstrap box, before every
parameter and datum, uniformly in all higher initial derivatives. The error
retains the explicit square of `δ = |e| (T/2) M`; no smallness substitution
`δ² ≤ 1` is made. The standing box alone suffices for this comparison. -/
theorem ordinary_incoming_variation_conversion : ∃ C : ℝ, 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ T →
      (∫ x in u..v, ‖pdU (triangle 0 T) S.b x v‖) ≤
        (∫ x in u..v,
          ‖pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v‖) +
          C * (|e| * (T / 2) * M) ^ 2 * ε := by
  obtain ⟨Ca, hCa, hpotential⟩ := axis_gauge_potential_bound
  refine ⟨8 * Ca, by positivity, ?_⟩
  intro e T ε M S h hset u v hu huv hvT
  have hε0 := hset.eps_nonneg
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hset.one_le_M
  have h4ε : 4 * ε ≤ M := by rw [hset.M_eq]; have := norm_nonneg (h 0); linarith
  have hs : MapsTo (fun x : ℝ => (x, v)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hu.trans hx.1, hx.2, hvT⟩
  let q : ℝ → ℂ := fun x => pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v
  have cp := continuousOn_pdU hset.c1.c1_b (uniqueDiffOn_triangle hset.pos)
  have cq : ContinuousOn q (Icc u v) := by
    apply (cp.add (((continuousOn_const (c := I * e)).mul
      (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_A.continuousOn)).mul
        hset.c1.c1_b.continuousOn)).comp
          (continuous_id.prodMk continuous_const).continuousOn hs
  have iq := cq.intervalIntegrable_of_Icc (μ := volume) huv
  have cder : ContinuousOn (fun x => pdU (triangle 0 T) S.b x v) (Icc u v) :=
    cp.comp (continuous_id.prodMk continuous_const).continuousOn hs
  have point (x : ℝ) (hx : x ∈ Icc u v) :
      ‖pdU (triangle 0 T) S.b x v‖ ≤ ‖q x‖ + 2 * Ca * e ^ 2 * M ^ 2 * ε * T := by
    have hp := hs hx
    have hb : ‖S.b x v‖ ≤ 2 * M := by
      rw [Fields.b]
      have hi := (norm_add_le (S.phi x v) (S.xi x v / S.nu x v)).trans
        (add_le_add (hset.box (x, v) hp).2.2.2.2.2.1 (hset.box (x, v) hp).2.2.2.2.2.2.2)
      linarith only [hi, h4ε]
    have hA := (hpotential e T ε M S h hset x v hp).2
    have hr0 := hset.radius_nonneg hp
    have hrT : S.r x v ≤ T := (Area.radius_bounds hset (hu.trans hx.1) hx.2 hvT).2.trans
      (by linarith only [hu, hx.1, hvT])
    have hg : ‖I * e * S.A x v * S.b x v‖ ≤ 2 * Ca * e ^ 2 * M ^ 2 * ε * T := by
      simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ |e| * (Ca * |e| * M * ε * S.r x v) * (2 * M) := by gcongr
        _ ≤ |e| * (Ca * |e| * M * ε * T) * (2 * M) := by gcongr
        _ = _ := by rw [← sq_abs]; ring
    have hid : pdU (triangle 0 T) S.b x v = q x - I * e * S.A x v * S.b x v := by
      dsimp only [q]
      ring
    rw [hid]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hg)
  have hi := intervalIntegral.integral_mono_on huv
    ((cder.intervalIntegrable_of_Icc (μ := volume) huv).norm)
    (iq.norm.add intervalIntegrable_const) point
  rw [intervalIntegral.integral_add iq.norm intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hi
  have herr : (v - u) * (2 * Ca * e ^ 2 * M ^ 2 * ε * T) ≤
      8 * Ca * (|e| * (T / 2) * M) ^ 2 * ε := by
    calc
      _ ≤ T * (2 * Ca * e ^ 2 * M ^ 2 * ε * T) :=
        mul_le_mul_of_nonneg_right (show v - u ≤ T by linarith only [hu, hvT])
          (by have := hset.pos; positivity)
      _ = _ := by rw [mul_pow, mul_pow, sq_abs]; ring
  exact hi.trans (add_le_add le_rfl herr)

end EmcsfAcExtension.Local
