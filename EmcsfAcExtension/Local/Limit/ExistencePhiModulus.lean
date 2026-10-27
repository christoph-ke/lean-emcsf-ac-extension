module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Defs.Bounds
public import EmcsfAcExtension.Infra.UnifIntegrable
import EmcsfAcExtension.Local.Limit.ExistenceHardy
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Infra.BV.Semicontinuity

/-! # Shrinking scalar variation at the axis

Uniform integrability of the actual classical envelopes controls every
short interval. Localized Hardy bounds and the ordinary connection remainder
then pass through variation semicontinuity to the frozen scalar condition.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem interval_mass_small {F : ℕ → ℝ → ℝ} {T : ℝ}
    (hF : ∀ n, IntegrableOn (F n) (Icc 0 T)) (h0 : ∀ n x, 0 ≤ F n x)
    (hUI : UnifIntegrable F 1 (volume.restrict (Icc 0 T))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n a b, 0 ≤ a → a ≤ b → b ≤ T → b - a ≤ δ →
      (∫ x in a..b, F n x) ≤ ε := by
  obtain ⟨δ, hδ, hsmall⟩ := (unifIntegrable_iff.1 hUI) (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.mpr hε)
  have hdreal : ∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d ≤ δ := by
    by_cases ht : δ = ⊤
    · exact ⟨1, zero_lt_one, ht ▸ le_top⟩
    · exact ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' ht, (ENNReal.ofReal_toReal ht).le⟩
  obtain ⟨d, hd, hde⟩ := hdreal
  refine ⟨d, hd, ?_⟩
  intro n a b ha hab hb hlen
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha hb
  have hmeasure : (volume.restrict (Icc 0 T)) (Icc a b) ≤ δ := by
    apply (Measure.restrict_apply_le (μ := volume) (Icc 0 T) (Icc a b)).trans
    rw [Real.volume_Icc]
    exact (ENNReal.ofReal_le_ofReal hlen).trans hde
  have hh := hsmall n (Icc a b) hmeasure
  have hi : IntegrableOn (F n) (Icc a b) := (hF n).mono_set hsub
  rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub,
    eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable] at hh
  have heq : ENNReal.ofReal (∫ x in a..b, F n x) = ∫⁻ x in Icc a b, ‖F n x‖ₑ := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    convert ofReal_integral_norm_eq_lintegral_enorm hi using 1
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    exact (Real.norm_of_nonneg (h0 n x)).symm
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 (heq ▸ hh)

private theorem axis_modulus_of_local_bounds {T C B : ℝ}
    {F : ℕ → ℝ → ℝ → ℂ} {f : ℝ → ℝ → ℂ} {J K : ℕ → ℝ → ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hlim : TendstoUniformlyOn (fun n => Function.uncurry (F n)) (Function.uncurry f)
      atTop (triangle 0 T))
    (hJ : ∀ n, IntegrableOn (J n) (Icc 0 T)) (hJ0 : ∀ n x, 0 ≤ J n x)
    (hK : ∀ n, IntegrableOn (K n) (Icc 0 T)) (hK0 : ∀ n x, 0 ≤ K n x)
    (hUIj : UnifIntegrable J 1 (volume.restrict (Icc 0 T)))
    (hUIk : UnifIntegrable K 1 (volume.restrict (Icc 0 T)))
    (hb : ∀ᶠ n in atTop, ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      eVariationOn (F n u) (Icc u v) ≤ ENNReal.ofReal (C * ∫ x in u..v, J n x) ∧
      eVariationOn (fun x => F n x v) (Icc u v) ≤
        ENNReal.ofReal (C * ∫ x in u..v, K n x) + ENNReal.ofReal (B * (v - u))) :
    ∀ t, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      (∀ u a b, outSeg u a b ⊆ triangle 0 T ∩ triangle (t - δ) (t + δ) →
        eVariationOn (f u) (Icc a b) ≤ ENNReal.ofReal η) ∧
      (∀ a b v, inSeg a b v ⊆ triangle 0 T ∩ triangle (t - δ) (t + δ) →
        eVariationOn (fun u => f u v) (Icc a b) ≤ ENNReal.ofReal η) := by
  intro t η hη
  let ε := η / (4 * (C + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hCε : C * ε ≤ η / 4 := by
    have he : (C + 1) * ε = η / 4 := by dsimp [ε]; field_simp
    linarith only [he, hε]
  obtain ⟨dj, hdj, hj⟩ := interval_mass_small hJ hJ0 hUIj hε
  obtain ⟨dk, hdk, hk⟩ := interval_mass_small hK hK0 hUIk hε
  let δ := min (dj / 2) (min (dk / 2) (η / (8 * (B + 1))))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hdj' : 2 * δ ≤ dj := by
    have hh : δ ≤ dj / 2 := min_le_left _ _
    linarith only [hh]
  have hdk' : 2 * δ ≤ dk := by
    have hh : δ ≤ dk / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith only [hh]
  have hBδ : B * (2 * δ) ≤ η / 4 := by
    have hh : δ ≤ η / (8 * (B + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hp : 0 < 8 * (B + 1) := by positivity
    have hmul := (le_div_iff₀ hp).1 hh
    nlinarith only [hmul, hδ]
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro u a b hseg
    by_cases hab : a ≤ b
    · have ha := hseg (show (u, a) ∈ outSeg u a b from ⟨rfl, le_rfl, hab⟩)
      have hb' := hseg (show (u, b) ∈ outSeg u a b from ⟨rfl, hab, le_rfl⟩)
      have hlen : b - u ≤ 2 * δ := by linarith only [ha.2.1, hb'.2.2.2]
      apply eVariationOn.le_of_tendsto_of_eventually_le
        (F := fun n x => F n u x) (f := f u) (s := Icc a b)
        (fun x hx => hlim.tendsto_at
          (show (u, x) ∈ triangle 0 T from (hseg ⟨rfl, hx.1, hx.2⟩).1))
      filter_upwards [hb] with n hn
      have hv := (hn u b ha.1.1 (ha.1.2.1.trans hab) hb'.1.2.2).1
      calc
        eVariationOn (F n u) (Icc a b) ≤ eVariationOn (F n u) (Icc u b) :=
          eVariationOn.mono (F n u) (Icc_subset_Icc ha.1.2.1 le_rfl)
        _ ≤ ENNReal.ofReal (C * ∫ x in u..b, J n x) := hv
        _ ≤ ENNReal.ofReal (C * ε) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (hj n u b ha.1.1 (ha.1.2.1.trans hab) hb'.1.2.2 (hlen.trans hdj')) hC)
        _ ≤ _ := ENNReal.ofReal_le_ofReal (hCε.trans (by linarith only [hη]))
    · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab), eVariationOn]
  · intro a b v hseg
    by_cases hab : a ≤ b
    · have ha := hseg (show (a, v) ∈ inSeg a b v from ⟨le_rfl, hab, rfl⟩)
      have hb' := hseg (show (b, v) ∈ inSeg a b v from ⟨hab, le_rfl, rfl⟩)
      have hlen : v - a ≤ 2 * δ := by linarith only [ha.2.1, hb'.2.2.2]
      apply eVariationOn.le_of_tendsto_of_eventually_le
        (F := fun n x => F n x v) (f := fun x => f x v) (s := Icc a b)
        (fun x hx => hlim.tendsto_at
          (show (x, v) ∈ triangle 0 T from (hseg ⟨hx.1, hx.2, rfl⟩).1))
      filter_upwards [hb] with n hn
      have hv := (hn a v ha.1.1 ha.1.2.1 ha.1.2.2).2
      have hCv := mul_le_mul_of_nonneg_left
        (hk n a v ha.1.1 ha.1.2.1 ha.1.2.2 (hlen.trans hdk')) hC
      have hBv := (mul_le_mul_of_nonneg_left hlen hB).trans hBδ
      calc
        eVariationOn (fun x => F n x v) (Icc a b) ≤
            eVariationOn (fun x => F n x v) (Icc a v) :=
          eVariationOn.mono (fun x => F n x v) (Icc_subset_Icc le_rfl hb'.1.2.1)
        _ ≤ _ := hv
        _ ≤ ENNReal.ofReal (C * ε) + ENNReal.ofReal (η / 4) :=
          add_le_add (ENNReal.ofReal_le_ofReal hCv) (ENNReal.ofReal_le_ofReal hBv)
        _ ≤ ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4) :=
          add_le_add (ENNReal.ofReal_le_ofReal hCε) le_rfl
        _ ≤ _ := by
          rw [← ENNReal.ofReal_add (by positivity : 0 ≤ η / 4) (by positivity : 0 ≤ η / 4)]
          exact ENNReal.ofReal_le_ofReal (by linarith only [hη])
    · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab), eVariationOn]

/-- The frozen shrinking-triangle scalar variation condition follows from
the actual smooth Hardy bounds and UI of the two classical envelopes.
The smooth coefficient `C` retains its original scope. The shrinking modulus
may depend on the fixed family, coupling and triangle, as the frozen clause
permits; no derivative supremum bound is assumed. -/
theorem StrongLimit.axis_small_var_of_smoothBounds {C e T M : ℝ}
    {Sn : ℕ → Fields} {dn Mn : ℕ → ℝ} {S : Fields}
    (hT : 0 < T) (hC : 0 ≤ C) (hM : 0 ≤ M) (hMn : ∀ n, 0 ≤ Mn n)
    (hc1 : ∀ n, IsC1Solution e (Sn n) (triangle 0 T)) (hlim : StrongLimit e T Sn S)
    (hMl : Tendsto Mn atTop (𝓝 M))
    (hb : ∀ n, SmoothBounds C e T (dn n) (Mn n) (Sn n))
    (hUIj : UnifIntegrable (fun n v => (outEnv 0 (jC1 (triangle 0 T) (Sn n)) v).toReal)
      1 (volume.restrict (Icc 0 T)))
    (hUIk : UnifIntegrable (fun n u => (inEnv T (kC1 e (triangle 0 T) (Sn n)) u).toReal)
      1 (volume.restrict (Icc 0 T))) :
    ∀ t, (t, t) ∈ triangle 0 T → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      (∀ u a b, outSeg u a b ⊆ triangle 0 T ∩ triangle (t - δ) (t + δ) →
        eVariationOn (S.phi u) (Icc a b) ≤ ENNReal.ofReal η) ∧
      (∀ a b v, inSeg a b v ⊆ triangle 0 T ∩ triangle (t - δ) (t + δ) →
        eVariationOn (fun u => S.phi u v) (Icc a b) ≤ ENNReal.ofReal η) := by
  have ca := hlim.unif_A.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_A.continuousOn).frequently
  obtain ⟨B₀, hB₀⟩ := (isCompact_triangle 0 T).bddAbove_image ca.norm
  let B := max 0 (B₀ + 1)
  have hB : 0 ≤ B := le_max_left _ _
  have hAe : ∀ᶠ n in atTop, ∀ p ∈ triangle 0 T, |(Sn n).A p.1 p.2| ≤ B := by
    have he := (uniformContinuous_norm.comp_tendstoUniformlyOn hlim.unif_A).eventually_forall_le
      (show B₀ < B₀ + 1 by linarith) (fun p hp => hB₀ (mem_image_of_mem _ hp))
    filter_upwards [he] with n hn p hp
    have hx : |(Sn n).A p.1 p.2| ≤ B₀ + 1 := by
      simpa only [Real.norm_eq_abs, Function.uncurry_apply_pair, Function.comp_def] using! hn p hp
    exact hx.trans (le_max_right _ _)
  have hMe : ∀ᶠ n in atTop, Mn n ≤ M + 1 :=
    ((tendsto_order.1 hMl).2 (M + 1) (by linarith)).mono fun _ h => h.le
  have hj n : IntegrableOn (fun v => (outEnv 0 (jC1 (triangle 0 T) (Sn n)) v).toReal) (Icc 0 T) :=
    integrable_toReal_of_lintegral_ne_top (aemeasurable_outEnv ((hc1 n).continuousOn_jC1 hT))
      (outEnv_lintegral_ne_top_of_continuousOn ((hc1 n).continuousOn_jC1 hT))
  have hk n : IntegrableOn (fun u => (inEnv T (kC1 e (triangle 0 T) (Sn n)) u).toReal) (Icc 0 T) :=
    integrable_toReal_of_lintegral_ne_top (aemeasurable_inEnv ((hc1 n).continuousOn_kC1 hT))
      (inEnv_lintegral_ne_top_of_continuousOn ((hc1 n).continuousOn_kC1 hT))
  apply fun t _ => axis_modulus_of_local_bounds hC (show 0 ≤ |e| * B * (M + 1) by positivity)
    hlim.unif_phi hj (fun _ _ => ENNReal.toReal_nonneg) hk (fun _ _ => ENNReal.toReal_nonneg)
    hUIj hUIk ?_ t
  filter_upwards [hAe, hMe] with n hAn hMbound u v hu huv hv
  refine ⟨phi_out_variation_of_bounds (hc1 n) (hb n) hu huv hv,
    (phi_in_variation_of_bounds hB (hMn n) (hc1 n) (hb n) hAn hu huv hv).trans ?_⟩
  apply add_le_add le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hMbound (mul_nonneg (abs_nonneg _) hB)) (sub_nonneg.mpr huv)

end EmcsfAcExtension.Local
