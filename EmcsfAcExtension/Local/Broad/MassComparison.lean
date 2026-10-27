module

public import EmcsfAcExtension.Local.Broad.Mass
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Broad.Charge

/-! # Comparison of positive radial mass averages

All weight and radial-denominator errors are retained at the same null labels.
This is the mass-operator calculation (T)–(MD) in the approved internal project record.
-/

public section

open Set MeasureTheory Filter Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

private theorem scalar_mass_difference_of_bounds {μ₁ μ₂ ε H X : ℝ} {f₁ f₂ : ℂ}
    (hμ₁ : 0 ≤ μ₁) (hμ₁' : μ₁ ≤ 1) (_hε : 0 ≤ ε) (hH : 0 ≤ H) (hX : 0 ≤ X)
    (hf₁ : ‖f₁‖ ≤ ε) (hf₂ : ‖f₂‖ ≤ ε) (hδf : ‖f₁ - f₂‖ ≤ H)
    (hδμ : |μ₁ - μ₂| ≤ X) :
    |(1 - μ₁) * ‖f₁‖ ^ 2 - (1 - μ₂) * ‖f₂‖ ^ 2| ≤ 2 * ε * H + ε ^ 2 * X := by
  have hsq : |‖f₁‖ ^ 2 - ‖f₂‖ ^ 2| ≤ 2 * ε * H := by
    rw [show ‖f₁‖ ^ 2 - ‖f₂‖ ^ 2 = (‖f₁‖ - ‖f₂‖) * (‖f₁‖ + ‖f₂‖) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc
      _ ≤ H * (ε + ε) := mul_le_mul ((abs_norm_sub_norm_le _ _).trans hδf)
        (add_le_add hf₁ hf₂) (add_nonneg (norm_nonneg _) (norm_nonneg _)) hH
      _ = _ := by ring
  have heq : (1 - μ₁) * ‖f₁‖ ^ 2 - (1 - μ₂) * ‖f₂‖ ^ 2 =
      (1 - μ₁) * (‖f₁‖ ^ 2 - ‖f₂‖ ^ 2) - (μ₁ - μ₂) * ‖f₂‖ ^ 2 := by ring
  rw [heq]
  calc
    _ ≤ |(1 - μ₁) * (‖f₁‖ ^ 2 - ‖f₂‖ ^ 2)| + |(μ₁ - μ₂) * ‖f₂‖ ^ 2| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        ((1 - μ₁) * (‖f₁‖ ^ 2 - ‖f₂‖ ^ 2)) ((μ₁ - μ₂) * ‖f₂‖ ^ 2)
    _ = (1 - μ₁) * |‖f₁‖ ^ 2 - ‖f₂‖ ^ 2| + |μ₁ - μ₂| * ‖f₂‖ ^ 2 := by
      simp only [abs_mul, abs_of_nonneg (sub_nonneg.mpr hμ₁'),
        abs_of_nonneg (sq_nonneg ‖f₂‖)]
    _ ≤ 1 * (2 * ε * H) + X * ε ^ 2 := by
      gcongr
      linarith
    _ = _ := by ring

/-- Difference of two positive weighted radial averages at the same labels.
The displayed coefficient depends only on the lower weight bound `c` and
the two-sided weight/radius comparison factor `k`. Every weight and radial
denominator error is retained. This algebraic helper requires no regularity
besides the three stated integrabilities. -/
theorem average_difference_le_of_bounds
    {a b R₁ R₂ c k G : ℝ} {w₁ w₂ F₁ F₂ : ℝ → ℝ}
    (hab : a ≤ b) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hc : 0 < c)
    (hk : 0 ≤ k) (hG : 0 ≤ G)
    (hw₁ : ∀ x ∈ Icc a b, c ≤ w₁ x) (hw₂ : ∀ x ∈ Icc a b, 0 ≤ w₂ x)
    (hF₂ : ∀ x ∈ Icc a b, 0 ≤ F₂ x)
    (hwratio : ∀ x ∈ Icc a b, w₁ x ≤ k * w₂ x)
    (hδw : ∀ x ∈ Icc a b, |w₁ x - w₂ x| ≤ G)
    (hRratio : R₂ ≤ k * R₁) (hδR : |R₁ - R₂| ≤ G * R₁)
    (i₁₁ : IntervalIntegrable (fun x => w₁ x * F₁ x) volume a b)
    (i₁₂ : IntervalIntegrable (fun x => w₁ x * F₂ x) volume a b)
    (i₂₂ : IntervalIntegrable (fun x => w₂ x * F₂ x) volume a b) :
    |R₁⁻¹ * (∫ x in a..b, w₁ x * F₁ x) - R₂⁻¹ * (∫ x in a..b, w₂ x * F₂ x)| ≤
      R₁⁻¹ * (∫ x in a..b, w₁ x * |F₁ x - F₂ x|) +
        (k ^ 2 / c + 1) * G * (R₂⁻¹ * ∫ x in a..b, w₂ x * F₂ x) := by
  let T₂ := R₂⁻¹ * ∫ x in a..b, w₂ x * F₂ x
  let T₁₂ := R₁⁻¹ * ∫ x in a..b, w₁ x * F₂ x
  have hw₁0 x (hx : x ∈ Icc a b) : 0 ≤ w₁ x := hc.le.trans (hw₁ x hx)
  have hT₂ : 0 ≤ T₂ := mul_nonneg (inv_nonneg.mpr hR₂.le)
    (intervalIntegral.integral_nonneg hab (fun x hx => mul_nonneg (hw₂ x hx) (hF₂ x hx)))
  have hT₁₂ : T₁₂ ≤ k ^ 2 * T₂ := by
    have hmix := intervalIntegral.integral_mono_on hab i₁₂ (i₂₂.const_mul k)
      (fun x hx => by
        calc
          _ ≤ (k * w₂ x) * F₂ x := mul_le_mul_of_nonneg_right (hwratio x hx) (hF₂ x hx)
          _ = _ := by ring)
    rw [intervalIntegral.integral_const_mul] at hmix
    have hR := (div_le_iff₀ hR₁).mpr hRratio
    calc
      _ ≤ R₁⁻¹ * (k * ∫ x in a..b, w₂ x * F₂ x) :=
        mul_le_mul_of_nonneg_left hmix (inv_nonneg.mpr hR₁.le)
      _ = k * (R₂ / R₁) * T₂ := by dsimp [T₂]; field_simp [hR₁.ne', hR₂.ne']
      _ ≤ k * k * T₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR hk) hT₂
      _ = _ := by ring
  have iw : IntervalIntegrable (fun x => (w₁ x - w₂ x) * F₂ x) volume a b :=
    (i₁₂.sub i₂₂).congr (fun x _ => by ring)
  have idiff : IntervalIntegrable (fun x => w₁ x * (F₁ x - F₂ x)) volume a b :=
    (i₁₁.sub i₁₂).congr (fun x _ => by ring)
  have hW : |∫ x in a..b, (w₁ x - w₂ x) * F₂ x| ≤
      (G / c) * ∫ x in a..b, w₁ x * F₂ x := by
    calc
      _ = ‖∫ x in a..b, (w₁ x - w₂ x) * F₂ x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x in a..b, ‖(w₁ x - w₂ x) * F₂ x‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ x in a..b, (G / c) * (w₁ x * F₂ x) := by
        apply intervalIntegral.integral_mono_on hab iw.norm (i₁₂.const_mul _)
        intro x hx
        change ‖(w₁ x - w₂ x) * F₂ x‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hF₂ x hx)]
        have hw : |w₁ x - w₂ x| ≤ (G / c) * w₁ x := by
          calc
            _ ≤ G := hδw x hx
            _ = (G / c) * c := by field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left (hw₁ x hx) (div_nonneg hG hc.le)
        exact (mul_le_mul_of_nonneg_right hw (hF₂ x hx)).trans_eq (by ring)
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hW' : |R₁⁻¹ * ∫ x in a..b, (w₁ x - w₂ x) * F₂ x| ≤
      (G / c) * (k ^ 2 * T₂) := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hR₁)]
    calc
      _ ≤ R₁⁻¹ * ((G / c) * ∫ x in a..b, w₁ x * F₂ x) :=
        mul_le_mul_of_nonneg_left hW (inv_nonneg.mpr hR₁.le)
      _ = (G / c) * T₁₂ := by dsimp [T₁₂]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hT₁₂ (div_nonneg hG hc.le)
  have hR' : |((R₂ - R₁) / R₁) * T₂| ≤ G * T₂ := by
    rw [abs_mul, abs_of_nonneg hT₂, abs_div, abs_of_pos hR₁, abs_sub_comm]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hR₁).mpr hδR) hT₂
  have hfirst : |R₁⁻¹ * ∫ x in a..b, w₁ x * (F₁ x - F₂ x)| ≤
      R₁⁻¹ * ∫ x in a..b, w₁ x * |F₁ x - F₂ x| := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hR₁)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR₁.le)
    calc
      _ = ‖∫ x in a..b, w₁ x * (F₁ x - F₂ x)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x in a..b, ‖w₁ x * (F₁ x - F₂ x)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        change ‖w₁ x * (F₁ x - F₂ x)‖ = w₁ x * |F₁ x - F₂ x|
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw₁0 x hx)]
  have heq : R₁⁻¹ * (∫ x in a..b, w₁ x * F₁ x) - T₂ =
      (R₁⁻¹ * (∫ x in a..b, w₁ x * (F₁ x - F₂ x)) +
        R₁⁻¹ * (∫ x in a..b, (w₁ x - w₂ x) * F₂ x)) + ((R₂ - R₁) / R₁) * T₂ := by
    simp_rw [mul_sub, sub_mul]
    rw [intervalIntegral.integral_sub i₁₁ i₁₂, intervalIntegral.integral_sub i₁₂ i₂₂]
    dsimp [T₂]
    field_simp [hR₁.ne', hR₂.ne']
    ring
  rw [heq]
  apply ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
  apply (add_le_add (add_le_add hfirst hW') hR').trans_eq
  ring

private theorem mass_ratio_self_bound (C : ℝ) (hC : 0 ≤ C)
    {s t e M ε : ℝ} {S : Fields} (hS : IsSolution e S (triangle s t))
    (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hbox : ∀ p ∈ triangle s t, S.lam p.1 p.2 ≤ C ∧
      ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε)
    {u v : ℝ} (hp : (u, v) ∈ triangle s t) :
    S.mu u v ≤ ε ^ 2 + 4 * C ^ 2 *
      (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε ^ 2 := by
  rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
  · subst v
    simp only [Fields.mu, (hS.axis u hp).1, div_zero]
    positivity
  · have hs : outSeg u u v ⊆ triangle s t := by
      rintro p ⟨rfl, hx⟩
      exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
    have hr := hS.r_pos (u, v) hp huv
    have cl := continuousOn_out_section hS.cont_lam hs
    have cr := continuousOn_out_section hS.cont_r hs
    have ilam : IntervalIntegrable (S.lam u) volume u v :=
      ContinuousOn.intervalIntegrable_of_Icc huv.le cl
    have ilamr : IntervalIntegrable (fun x => S.lam u x * S.r u x ^ 2) volume u v :=
      ContinuousOn.intervalIntegrable_of_Icc huv.le (cl.mul (cr.pow 2))
    have hq (x : ℝ) (hx : x ∈ Icc u v) :
        S.Q u x ^ 2 / S.r u x ^ 2 ≤ e ^ 2 * M ^ 2 * ε ^ 2 * S.r u x ^ 2 := by
      by_cases hrx : S.r u x = 0
      · simp [hrx]
      · have hsx : outSeg u u x ⊆ triangle s t := by
          rintro p ⟨rfl, hy⟩
          exact hs ⟨rfl, hy.1, hy.2.trans hx.2⟩
        have hQ := charge_bound hS hx.1 hsx
          (fun y hy => (hbox (u, y) (hsx ⟨rfl, hy⟩)).2.1)
          (fun y hy => (hbox (u, y) (hsx ⟨rfl, hy⟩)).2.2)
        have hQ' : |S.Q u x| ≤ |e| * M * ε * S.r u x ^ 2 := by
          have h0 : 0 ≤ |e| * M * ε * S.r u x ^ 2 := by positivity
          exact hQ.trans (by linarith)
        have hsq := (sq_le_sq₀ (abs_nonneg (S.Q u x)) (by positivity)).mpr hQ'
        simp only [sq_abs, mul_pow] at hsq
        apply (div_le_iff₀ (sq_pos_of_ne_zero hrx)).mpr
        exact hsq.trans_eq (by ring)
    have hdensity x (hx : x ∈ Icc u v) :
        (1 - S.mu u x) * ‖S.theta u x / S.lam u x‖ ^ 2 + S.Q u x ^ 2 / S.r u x ^ 2 ≤
          ε ^ 2 + (e ^ 2 * M ^ 2 * ε ^ 2) * S.r u x ^ 2 := by
      have hμ := mu_mem_Ico hS (hs ⟨rfl, hx⟩)
      apply add_le_add _ (by simpa only [mul_assoc] using hq x hx)
      calc
        _ ≤ 1 * ε ^ 2 := mul_le_mul (by linarith [hμ.1])
          ((sq_le_sq₀ (norm_nonneg _) hε).mpr (hbox (u, x) (hs ⟨rfl, hx⟩)).2.2)
          (sq_nonneg _) zero_le_one
        _ = _ := one_mul _
    have imaj : IntervalIntegrable (fun x => S.lam u x *
        (ε ^ 2 + (e ^ 2 * M ^ 2 * ε ^ 2) * S.r u x ^ 2)) volume u v :=
      ContinuousOn.intervalIntegrable_of_Icc huv.le
        (cl.mul (continuousOn_const.add (continuousOn_const.mul (cr.pow 2))))
    have hi := intervalIntegral.integral_mono_on huv.le
      (outgoing_mass_density_integrable hS huv.le hs) imaj
      (fun x hx => mul_le_mul_of_nonneg_left (hdensity x hx)
        (hS.lam_pos (u, x) (hs ⟨rfl, hx⟩)).le)
    have hm2 := outgoing_radius_moment hS huv.le hs 2
    norm_num at hm2
    have hself : S.mu u v ≤ ε ^ 2 + (e ^ 2 * M ^ 2 * ε ^ 2) * S.r u v ^ 2 / 3 := by
      rw [outgoing_mass_ratio_reconstruction hS huv.le hs]
      apply (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hr.le)).trans_eq
      have hpoly : (fun x => S.lam u x * (ε ^ 2 + (e ^ 2 * M ^ 2 * ε ^ 2) * S.r u x ^ 2)) =
          fun x => ε ^ 2 * S.lam u x + (e ^ 2 * M ^ 2 * ε ^ 2) * (S.lam u x * S.r u x ^ 2) :=
        funext fun x => by ring
      rw [hpoly, intervalIntegral.integral_add (ilam.const_mul _) (ilamr.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        outgoing_radius_reconstruction hS huv.le hs, hm2]
      field_simp [hr.ne']
    have hst : 0 ≤ t - s := by linarith [hp.1, hp.2.1, hp.2.2]
    have hR := (outgoing_radius_upper hS huv.le hs
      (fun x hx => (hbox (u, x) (hs ⟨rfl, hx⟩)).1)).trans
        (mul_le_mul_of_nonneg_left (show v - u ≤ t - s by linarith [hp.1, hp.2.2]) hC)
    calc
      _ ≤ ε ^ 2 + (e ^ 2 * M ^ 2 * ε ^ 2) * S.r u v ^ 2 / 3 := hself
      _ ≤ ε ^ 2 + (e ^ 2 * M ^ 2 * ε ^ 2) * (C * (t - s)) ^ 2 / 3 := by gcongr
      _ = ε ^ 2 + (4 * C ^ 2 / 3) * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε ^ 2 := by ring
      _ ≤ _ := by gcongr; have h0 := sq_nonneg C; linarith

end EmcsfAcExtension.Local.Broad

namespace EmcsfAcExtension.Local

open Broad

/-- [node restart-stab-broad-mu-sup]
Uniform broad mass-ratio comparison, charged_SF_new_version.tex:L5748–5750 and internal project
record
(MS). For a fixed box `c,C`, the positive constant is independent of the
triangle, coupling, scalar size, ratio size and competing frozen solutions.
The finite uniform mass distance is absorbed using `ε² ≤ 1/2`; no BV budget
or derivative envelope enters this estimate. -/
theorem stab_broad_mu_sup (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → ε ^ 2 ≤ 1 / 2 →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
          ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      (mass_ratio_distance s t S₁ S₂).toReal ≤
        K * ε * (normalized_field_distance s t S₁ S₂).toReal +
        K * ε ^ 2 * (geometry_distance s t S₁ S₂).toReal +
        K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε *
          ((normalized_field_distance s t S₁ S₂).toReal +
            ε * (geometry_distance s t S₁ S₂).toReal) := by
  obtain ⟨A, hA, hscalar⟩ := scalar_average_difference_bound c hc
  obtain ⟨Ke, hKe, helectric⟩ := charged_mass_average_difference c C hc hC
  let k := C / c
  let KT := k ^ 2 / c + 1
  let a := 2 * (1 + A) + KT
  let b := Ke + 4 * C ^ 2 * KT
  let K := 2 * (a + b) + 1
  have hk : 0 ≤ k := div_nonneg hC hc.le
  have hKT : 0 ≤ KT := by dsimp [KT]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hbox hosc
  have hmem₁ : S₁ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hmem₂ : S₂ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM
  let d := (normalized_field_distance s t S₁ S₂).toReal
  let g := (geometry_distance s t S₁ S₂).toReal
  let X := (mass_ratio_distance s t S₁ S₂).toReal
  let E := d + ε * g
  let σ := e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2
  let H := (1 + A) * E
  let A₀ := 2 * ε * H + ε ^ 2 * X
  let N := a * ε * E + ε ^ 2 * X + b * σ * ε * E
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hg : 0 ≤ g := ENNReal.toReal_nonneg
  have hX : 0 ≤ X := ENNReal.toReal_nonneg
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hfin := geometry_distance_ne_top hS₁ hS₂ hc
    (fun p hp => (hbox S₁ hmem₁ p hp).1)
  have hδφ p (hp : p ∈ triangle s t) :
      ‖S₁.phi p.1 p.2 - S₂.phi p.1 p.2‖ ≤ A * E :=
    hscalar s t e ε S₁ S₂ hS₁ hS₂ hε
      (fun p hp => (hbox S₁ hmem₁ p hp).1) hosc p.1 p.2 hp
  have hpoint (u v : ℝ) (hp : (u, v) ∈ triangle s t) : |S₁.mu u v - S₂.mu u v| ≤ N := by
    rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
    · subst v
      simpa [Fields.mu, (hS₁.axis u hp).1, (hS₂.axis u hp).1] using hN
    · have hs : outSeg u u v ⊆ triangle s t := by
        rintro p ⟨rfl, hx⟩
        exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
      have hr₁ := hS₁.r_pos (u, v) hp huv
      have hr₂ := hS₂.r_pos (u, v) hp huv
      let f₁ := fun x => S₁.theta u x / (S₁.lam u x : ℂ)
      let f₂ := fun x => S₂.theta u x / (S₂.lam u x : ℂ)
      let q₁ := fun x => S₁.Q u x ^ 2 / S₁.r u x ^ 2
      let q₂ := fun x => S₂.Q u x ^ 2 / S₂.r u x ^ 2
      let F₁ := fun x => (1 - S₁.mu u x) * ‖f₁ x‖ ^ 2 + q₁ x
      let F₂ := fun x => (1 - S₂.mu u x) * ‖f₂ x‖ ^ 2 + q₂ x
      have cl₁ := continuousOn_out_section hS₁.cont_lam hs
      have cl₂ := continuousOn_out_section hS₂.cont_lam hs
      have ilam : IntervalIntegrable (S₁.lam u) volume u v :=
        ContinuousOn.intervalIntegrable_of_Icc huv.le cl₁
      have cRatio : ContinuousOn (fun x => S₁.lam u x / S₂.lam u x) (uIcc u v) := by
        rw [uIcc_of_le huv.le]
        exact cl₁.div cl₂ (fun x hx => (hS₂.lam_pos (u, x) (hs ⟨rfl, hx⟩)).ne')
      have i₁₁ : IntervalIntegrable (fun x => S₁.lam u x * F₁ x) volume u v :=
        outgoing_mass_density_integrable hS₁ huv.le hs
      have i₂₂ : IntervalIntegrable (fun x => S₂.lam u x * F₂ x) volume u v :=
        outgoing_mass_density_integrable hS₂ huv.le hs
      have i₁₂ : IntervalIntegrable (fun x => S₁.lam u x * F₂ x) volume u v := by
        apply (i₂₂.mul_continuousOn cRatio).congr
        intro x hx
        have hx' : x ∈ Icc u v := by simpa only [uIcc_of_le huv.le] using uIoc_subset_uIcc hx
        have hlam := (hS₂.lam_pos (u, x) (hs ⟨rfl, hx'⟩)).ne'
        field_simp [hlam]
      have cf {S : Fields} (hS : IsSolution e S (triangle s t)) :
          ContinuousOn (fun x => S.theta u x / (S.lam u x : ℂ)) (Icc u v) :=
        (continuousOn_out_section hS.cont_theta hs).div
          (continuous_ofReal.comp_continuousOn (continuousOn_out_section hS.cont_lam hs))
          (fun x hx => by exact_mod_cast (hS.lam_pos (u, x) (hs ⟨rfl, hx⟩)).ne')
      have cs₁ : ContinuousOn (fun x => S₁.lam u x * ((1 - S₁.mu u x) * ‖f₁ x‖ ^ 2))
          (Icc u v) := cl₁.mul ((continuousOn_const.sub (continuousOn_mu_out hS₁ huv hs)).mul
            ((cf hS₁).norm.pow 2))
      have cs₂ : ContinuousOn (fun x => S₁.lam u x * ((1 - S₂.mu u x) * ‖f₂ x‖ ^ 2))
          (Icc u v) := cl₁.mul ((continuousOn_const.sub (continuousOn_mu_out hS₂ huv hs)).mul
            ((cf hS₂).norm.pow 2))
      have iq₁ : IntervalIntegrable (fun x => S₁.lam u x * q₁ x) volume u v :=
        (i₁₁.sub (ContinuousOn.intervalIntegrable_of_Icc huv.le cs₁)).congr
          (fun x _ => by dsimp [F₁]; ring)
      have iq₂ : IntervalIntegrable (fun x => S₁.lam u x * q₂ x) volume u v :=
        (i₁₂.sub (ContinuousOn.intervalIntegrable_of_Icc huv.le cs₂)).congr
          (fun x _ => by dsimp [F₂]; ring)
      have iQ : IntervalIntegrable (fun x => S₁.lam u x * |q₁ x - q₂ x|) volume u v := by
        apply (iq₁.sub iq₂).norm.congr
        intro x hx
        have hx' : x ∈ Icc u v := by simpa only [uIcc_of_le huv.le] using uIoc_subset_uIcc hx
        change ‖S₁.lam u x * q₁ x - S₁.lam u x * q₂ x‖ = _
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul,
          abs_of_pos (hS₁.lam_pos (u, x) (hs ⟨rfl, hx'⟩))]
      have iD : IntervalIntegrable (fun x => S₁.lam u x * |F₁ x - F₂ x|) volume u v := by
        have hi : IntervalIntegrable (fun x => S₁.lam u x * (F₁ x - F₂ x)) volume u v :=
          (i₁₁.sub i₁₂).congr (fun x _ => by ring)
        apply hi.norm.congr
        intro x hx
        have hx' : x ∈ Icc u v := by simpa only [uIcc_of_le huv.le] using uIoc_subset_uIcc hx
        change ‖S₁.lam u x * (F₁ x - F₂ x)‖ = _
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hS₁.lam_pos (u, x) (hs ⟨rfl, hx'⟩))]
      have hDiff x (hx : x ∈ Icc u v) : |F₁ x - F₂ x| ≤ A₀ + |q₁ x - q₂ x| := by
        have hpx : (u, x) ∈ triangle s t := hs ⟨rfl, hx⟩
        have hμ := mu_mem_Ico hS₁ hpx
        have hδf : ‖f₁ x - f₂ x‖ ≤ H := by
          apply ((norm_ratio_sub_le_distance_add_scalar hS₁ hS₂ hpx).1).trans
          have hdE : d ≤ E := le_add_of_nonneg_right (mul_nonneg hε hg)
          have hφ := hδφ (u, x) hpx
          dsimp only [H]
          linarith
        have hscalarDiff := Broad.scalar_mass_difference_of_bounds hμ.1 hμ.2.le hε hH hX
          (hbox S₁ hmem₁ (u, x) hpx).2.2.2 (hbox S₂ hmem₂ (u, x) hpx).2.2.2 hδf
          (abs_mu_sub_le_mass_ratio_distance hS₁ hS₂ hpx)
        have heq : F₁ x - F₂ x =
            ((1 - S₁.mu u x) * ‖f₁ x‖ ^ 2 - (1 - S₂.mu u x) * ‖f₂ x‖ ^ 2) + (q₁ x - q₂ x) := by
          dsimp [F₁, F₂]
          ring
        rw [heq]
        exact (abs_add_le _ _).trans (add_le_add hscalarDiff le_rfl)
      have imaj : IntervalIntegrable (fun x => S₁.lam u x * (A₀ + |q₁ x - q₂ x|)) volume u v :=
        ((ilam.const_mul A₀).add iQ).congr (fun x _ => by ring)
      have hUineq := intervalIntegral.integral_mono_on huv.le iD imaj
        (fun x hx => mul_le_mul_of_nonneg_left (hDiff x hx)
          (hS₁.lam_pos (u, x) (hs ⟨rfl, hx⟩)).le)
      have hU : (S₁.r u v)⁻¹ * (∫ x in u..v, S₁.lam u x * |F₁ x - F₂ x|) ≤
          A₀ + Ke * σ * ε * E := by
        have hElectric := helectric s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hbox hosc u v hp
        have hQavg : (S₁.r u v)⁻¹ * (∫ x in u..v, S₁.lam u x * |q₁ x - q₂ x|) ≤
            Ke * σ * ε * E := hElectric.2.1
        calc
          _ ≤ (S₁.r u v)⁻¹ * ∫ x in u..v, S₁.lam u x * (A₀ + |q₁ x - q₂ x|) :=
            mul_le_mul_of_nonneg_left hUineq (inv_nonneg.mpr hr₁.le)
          _ = A₀ + (S₁.r u v)⁻¹ * ∫ x in u..v, S₁.lam u x * |q₁ x - q₂ x| := by
            simp_rw [mul_add]
            rw [intervalIntegral.integral_add (ilam.mul_const A₀) iQ,
              intervalIntegral.integral_mul_const, outgoing_radius_reconstruction hS₁ huv.le hs]
            field_simp [hr₁.ne']
          _ ≤ _ := add_le_add le_rfl hQavg
      have hwratio x (hx : x ∈ Icc u v) : S₁.lam u x ≤ k * S₂.lam u x := by
        calc
          _ ≤ C := (hbox S₁ hmem₁ (u, x) (hs ⟨rfl, hx⟩)).2.1
          _ = k * c := by dsimp [k]; field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left (hbox S₂ hmem₂ (u, x) (hs ⟨rfl, hx⟩)).1 hk
      have hRratio : S₂.r u v ≤ k * S₁.r u v := by
        have hlo := outgoing_radius_lower hS₁ huv.le hs
          (fun x hx => (hbox S₁ hmem₁ (u, x) (hs ⟨rfl, hx⟩)).1)
        calc
          _ ≤ C * (v - u) := outgoing_radius_upper hS₂ huv.le hs
            (fun x hx => (hbox S₂ hmem₂ (u, x) (hs ⟨rfl, hx⟩)).2.1)
          _ = k * (c * (v - u)) := by dsimp [k]; field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hlo hk
      have hCore := Broad.average_difference_le_of_bounds huv.le hr₁ hr₂ hc hk hg
        (fun x hx => (hbox S₁ hmem₁ (u, x) (hs ⟨rfl, hx⟩)).1)
        (fun x hx => (hS₂.lam_pos (u, x) (hs ⟨rfl, hx⟩)).le)
        (fun x hx => add_nonneg (mul_nonneg (hS₂.one_sub_mu_pos (u, x) (hs ⟨rfl, hx⟩)).le
          (sq_nonneg _)) (div_nonneg (sq_nonneg _) (sq_nonneg _))) hwratio
        (fun x hx => abs_lam_sub_le_geometry_distance hS₁ hfin (hs ⟨rfl, hx⟩)) hRratio
        (abs_radius_sub_le_geometry_distance_mul_radius hS₁ hS₂ hfin hp) i₁₁ i₁₂ i₂₂
      have hμ₁ : S₁.mu u v = (S₁.r u v)⁻¹ * ∫ x in u..v, S₁.lam u x * F₁ x :=
        outgoing_mass_ratio_reconstruction hS₁ huv.le hs
      have hμ₂ : S₂.mu u v = (S₂.r u v)⁻¹ * ∫ x in u..v, S₂.lam u x * F₂ x :=
        outgoing_mass_ratio_reconstruction hS₂ huv.le hs
      rw [← hμ₁, ← hμ₂] at hCore
      have hself := Broad.mass_ratio_self_bound C hC hS₂ hM0 hε
        (fun p hp => ⟨(hbox S₂ hmem₂ p hp).2.1, (hbox S₂ hmem₂ p hp).2.2.1,
          (hbox S₂ hmem₂ p hp).2.2.2⟩) hp
      have hweight : KT * g * (ε ^ 2 + 4 * C ^ 2 * σ * ε ^ 2) ≤
          KT * ε * E + 4 * C ^ 2 * KT * σ * ε * E := by
        calc
          _ = (KT * ε * (1 + 4 * C ^ 2 * σ)) * (ε * g) := by ring
          _ ≤ (KT * ε * (1 + 4 * C ^ 2 * σ)) * E :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hd) (by positivity)
          _ = _ := by ring
      calc
        _ ≤ (A₀ + Ke * σ * ε * E) + KT * g * (ε ^ 2 + 4 * C ^ 2 * σ * ε ^ 2) :=
          hCore.trans (add_le_add hU (mul_le_mul_of_nonneg_left hself (mul_nonneg hKT hg)))
        _ ≤ (A₀ + Ke * σ * ε * E) + (KT * ε * E + 4 * C ^ 2 * KT * σ * ε * E) :=
          add_le_add le_rfl hweight
        _ = N := by dsimp [N, a, b, A₀, H]; ring
  have hENN : mass_ratio_distance s t S₁ S₂ ≤ ENNReal.ofReal N := by
    apply iSup₂_le
    rintro ⟨u, v⟩ hp
    exact ENNReal.ofReal_le_ofReal (hpoint u v hp)
  have hXineq := ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN
  rw [ENNReal.toReal_ofReal hN] at hXineq
  change X ≤ N at hXineq
  have hfeedback : ε ^ 2 * X ≤ (1 / 2) * X := mul_le_mul_of_nonneg_right hsmall hX
  have habsorbed : X ≤ 2 * a * ε * E + 2 * b * σ * ε * E := by
    dsimp only [N] at hXineq
    linarith only [hXineq, hfeedback]
  calc
    _ ≤ 2 * a * ε * E + 2 * b * σ * ε * E := habsorbed
    _ ≤ K * ε * E + K * σ * ε * E := by
      have hKa : 2 * a ≤ K := by dsimp [K]; linarith
      have hKb : 2 * b ≤ K := by dsimp [K]; linarith
      gcongr
    _ = _ := by dsimp [E, d, g]; ring

end EmcsfAcExtension.Local
