module

public import EmcsfAcExtension.Local.Construction.ReconBasic
public import EmcsfAcExtension.Frozen.Fields.RadiusUV
public import EmcsfAcExtension.Frozen.Fields.MassV
public import EmcsfAcExtension.Frozen.Fields.ChargeV
public import EmcsfAcExtension.Frozen.Fields.PotentialV
public import EmcsfAcExtension.Frozen.Fields.PhiV
public import EmcsfAcExtension.Frozen.IntegralForm

/-! # Uniform orders at the center

The bounded `C¹ᵥ` candidate estimates of `charged_SF_new_version.tex:L5997–L6014` and approved
internal project record, with constants chosen before the candidate. Center orders require no
Hawking gap.
-/

public section

open MeasureTheory Set Filter Topology Complex


namespace EmcsfAcExtension.Local.Null

/-- [node restart-sec-independent-null-construction#center-orders]
Uniform linear scalar oscillation and cubic charge and mass orders. The positive constant
depends only on `l,U,H,D,L,|e|`, and is chosen before the candidate, vertex and section.
No smallness assumption and no lower bound on `1-μ` is used. The derivative is taken within
the closed section, as in the approved blueprint's `C⁰ᵤC¹ᵥ` candidate class. -/
theorem center_orders {l U H D L e : ℝ} (hl : 0 < l) (hlU : l ≤ U)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    ∃ C > 0, ∀ (lam : ℝ → ℝ → ℝ) (hh : ℝ → ℝ → ℂ) (h' : ℝ → ℂ) (u b : ℝ),
      u ≤ b → b - u ≤ L → ContinuousOn (lam u) (Icc u b) →
      (∀ s ∈ Icc u b, l ≤ lam u s ∧ lam u s ≤ U) →
      (∀ s ∈ Icc u b, HasDerivWithinAt (hh u) (h' s) (Icc u b) s) →
      (∀ s ∈ Icc u b, ‖hh u s‖ ≤ H ∧ ‖h' s‖ ≤ D) →
      ∀ v ∈ Icc u b, ‖Recon.ratio lam hh u v‖ ≤ D * (v - u) ∧
        |Recon.Q e lam hh u v| ≤ C * (v - u) ^ 3 ∧
        0 ≤ Recon.m e lam hh u v ∧ Recon.m e lam hh u v ≤ C * (v - u) ^ 3 := by
  have hU : 0 ≤ U := hl.le.trans hlU
  let K := |e| * H * U ^ 2 * D
  let B := U * (D ^ 2 + (K / l) ^ 2 * L ^ 2) / 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨1 + K + B, by positivity, ?_⟩
  intro lam hh h' u b hub hbL hlam hlamB hder hbound
  have hhc : ContinuousOn (hh u) (Icc u b) := fun s hs => (hder s hs).continuousWithinAt
  have hsub (v) (hv : v ∈ Icc u b) : Icc u v ⊆ Icc u b := Icc_subset_Icc le_rfl hv.2
  have hr (v) (hv : v ∈ Icc u b) := Recon.r_bounds hv.1 (hlam.mono (hsub v hv))
    (fun s hs => (hlamB s (hsub v hv hs)).1) (fun s hs => (hlamB s (hsub v hv hs)).2)
  have hf (v) (hv : v ∈ Icc u b) : ‖Recon.ratio lam hh u v‖ ≤ D * (v - u) := by
    apply Recon.norm_ratio_le_of_lipschitz hl hD hv.1 (hlam.mono (hsub v hv))
      (hhc.mono (hsub v hv)) (fun s hs => (hlamB s (hsub v hv hs)).1)
    intro s hs
    simpa [abs_of_nonneg (sub_nonneg.mpr hs.2)] using
      Recon.norm_sub_le_of_hasDerivWithinAt hder (fun t ht => (hbound t ht).2)
        (hsub v hv hs) hv
  have hp (v) (hv : v ∈ Icc u b) : ‖Recon.phi lam hh u v‖ ≤ H :=
    Recon.norm_phi_le hl hv.1 (hlam.mono (hsub v hv)) (hhc.mono (hsub v hv))
      (fun s hs => (hlamB s (hsub v hv hs)).1) (fun s hs => (hbound s (hsub v hv hs)).1)
  have hq (v) (hv : v ∈ Icc u b) : |Recon.Q e lam hh u v| ≤ K * (v - u) ^ 3 := by
    apply Recon.abs_Q_le_of_bounds hU hH hD hv.1
    · intro s hs
      have hr' := hr s (hsub v hv hs)
      exact ⟨(mul_nonneg hl.le (sub_nonneg.mpr hs.1)).trans hr'.1, hr'.2⟩
    · intro s hs
      exact ⟨hl.le.trans (hlamB s (hsub v hv hs)).1, (hlamB s (hsub v hv hs)).2⟩
    · exact fun s hs => hp s (hsub v hv hs)
    · exact fun s hs => hf s (hsub v hv hs)
  intro v hv
  have hm := Recon.mass_bounds_of_bounds hl hU hD hK hL hv.1
    ((sub_le_sub_right hv.2 u).trans hbL)
    (fun s hs => (hr s (hsub v hv hs)).1)
    (fun s hs => ⟨hl.le.trans (hlamB s (hsub v hv hs)).1,
      (hlamB s (hsub v hv hs)).2⟩)
    (fun s hs => hf s (hsub v hv hs)) (fun s hs => hq s (hsub v hv hs))
  refine ⟨hf v hv, (hq v hv).trans ?_, hm.1, hm.2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (sub_nonneg.mpr hv.1) 3)
  · change B * (v - u) ^ 3 ≤ _
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (sub_nonneg.mpr hv.1) 3)

open Recon

/-- [node restart-sec-independent-null-construction#coefficient-center-regularity]
The radial and transport coefficients extend continuously to the center and have their
uniform linear and quadratic orders. The constant depends only on `l,U,H,D,L,|e|,κ`,
and is chosen before the candidate and section. The gap is precisely binding note S1.
The last expression is the ordinary scalar transport source, including its connection term. -/
theorem coefficient_center_regularity {l U H D L e κ : ℝ} (hl : 0 < l) (hlU : l ≤ U)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hL : 0 ≤ L) (hκ : 0 < κ) :
    ∃ C > 0, ∀ (lam : ℝ → ℝ → ℝ) (hh : ℝ → ℝ → ℂ) (h' : ℝ → ℂ) (u b : ℝ),
      u ≤ b → b - u ≤ L → ContinuousOn (lam u) (Icc u b) →
      (∀ s ∈ Icc u b, l ≤ lam u s ∧ lam u s ≤ U) →
      (∀ s ∈ Icc u b, HasDerivWithinAt (hh u) (h' s) (Icc u b) s) →
      (∀ s ∈ Icc u b, ‖hh u s‖ ≤ H ∧ ‖h' s‖ ≤ D) →
      (∀ s ∈ Icc u b, κ ≤ 1 - mu e lam hh u s) →
      ContinuousOn (phi lam hh u) (Icc u b) ∧ ContinuousOn (Q e lam hh u) (Icc u b) ∧
      ContinuousOn (m e lam hh u) (Icc u b) ∧ ContinuousOn (mu e lam hh u) (Icc u b) ∧
      ContinuousOn (fun s => lam u s * ‖ratio lam hh u s‖ ^ 2 / r lam u s) (Icc u b) ∧
      ContinuousOn (fun s => lam u s * (‖ratio lam hh u s‖ ^ 2 +
        Q e lam hh u s ^ 2 / r lam u s ^ 2)) (Icc u b) ∧
      ContinuousOn (fun s => lam u s / r lam u s * z e lam hh u s) (Icc u b) ∧
      ContinuousOn (nu e lam hh u) (Icc u b) ∧
      ContinuousOn (fun s => 2 * nu e lam hh u s * lam u s * Q e lam hh u s /
        ((1 - mu e lam hh u s) * r lam u s ^ 2)) (Icc u b) ∧
      ContinuousOn (A e lam hh u) (Icc u b) ∧
      ContinuousOn (fun v => nu e lam hh u v / r lam u v * z e lam hh u v) (Icc u b) ∧
      ContinuousOn (fun v => -(I * e * A e lam hh u v) * hh u v +
        ((-nu e lam hh u v / r lam u v : ℝ) : ℂ) * ((z e lam hh u v : ℂ) * ratio lam hh u v +
          I * e * Q e lam hh u v * phi lam hh u v / (1 - (mu e lam hh u v : ℂ)))) (Icc u b) ∧
      ∀ v ∈ Icc u b,
        |lam u v / r lam u v * z e lam hh u v| ≤ C * (v - u) ∧
        |2 * nu e lam hh u v * lam u v * Q e lam hh u v /
          ((1 - mu e lam hh u v) * r lam u v ^ 2)| ≤ C * (v - u) ∧
        |nu e lam hh u v / r lam u v * z e lam hh u v| ≤ C * (v - u) ∧
        ‖-(I * e * A e lam hh u v) * hh u v + ((-nu e lam hh u v / r lam u v : ℝ) : ℂ) *
          ((z e lam hh u v : ℂ) * ratio lam hh u v +
            I * e * Q e lam hh u v * phi lam hh u v / (1 - (mu e lam hh u v : ℂ)))‖ ≤
          C * (v - u) ^ 2 := by
  obtain ⟨K, hK, hcenter⟩ := center_orders (e := e) hl hlU hH hD hL
  have hU : 0 ≤ U := hl.le.trans hlU
  let Z := (2 * K / l + (K / l) ^ 2 * L ^ 2) / κ
  let B := U * Z / l
  let N := U * Real.exp (B * L ^ 2)
  let P := 2 * N * U * K / l ^ 2 / κ
  let G := N * Z / l
  let F := |e| * P * H + N / l * (Z * D + |e| * K * H / κ)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨1 + B + P + G + F, by positivity, ?_⟩
  intro lam hh h' u b hub hbL hlam hlamB hder hbound hgap
  have hc := hcenter lam hh h' u b hub hbL hlam hlamB hder hbound
  have hhc : ContinuousOn (hh u) (Icc u b) := fun s hs => (hder s hs).continuousWithinAt
  have cr : ContinuousOn (r lam u) (Icc u b) :=
    continuousOn_primitive hub (hlam.intervalIntegrable_of_Icc hub)
  have hr (v) (hv : v ∈ Icc u b) := r_bounds hv.1
    (hlam.mono (Icc_subset_Icc le_rfl hv.2))
    (fun s hs => (hlamB s ⟨hs.1, hs.2.trans hv.2⟩).1)
    (fun s hs => (hlamB s ⟨hs.1, hs.2.trans hv.2⟩).2)
  have hrp (v) (hv : v ∈ Icc u b) (hux : u < v) : 0 < r lam u v :=
    (mul_pos hl (sub_pos.mpr hux)).trans_le (hr v hv).1
  have cp := continuousOn_phi_of_lipschitz hl hD hub hlam hhc
    (fun s hs => (hlamB s hs).1)
    (fun s hs t ht => norm_sub_le_of_hasDerivWithinAt hder (fun x hx => (hbound x hx).2) hs ht)
  have cf : ContinuousOn (ratio lam hh u) (Icc u b) := hhc.sub cp
  have cQ : ContinuousOn (Q e lam hh u) (Icc u b) := fun v hv =>
    (hasDerivWithinAt_Q_of_continuous hlam hhc cp hv).continuousWithinAt
  have hq (v) (hv : v ∈ Icc u b) : Q e lam hh u v ^ 2 / r lam u v ^ 2 ≤
      (K / l) ^ 2 * (v - u) ^ 4 := by
    rcases hv.1.eq_or_lt with rfl | hux
    · simp
    · exact charge_sq_div_r_sq_le_of_bounds hl hK.le hux (hr v hv).1 (hc v hv).2.1
  have cq : ContinuousOn (fun v => Q e lam hh u v ^ 2 / r lam u v ^ 2) (Icc u b) := by
    apply continuousOn_of_axis_bound (by simp) (g := fun v => (K / l) ^ 2 * (v - u) ^ 4)
      (by fun_prop) (by ring)
    · intro v hv
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact hq v hv
    · intro v hv hux
      exact ((cQ v hv).pow 2).div ((cr v hv).pow 2) (pow_ne_zero 2 (hrp v hv hux).ne')
  have ha (v) (hv : v ∈ Icc u b) :
      |lam u v * ‖ratio lam hh u v‖ ^ 2 / r lam u v| ≤ (U * D ^ 2 / l) * (v - u) := by
    rcases hv.1.eq_or_lt with rfl | hux
    · simp
    · have hlv := (hlamB v hv).2
      have hfv := (hc v hv).1
      have hnum : |lam u v * ‖ratio lam hh u v‖ ^ 2| ≤
          (U * D ^ 2) * (v - u) ^ (1 + 1) := by
        rw [abs_of_nonneg (mul_nonneg (hl.le.trans (hlamB v hv).1) (sq_nonneg _))]
        calc
          _ ≤ U * (D * (v - u)) ^ 2 := by gcongr
          _ = _ := by ring
      simpa only [pow_one] using abs_div_pow_le_of_order (n := 1) (j := 1)
        hl (sub_pos.mpr hux) (by positivity) (hr v hv).1 hnum
  have ca : ContinuousOn (fun v => lam u v * ‖ratio lam hh u v‖ ^ 2 / r lam u v)
      (Icc u b) := by
    apply continuousOn_of_axis_bound (by simp) (g := fun v => (U * D ^ 2 / l) * (v - u))
      (by fun_prop) (by ring) (fun v hv => by simpa only [Real.norm_eq_abs] using ha v hv)
    intro v hv hux
    exact ((hlam v hv).mul ((cf v hv).norm.pow 2)).div (cr v hv) (hrp v hv hux).ne'
  have cb : ContinuousOn (fun v => lam u v * (‖ratio lam hh u v‖ ^ 2 +
      Q e lam hh u v ^ 2 / r lam u v ^ 2)) (Icc u b) := hlam.mul (cf.norm.pow 2 |>.add cq)
  have cm : ContinuousOn (m e lam hh u) (Icc u b) := fun v hv =>
    (hasDerivWithinAt_m_of_continuous ca cb hv).continuousWithinAt
  have hm (v) (hv : v ∈ Icc u b) : |mu e lam hh u v| ≤ (2 * K / l) * (v - u) ^ 2 := by
    rcases hv.1.eq_or_lt with rfl | hux
    · simp
    · exact abs_mu_le_of_bounds hl hK.le hux (hr v hv).1 (hc v hv).2.2.1 (hc v hv).2.2.2
  have cμ : ContinuousOn (mu e lam hh u) (Icc u b) := by
    apply continuousOn_of_axis_bound (by simp) (g := fun v => (2 * K / l) * (v - u) ^ 2)
      (by fun_prop) (by ring) (fun v hv => by simpa only [Real.norm_eq_abs] using hm v hv)
    intro v hv hux
    exact ((cm v hv).const_mul 2).div (cr v hv) (hrp v hv hux).ne'
  have cz : ContinuousOn (z e lam hh u) (Icc u b) :=
    (cμ.sub cq).div (continuousOn_const.sub cμ) (fun v hv => (hκ.trans_le (hgap v hv)).ne')
  have hz (v) (hv : v ∈ Icc u b) : |z e lam hh u v| ≤ Z * (v - u) ^ 2 := by
    have hq' : |Q e lam hh u v ^ 2 / r lam u v ^ 2| ≤
        (K / l) ^ 2 * L ^ 2 * (v - u) ^ 2 := by
      rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
      calc
        _ ≤ (K / l) ^ 2 * (v - u) ^ 4 := hq v hv
        _ = (K / l) ^ 2 * (v - u) ^ 2 * (v - u) ^ 2 := by ring
        _ ≤ _ := by gcongr <;> linarith [hv.1, hv.2]
    rw [z, abs_div, abs_of_pos (hκ.trans_le (hgap v hv))]
    calc
      _ ≤ ((2 * K / l) * (v - u) ^ 2 +
          (K / l) ^ 2 * L ^ 2 * (v - u) ^ 2) / κ := by
        apply div_le_div₀ (by positivity) ((abs_sub _ _).trans (add_le_add (hm v hv) hq'))
          hκ (hgap v hv)
      _ = _ := by dsimp [Z]; ring
  have hquot (V : ℝ) (hV : 0 ≤ V) (a : ℝ) (ha : |a| ≤ V)
      (v : ℝ) (hv : v ∈ Icc u b) :
      |a / r lam u v * z e lam hh u v| ≤ (V * Z / l) * (v - u) := by
    rcases hv.1.eq_or_lt with rfl | hux
    · simp
    · have hnum : |a * z e lam hh u v| ≤ (V * Z) * (v - u) ^ (1 + 1) := by
        rw [abs_mul]
        exact (mul_le_mul ha (hz v hv) (abs_nonneg _) hV).trans_eq (by ring)
      have hb := abs_div_pow_le_of_order (n := 1) (j := 1)
        hl (sub_pos.mpr hux) (by positivity) (hr v hv).1 hnum
      simpa only [pow_one, mul_div_right_comm] using hb
  have hBB (v) (hv : v ∈ Icc u b) : |lam u v / r lam u v * z e lam hh u v| ≤ B * (v - u) :=
    hquot U hU (lam u v)
      (by rw [abs_of_pos (hl.trans_le (hlamB v hv).1)]; exact (hlamB v hv).2) v hv
  have cB : ContinuousOn (fun v => lam u v / r lam u v * z e lam hh u v) (Icc u b) := by
    apply continuousOn_of_axis_bound (by simp) (g := fun v => B * (v - u))
      (by fun_prop) (by ring) (fun v hv => by simpa only [Real.norm_eq_abs] using hBB v hv)
    intro v hv hux
    exact ((hlam v hv).div (cr v hv) (hrp v hv hux).ne').mul (cz v hv)
  have cν : ContinuousOn (nu e lam hh u) (Icc u b) := fun v hv =>
    (hasDerivWithinAt_nu_of_continuous cB hv).continuousWithinAt
  have hn (v) (hv : v ∈ Icc u b) : |nu e lam hh u v| ≤ N := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := u) (b := v) (f := fun s => lam u s / r lam u s * z e lam hh u s)
      (C := B * (v - u)) (fun s hs => by
        have hs' : s ∈ Icc u b := by
          rw [uIoc_of_le hv.1] at hs
          exact ⟨hs.1.le, hs.2.trans hv.2⟩
        have hsv : s ≤ v := by
          rw [uIoc_of_le hv.1] at hs
          exact hs.2
        exact (hBB s hs').trans (mul_le_mul_of_nonneg_left (by linarith) hB))
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hv.1)] at hb
    rw [nu, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul (by rw [abs_of_pos (hl.trans_le (hlamB u ⟨le_rfl, hub⟩).1)]
                         exact (hlamB u ⟨le_rfl, hub⟩).2)
      (Real.exp_le_exp.mpr ?_) (by positivity) hU
    calc
      _ ≤ |∫ s in u..v, lam u s / r lam u s * z e lam hh u s| := le_abs_self _
      _ ≤ B * (v - u) * (v - u) := hb
      _ = B * (v - u) ^ 2 := by ring
      _ ≤ B * L ^ 2 := by gcongr <;> linarith [hv.1, hv.2]
  have hCA (v) (hv : v ∈ Icc u b) :
      |2 * nu e lam hh u v * lam u v * Q e lam hh u v /
        ((1 - mu e lam hh u v) * r lam u v ^ 2)| ≤ P * (v - u) := by
    have hx : 0 ≤ v - u := sub_nonneg.mpr hv.1
    rcases hv.1.eq_or_lt with rfl | hux
    · simp
    · have hlpos := hl.trans_le (hlamB v hv).1
      have hnum : |2 * nu e lam hh u v * lam u v * Q e lam hh u v| ≤
          (2 * N * U * K) * (v - u) ^ (1 + 2) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (hl.trans_le (hlamB v hv).1)]
        calc
          _ ≤ 2 * N * U * (K * (v - u) ^ 3) := by
            gcongr <;>
              first | positivity | exact hn v hv | exact (hlamB v hv).2 | exact (hc v hv).2.1
          _ = _ := by ring
      have hdiv := abs_div_pow_le_of_order (n := 1) (j := 2)
        hl (sub_pos.mpr hux) (by positivity) (hr v hv).1 hnum
      rw [mul_comm (1 - mu e lam hh u v), ← div_div, abs_div,
        abs_of_pos (hκ.trans_le (hgap v hv))]
      calc
        _ ≤ ((2 * N * U * K / l ^ 2) * (v - u)) / κ :=
          div_le_div₀ (by positivity) (by simpa only [pow_one] using hdiv) hκ (hgap v hv)
        _ = _ := by dsimp [P]; ring
  have cCA : ContinuousOn (fun v => 2 * nu e lam hh u v * lam u v * Q e lam hh u v /
      ((1 - mu e lam hh u v) * r lam u v ^ 2)) (Icc u b) := by
    apply continuousOn_of_axis_bound (by simp) (g := fun v => P * (v - u))
      (by fun_prop) (by ring) (fun v hv => by simpa only [Real.norm_eq_abs] using hCA v hv)
    intro v hv hux
    exact ((((cν v hv).const_mul 2).mul (hlam v hv)).mul (cQ v hv)).div
      ((continuousWithinAt_const.sub (cμ v hv)).mul ((cr v hv).pow 2))
      (mul_ne_zero (hκ.trans_le (hgap v hv)).ne' (pow_ne_zero 2 (hrp v hv hux).ne'))
  have cA : ContinuousOn (A e lam hh u) (Icc u b) := fun v hv =>
    (hasDerivWithinAt_A_of_continuous cCA hv).continuousWithinAt
  have hA (v) (hv : v ∈ Icc u b) : |A e lam hh u v| ≤ P * (v - u) ^ 2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := u) (b := v) (f := fun s => 2 * nu e lam hh u s * lam u s * Q e lam hh u s /
        ((1 - mu e lam hh u s) * r lam u s ^ 2)) (C := P * (v - u)) (fun s hs => by
        rw [uIoc_of_le hv.1] at hs
        exact (hCA s ⟨hs.1.le, hs.2.trans hv.2⟩).trans
          (mul_le_mul_of_nonneg_left (by linarith [hs.1, hs.2]) hP))
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hv.1),
      A, pow_two, mul_assoc] using hb
  have hFF (v) (hv : v ∈ Icc u b) :
      ‖-(I * e * A e lam hh u v) * hh u v + ((-nu e lam hh u v / r lam u v : ℝ) : ℂ) *
        ((z e lam hh u v : ℂ) * ratio lam hh u v +
          I * e * Q e lam hh u v * phi lam hh u v / (1 - (mu e lam hh u v : ℂ)))‖ ≤
        F * (v - u) ^ 2 := by
    rcases hv.1.eq_or_lt with rfl | hux
    · simp [Recon.z]
    · have hx : 0 ≤ v - u := sub_nonneg.mpr hv.1
      have hpv : ‖phi lam hh u v‖ ≤ H := norm_phi_le hl hv.1
        (hlam.mono (Icc_subset_Icc le_rfl hv.2)) (hhc.mono (Icc_subset_Icc le_rfl hv.2))
        (fun s hs => (hlamB s ⟨hs.1, hs.2.trans hv.2⟩).1)
        (fun s hs => (hbound s ⟨hs.1, hs.2.trans hv.2⟩).1)
      have hgpos := hκ.trans_le (hgap v hv)
      have h1 : ‖(z e lam hh u v : ℂ) * ratio lam hh u v‖ ≤ Z * D * (v - u) ^ 3 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul (hz v hv) (hc v hv).1 (norm_nonneg _) (by positivity)).trans_eq (by ring)
      have h2 : ‖I * e * Q e lam hh u v * phi lam hh u v /
          (1 - (mu e lam hh u v : ℂ))‖ ≤ (|e| * K * H / κ) * (v - u) ^ 3 := by
        have hden : ‖(1 : ℂ) - (mu e lam hh u v : ℂ)‖ = 1 - mu e lam hh u v := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hgpos]
        rw [norm_div, hden]
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          _ ≤ (|e| * (K * (v - u) ^ 3) * H) / κ := by
            apply div_le_div₀ (by positivity) ?_ hκ (hgap v hv)
            gcongr
            exact (hc v hv).2.1
          _ = _ := by ring
      have hc1 : ‖-(I * e * A e lam hh u v) * hh u v‖ ≤ |e| * P * H * (v - u) ^ 2 := by
        rw [norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        calc
          _ ≤ |e| * (P * (v - u) ^ 2) * H := by
            gcongr <;> first | exact hA v hv | exact (hbound v hv).1
          _ = _ := by ring
      calc
        _ ≤ ‖-(I * e * A e lam hh u v) * hh u v‖ +
            ‖((-nu e lam hh u v / r lam u v : ℝ) : ℂ) *
              ((z e lam hh u v : ℂ) * ratio lam hh u v +
                I * e * Q e lam hh u v * phi lam hh u v / (1 - (mu e lam hh u v : ℂ)))‖ :=
          norm_add_le _ _
        _ ≤ |e| * P * H * (v - u) ^ 2 +
            N / l * (Z * D + |e| * K * H / κ) * (v - u) ^ 2 := by
          apply add_le_add hc1
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
            abs_of_pos (hrp v hv hux)]
          calc
            _ ≤ N / (l * (v - u)) *
                ((Z * D + |e| * K * H / κ) * (v - u) ^ 3) := by
              apply mul_le_mul
              · exact div_le_div₀ (by positivity) (hn v hv)
                  (mul_pos hl (sub_pos.mpr hux)) (hr v hv).1
              · exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)
              · positivity
              · positivity
            _ = _ := by field_simp
        _ = _ := by dsimp [F]; ring
  have cG : ContinuousOn (fun v => nu e lam hh u v / r lam u v * z e lam hh u v)
      (Icc u b) := by
    apply continuousOn_of_axis_bound (by simp) (g := fun v => G * (v - u))
      (by fun_prop) (by ring)
      (fun v hv => by simpa only [Real.norm_eq_abs] using hquot N hN _ (hn v hv) v hv)
    intro v hv hux
    exact ((cν v hv).div (cr v hv) (hrp v hv hux).ne').mul (cz v hv)
  have cF : ContinuousOn (fun v => -(I * e * A e lam hh u v) * hh u v +
      ((-nu e lam hh u v / r lam u v : ℝ) : ℂ) * ((z e lam hh u v : ℂ) * ratio lam hh u v +
        I * e * Q e lam hh u v * phi lam hh u v / (1 - (mu e lam hh u v : ℂ)))) (Icc u b) := by
    apply continuousOn_of_axis_bound (by simp [z]) (g := fun v => F * (v - u) ^ 2)
      (by fun_prop) (by ring) hFF
    intro v hv hux
    have cAv := cA v hv
    have chv := hhc v hv
    have cnv := cν v hv
    have crv := cr v hv
    have czv := cz v hv
    have cfv := cf v hv
    have cQv := cQ v hv
    have cpv := cp v hv
    have cmv := cμ v hv
    have hrn := (hrp v hv hux).ne'
    have hmn : (1 : ℂ) - (mu e lam hh u v : ℂ) ≠ 0 := by
      exact_mod_cast (hκ.trans_le (hgap v hv)).ne'
    have cof {f : ℝ → ℝ} (hf : ContinuousWithinAt f (Icc u b) v) :
        ContinuousWithinAt (fun x => (f x : ℂ)) (Icc u b) v :=
      Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt hf
    have conn := (((cof cAv).const_mul (I * (e : ℂ))).neg).mul chv
    have em := (((cof cQv).const_mul (I * (e : ℂ))).mul cpv).div
      ((continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => (1 : ℂ))
        (Icc u b) v).sub (cof cmv)) hmn
    exact conn.add ((cof (cnv.neg.div crv hrn)).mul (((cof czv).mul cfv).add em))
  refine ⟨cp, cQ, cm, cμ, ca, cb, cB, cν, cCA, cA, cG, cF, ?_⟩
  intro v hv
  refine ⟨(hBB v hv).trans ?_, (hCA v hv).trans ?_,
    (hquot N hN (nu e lam hh u v) (hn v hv) v hv).trans ?_, (hFF v hv).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith only [hB, hP, hG, hF])
      (sub_nonneg.mpr hv.1)
  · exact mul_le_mul_of_nonneg_right (by linarith only [hB, hP, hG, hF])
      (sub_nonneg.mpr hv.1)
  · change G * (v - u) ≤ _
    exact mul_le_mul_of_nonneg_right (by linarith only [hB, hP, hG, hF])
      (sub_nonneg.mpr hv.1)
  · exact mul_le_mul_of_nonneg_right (by linarith only [hB, hP, hG, hF])
      (sq_nonneg (v - u))

/-- [node restart-sec-independent-null-construction#outgoing-constraints]
[node restart-null-reconstruct-charge]
[node restart-null-reconstruct-mass]
[node restart-null-reconstruct-nu]
[node restart-null-reconstruct-potential]
On a nondegenerate bounded `C¹ᵥ` outgoing prefix the reconstruction solves the frozen
outgoing equations and all axis normalizations. Derivatives are within the closed section;
the scalar equation is asserted off axis, where its frozen quotient has its usual meaning.
No incoming equation or restriction on the size of the data is assumed. -/
theorem outgoing_constraints {l U H D L e κ u b : ℝ}
    {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ} {h' : ℝ → ℂ}
    (hl : 0 < l) (hlU : l ≤ U) (hH : 0 ≤ H) (hD : 0 ≤ D) (hL : 0 ≤ L) (hκ : 0 < κ)
    (hub : u ≤ b) (hbL : b - u ≤ L) (hlam : ContinuousOn (lam u) (Icc u b))
    (hlamB : ∀ s ∈ Icc u b, l ≤ lam u s ∧ lam u s ≤ U)
    (hder : ∀ s ∈ Icc u b, HasDerivWithinAt (hh u) (h' s) (Icc u b) s)
    (hbound : ∀ s ∈ Icc u b, ‖hh u s‖ ≤ H ∧ ‖h' s‖ ≤ D)
    (hgap : ∀ s ∈ Icc u b, κ ≤ 1 - mu e lam hh u s) :
    let S := toFields e lam hh
    (∀ v ∈ Icc u b,
      HasDerivWithinAt (S.r u) (S.lam u v) (Icc u b) v ∧
      HasDerivWithinAt (fun x => (S.r u x : ℂ) * S.phi u x)
        ((lam u v : ℂ) * hh u v) (Icc u b) v ∧
      HasDerivWithinAt (S.nu u) (S.rUV u v) (Icc u b) v ∧
      HasDerivWithinAt (S.m u) (S.mV u v) (Icc u b) v ∧
      HasDerivWithinAt (S.Q u) (S.QV e u v) (Icc u b) v ∧
      HasDerivWithinAt (S.A u) (S.AV u v) (Icc u b) v ∧
      (u < v → HasDerivWithinAt (S.phi u) (S.phiV u v) (Icc u b) v) ∧
      S.nu u v < 0 ∧ S.a u v = hh u v) ∧
    (S.r u u = 0 ∧ S.m u u = 0 ∧ S.Q u u = 0 ∧ S.A u u = 0 ∧
      S.lam u u + S.nu u u = 0 ∧ S.a u u = S.phi u u ∧ S.b u u = S.phi u u) ∧
    S.phi u u = hh u u ∧ Tendsto (S.mu u) (𝓝[Icc u b] u) (𝓝 0) ∧
    AbsolutelyContinuousOnInterval (S.nu u) u b ∧
    ∀ n : ℝ → ℝ, AbsolutelyContinuousOnInterval n u b → n u = -lam u u →
      (∀ᵐ x, x ∈ uIcc u b → HasDerivAt n
        (n x * (lam u x / r lam u x * z e lam hh u x)) x) →
      ∀ v ∈ Icc u b, n v = S.nu u v := by
  dsimp only
  obtain ⟨C, hC, hreg⟩ := coefficient_center_regularity (e := e) hl hlU hH hD hL hκ
  obtain ⟨cp, cQ, cm, cμ, ca, cb, cB, cν, cCA, cA, cG, cF, hest⟩ :=
    hreg lam hh h' u b hub hbL hlam hlamB hder hbound hgap
  have hhc : ContinuousOn (hh u) (Icc u b) := fun s hs => (hder s hs).continuousWithinAt
  refine ⟨?_, toFields_axis, phi_axis, ?_,
    ac_nu_of_integrable (cB.intervalIntegrable_of_Icc hub), ?_⟩
  · intro v hv
    have hlpos : 0 < lam u v := hl.trans_le (hlamB v hv).1
    refine ⟨hasDerivWithinAt_r hlam hv,
      hasDerivWithinAt_r_mul_phi hl hlam hhc (fun s hs => (hlamB s hs).1) hv,
      hasDerivWithinAt_nu_of_continuous cB hv, ?_, ?_,
      hasDerivWithinAt_A_of_continuous cCA hv, ?_,
      nu_neg (hl.trans_le (hlamB u ⟨le_rfl, hub⟩).1), toFields_a_eq hlpos.ne'⟩
    · have he : (toFields e lam hh).mV u v =
          (1 - mu e lam hh u v) * lam u v * ‖ratio lam hh u v‖ ^ 2 / 2 +
            lam u v * Q e lam hh u v ^ 2 / (2 * r lam u v ^ 2) := by
        dsimp only [Fields.mV, Fields.mu, toFields, mu]
        rcases hv.1.eq_or_lt with rfl | hux
        · simp
        · have hrpos := r_pos hl hux (hlam.mono (Icc_subset_Icc le_rfl hv.2))
            (fun s hs => (hlamB s ⟨hs.1, hs.2.trans hv.2⟩).1)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlpos]
          field_simp [hlpos.ne', hrpos.ne']
      change HasDerivWithinAt (m e lam hh u) ((toFields e lam hh).mV u v) (Icc u b) v
      rw [he]
      exact hasDerivWithinAt_m_of_continuous ca cb hv
    · change HasDerivWithinAt (Q e lam hh u)
        (-(e * r lam u v * (starRingEnd ℂ (phi lam hh u v) *
          ((lam u v : ℂ) * ratio lam hh u v)).im)) (Icc u b) v
      convert hasDerivWithinAt_Q_of_continuous hlam hhc cp hv using 1
      ring
    · intro huv
      exact hasDerivWithinAt_phi hlam hhc hv huv
        (r_pos hl huv (hlam.mono (Icc_subset_Icc le_rfl hv.2))
          (fun s hs => (hlamB s ⟨hs.1, hs.2.trans hv.2⟩).1)).ne'
  · change Tendsto (mu e lam hh u) (𝓝[Icc u b] u) (𝓝 0)
    simpa only [ContinuousWithinAt, mu_axis] using cμ u ⟨le_rfl, hub⟩
  · intro n hn haxis hd
    exact nu_eq_of_ac_of_ae_hasDerivAt hn (cB.intervalIntegrable_of_Icc hub) hd haxis

private theorem integralForm_of_closed_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E} {u b v : ℝ}
    (cf : ContinuousOn f (Icc u b)) (hg : IntervalIntegrable g volume u b)
    (hd : ∀ x ∈ Ioo u b, HasDerivAt f (g x) x) (hv : v ∈ Icc u b) :
    IntegralForm f g u v := by
  have hi := hg.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hv))
  exact ⟨hi, (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hv.1
    (cf.mono (Icc_subset_Icc le_rfl hv.2))
    (fun x hx => hd x ⟨hx.1, hx.2.trans_le hv.2⟩) hi).symm⟩

/-- [node restart-sec-independent-null-construction#outgoing-constraints]
The six frozen outgoing constraints in integral form on every axis-anchored prefix.
The singular scalar quotient is integrable even though its raw axis value can differ
from its continuous limit. All premises are candidate bounds and the nondegenerate gap. -/
theorem outgoing_integral_constraints {l U H D L e κ u b : ℝ}
    {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ} {h' : ℝ → ℂ}
    (hl : 0 < l) (hlU : l ≤ U) (hH : 0 ≤ H) (hD : 0 ≤ D) (hL : 0 ≤ L) (hκ : 0 < κ)
    (hub : u ≤ b) (hbL : b - u ≤ L) (hlam : ContinuousOn (lam u) (Icc u b))
    (hlamB : ∀ s ∈ Icc u b, l ≤ lam u s ∧ lam u s ≤ U)
    (hder : ∀ s ∈ Icc u b, HasDerivWithinAt (hh u) (h' s) (Icc u b) s)
    (hbound : ∀ s ∈ Icc u b, ‖hh u s‖ ≤ H ∧ ‖h' s‖ ≤ D)
    (hgap : ∀ s ∈ Icc u b, κ ≤ 1 - mu e lam hh u s) :
    let S := toFields e lam hh
    ∀ v ∈ Icc u b, IntegralForm (S.r u) (S.lam u) u v ∧
      IntegralForm (S.phi u) (S.phiV u) u v ∧ IntegralForm (S.Q u) (S.QV e u) u v ∧
      IntegralForm (S.m u) (S.mV u) u v ∧ IntegralForm (S.nu u) (S.rUV u) u v ∧
      IntegralForm (S.A u) (S.AV u) u v := by
  dsimp only
  obtain ⟨C, hC, hreg⟩ := coefficient_center_regularity (e := e) hl hlU hH hD hL hκ
  obtain ⟨cp, cQ, cm, cμ, ca, cb, cB, cν, cCA, cA, cG, cF, hest⟩ :=
    hreg lam hh h' u b hub hbL hlam hlamB hder hbound hgap
  have hU : 0 ≤ U := hl.le.trans hlU
  have hsol := (outgoing_constraints hl hlU hH hD hL hκ hub hbL hlam hlamB hder hbound hgap).1
  have hhc : ContinuousOn (hh u) (Icc u b) := fun s hs => (hder s hs).continuousWithinAt
  have cr : ContinuousOn (r lam u) (Icc u b) :=
    continuousOn_primitive hub (hlam.intervalIntegrable_of_Icc hub)
  have cf : ContinuousOn (ratio lam hh u) (Icc u b) := hhc.sub cp
  have cθ := (Complex.continuous_ofReal.comp_continuousOn hlam).mul cf
  have cqv : ContinuousOn ((toFields e lam hh).QV e u) (Icc u b) := by
    exact ((cr.mul (Complex.continuous_im.comp_continuousOn
      ((Complex.continuous_conj.comp_continuousOn cp).mul cθ))).const_mul (-e)).congr
        (by intro v hv; dsimp only [Fields.QV, toFields, Function.comp_apply, Pi.mul_apply]; ring)
  have cmv : ContinuousOn ((toFields e lam hh).mV u) (Icc u b) := by
    apply (((cb.const_mul (1 / 2 : ℝ)).sub (ca.mul cm))).congr
    intro v hv
    dsimp only [Fields.mV, Fields.mu, toFields, Pi.mul_apply, Pi.sub_apply]
    rcases hv.1.eq_or_lt with rfl | hux
    · simp
    · have hlpos := hl.trans_le (hlamB v hv).1
      have hrpos := r_pos hl hux (hlam.mono (Icc_subset_Icc le_rfl hv.2))
        (fun s hs => (hlamB s ⟨hs.1, hs.2.trans hv.2⟩).1)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlpos]
      field_simp [hlpos.ne', hrpos.ne']
      ring
  have cnv : ContinuousOn ((toFields e lam hh).rUV u) (Icc u b) :=
    (cν.mul cB).congr (by intro v hv; dsimp only [Fields.rUV, Fields.mu, toFields, z, mu,
      Function.comp_apply, Pi.mul_apply]; ring)
  obtain ⟨K, hK, hc⟩ := center_orders (e := e) hl hlU hH hD hL
  have hcent := hc lam hh h' u b hub hbL hlam hlamB hder hbound
  have hphiv (v) (hv : v ∈ Icc u b) :
      ‖(toFields e lam hh).phiV u v‖ ≤ U * D / l := by
    rcases hv.1.eq_or_lt with rfl | hux
    · dsimp only [Fields.phiV, toFields]
      rw [r_axis, Complex.ofReal_zero, div_zero, norm_zero]
      positivity
    · have hrpos := r_pos hl hux (hlam.mono (Icc_subset_Icc le_rfl hv.2))
        (fun s hs => (hlamB s ⟨hs.1, hs.2.trans hv.2⟩).1)
      have hrlo := (r_bounds hv.1 (hlam.mono (Icc_subset_Icc le_rfl hv.2))
        (fun s hs => (hlamB s ⟨hs.1, hs.2.trans hv.2⟩).1)
        (fun s hs => (hlamB s ⟨hs.1, hs.2.trans hv.2⟩).2)).1
      have hnum : |‖(lam u v : ℂ) * ratio lam hh u v‖| ≤
          (U * D) * (v - u) ^ (0 + 1) := by
        rw [abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hl.trans_le (hlamB v hv).1)]
        calc
          _ ≤ U * (D * (v - u)) := mul_le_mul (hlamB v hv).2
            (hcent v hv).1 (norm_nonneg _) (hl.le.trans hlU)
          _ = _ := by ring
      have hb := abs_div_pow_le_of_order (n := 0) (j := 1)
        hl (sub_pos.mpr hux) (by positivity : 0 ≤ U * D) hrlo hnum
      simpa only [Fields.phiV, toFields, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hrpos, abs_div, abs_of_nonneg (norm_nonneg _), pow_one, pow_zero,
        mul_one] using hb
  have hmeas : AEStronglyMeasurable ((toFields e lam hh).phiV u) (volume.restrict (Icc u b)) :=
    ((cθ.aestronglyMeasurable measurableSet_Icc).aemeasurable.div
      ((Complex.continuous_ofReal.comp_continuousOn cr).aestronglyMeasurable
        measurableSet_Icc).aemeasurable).aestronglyMeasurable
  have hip : IntervalIntegrable ((toFields e lam hh).phiV u) volume u b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hub]
    apply (integrableOn_const (μ := volume) (s := Icc u b) (C := U * D / l)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact hphiv v hv
  have hd (v) (hv : v ∈ Ioo u b) := hsol v ⟨hv.1.le, hv.2.le⟩
  intro v hv
  refine ⟨integralForm_of_closed_derivative cr (hlam.intervalIntegrable_of_Icc hub)
      (fun x hx => (hd x hx).1.hasDerivAt (Icc_mem_nhds hx.1 hx.2)) hv,
    integralForm_of_closed_derivative cp hip
      (fun x hx => ((hd x hx).2.2.2.2.2.2.1 hx.1).hasDerivAt (Icc_mem_nhds hx.1 hx.2)) hv,
    integralForm_of_closed_derivative cQ (cqv.intervalIntegrable_of_Icc hub)
      (fun x hx => (hd x hx).2.2.2.2.1.hasDerivAt (Icc_mem_nhds hx.1 hx.2)) hv,
    integralForm_of_closed_derivative cm (cmv.intervalIntegrable_of_Icc hub)
      (fun x hx => (hd x hx).2.2.2.1.hasDerivAt (Icc_mem_nhds hx.1 hx.2)) hv,
    integralForm_of_closed_derivative cν (cnv.intervalIntegrable_of_Icc hub)
      (fun x hx => (hd x hx).2.2.1.hasDerivAt (Icc_mem_nhds hx.1 hx.2)) hv,
    integralForm_of_closed_derivative cA (cCA.intervalIntegrable_of_Icc hub)
      (fun x hx => (hd x hx).2.2.2.2.2.1.hasDerivAt (Icc_mem_nhds hx.1 hx.2)) hv⟩

end EmcsfAcExtension.Local.Null
