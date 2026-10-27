module

public import EmcsfAcExtension.Local.Stability.JCloseInitialCharge
import EmcsfAcExtension.Local.Stability.JCloseInitialAlgebra
import EmcsfAcExtension.Local.Stability.JCloseBarrier
import EmcsfAcExtension.Local.Stability.SourceDifferenceCharge
import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Calculus.AxisRatio

/-! # Data-only initial mass-ratio comparison

The common initial radius removes every geometric forcing term. The
singular damping coefficient is handled by a continuous endpoint barrier.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Stab

/-- The initial mass ratio depends Lipschitzly on the data, with its full
small factor `ε`. `C` is universal, independent of the coupling, length,
background, envelope and all initial or solution derivative suprema. -/
theorem initial_mass_difference : ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ≤ 1 → sigma e M T ≤ 1 →
      ∀ v ∈ Icc 0 T, |S₁.mu 0 v - S₂.mu 0 v| ≤ C * ε * dataDist h₁ h₂ T := by
  refine ⟨8, by norm_num, ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁
  let δ := dataDist h₁ h₂ T
  let f := fun v => S₁.mu 0 v - S₂.mu 0 v
  let p := fun v => S₁.lam 0 v / S₁.r 0 v * (1 + ‖S₁.theta 0 v / S₁.lam 0 v‖ ^ 2)
  let q := fun v => S₁.lam 0 v / S₁.r 0 v *
    ((1 - S₂.mu 0 v) * (‖S₁.theta 0 v / S₁.lam 0 v‖ ^ 2 - ‖S₂.theta 0 v / S₂.lam 0 v‖ ^ 2) +
      (S₁.Q 0 v ^ 2 - S₂.Q 0 v ^ 2) / S₁.r 0 v ^ 2)
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hM : 0 ≤ M := zero_le_one.trans hs₂.box.1
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hc₁ := (continuousOn_mu_aux hs₁.pos hs₁.c1).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (show MapsTo (fun v => (0, v)) (Icc 0 T) (triangle 0 T) from fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have hc₂ := (continuousOn_mu_aux hs₂.pos hs₂.c1).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (show MapsTo (fun v => (0, v)) (Icc 0 T) (triangle 0 T) from fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have hf : ContinuousOn f (Icc 0 T) := by simpa only [f, Pi.sub_def] using! hc₁.sub hc₂
  have h₀ : |f 0| ≤ 8 * ε * δ := by
    have hr₁ := (hs₁.c1.axis 0 ⟨le_rfl, le_rfl, hs₁.pos.le⟩).1
    have hr₂ := (hs₂.c1.axis 0 ⟨le_rfl, le_rfl, hs₂.pos.le⟩).1
    simp only [f, Fields.mu, hr₁, hr₂, div_zero, sub_self, abs_zero]
    positivity
  have hd (v : ℝ) (hv : v ∈ Ioo 0 T) : HasDerivAt f (-p v * f v + q v) v := by
    have hd₁ := (outgoing_mu_derivative_identity hs₁.c1 le_rfl hv.1 hv.2.le).hasDerivAt
      (Icc_mem_nhds hv.1 hv.2)
    have hd₂ := (outgoing_mu_derivative_identity hs₂.c1 le_rfl hv.1 hv.2.le).hasDerivAt
      (Icc_mem_nhds hv.1 hv.2)
    convert hd₁.sub hd₂ using 1
    dsimp only [p, q, f]
    rw [initial_lam_of_stabSetting hs₁ ⟨hv.1.le, hv.2.le⟩,
      initial_lam_of_stabSetting hs₂ ⟨hv.1.le, hv.2.le⟩,
      (hs₁.data.1 v ⟨hv.1.le, hv.2.le⟩).1, (hs₂.data.1 v ⟨hv.1.le, hv.2.le⟩).1]
    ring
  have hp (v : ℝ) (hv : v ∈ Ioo 0 T) : 0 ≤ p v := by
    have hr := hs₁.c1.r_pos (0, v) ⟨le_rfl, hv.1.le, hv.2.le⟩ hv.1
    have hl := hs₁.c1.lam_pos (0, v) ⟨le_rfl, hv.1.le, hv.2.le⟩
    dsimp only [p]
    positivity
  have hq (v : ℝ) (hv : v ∈ Ioo 0 T) : |q v| ≤ p v * (8 * ε * δ) := by
    have hvT : v ∈ Icc 0 T := ⟨hv.1.le, hv.2.le⟩
    have hpv : (0, v) ∈ triangle 0 T := ⟨le_rfl, hv.1.le, hv.2.le⟩
    have hr := hs₁.c1.r_pos (0, v) hpv hv.1
    have hl := hs₁.c1.lam_pos (0, v) hpv
    have hγ := initial_gamma_le_one hs₂ hvT
    have hx₁ := (le_add_of_nonneg_right (norm_nonneg _)).trans (hs₁.box.2 (0, v) hpv).2.2.2.2.2.1
    have hx₂ := (le_add_of_nonneg_right (norm_nonneg _)).trans (hs₂.box.2 (0, v) hpv).2.2.2.2.2.1
    have hxd := (initial_scalar_ratio_difference_le hs₁ hs₂ hvT).2
    have hxsq : |‖S₁.theta 0 v / S₁.lam 0 v‖ ^ 2 - ‖S₂.theta 0 v / S₂.lam 0 v‖ ^ 2| ≤ 4 * ε * δ :=
        by
      have h := (abs_norm_sq_difference_le hx₁ hx₂).trans
        (mul_le_mul_of_nonneg_left hxd (by positivity : 0 ≤ 2 * ε))
      nlinarith only [h]
    have hsc : |(1 - S₂.mu 0 v) *
        (‖S₁.theta 0 v / S₁.lam 0 v‖ ^ 2 - ‖S₂.theta 0 v / S₂.lam 0 v‖ ^ 2)| ≤ 4 * ε * δ := by
      rw [abs_mul, abs_of_pos hγ.1]
      simpa only [one_mul] using mul_le_mul hγ.2 hxsq (abs_nonneg _) zero_le_one
    have hrcommon : S₂.r 0 v = S₁.r 0 v := by rw [(hs₁.data.1 v hvT).1, (hs₂.data.1 v hvT).1]
    have hQ₁ := em_charge_bound_from_setting hs₁ hpv
    have hQ₂ := em_charge_bound_from_setting hs₂ hpv
    rw [hrcommon] at hQ₂
    have hQsum : |S₁.Q 0 v + S₂.Q 0 v| ≤ |e| * M * ε * S₁.r 0 v ^ 2 :=
      (abs_add_le _ _).trans (by linarith only [hQ₁, hQ₂])
    have hQdiff := initial_charge_difference_le hs₁ hs₂ hε₁ hvT
    have hcharge : |(S₁.Q 0 v ^ 2 - S₂.Q 0 v ^ 2) / S₁.r 0 v ^ 2| ≤
        3 * sigma e M T * ε * δ := by
      rw [show S₁.Q 0 v ^ 2 - S₂.Q 0 v ^ 2 =
          (S₁.Q 0 v - S₂.Q 0 v) * (S₁.Q 0 v + S₂.Q 0 v) by ring,
        abs_div, abs_mul, abs_of_pos (pow_pos hr 2)]
      have hprod := mul_le_mul hQdiff hQsum (abs_nonneg _) (by positivity)
      have hscaled : (3 * |e| * M * δ * S₁.r 0 v ^ 2) *
          (|e| * M * ε * S₁.r 0 v ^ 2) / S₁.r 0 v ^ 2 =
            3 * e ^ 2 * M ^ 2 * ε * δ * S₁.r 0 v ^ 2 := by
        rw [← sq_abs e]
        field_simp
      have hrbound : S₁.r 0 v ^ 2 ≤ (T / 2) ^ 2 := by
        rw [(hs₁.data.1 v hvT).1]
        exact pow_le_pow_left₀ (div_nonneg hvT.1 (by norm_num)) (div_le_div_of_nonneg_right hvT.2
            (by norm_num)) 2
      calc
        _ ≤ _ := div_le_div_of_nonneg_right hprod (sq_nonneg _)
        _ = _ := hscaled
        _ ≤ 3 * e ^ 2 * M ^ 2 * ε * δ * (T / 2) ^ 2 := by gcongr
        _ = _ := by dsimp only [sigma]; ring
    have hcharge' : |(S₁.Q 0 v ^ 2 - S₂.Q 0 v ^ 2) / S₁.r 0 v ^ 2| ≤ 3 * ε * δ := by
      have h := mul_le_mul_of_nonneg_right hσ₁ (by positivity : 0 ≤ 3 * ε * δ)
      nlinarith only [hcharge, h]
    have hforcing := (abs_add_le _ _).trans (add_le_add hsc hcharge')
    dsimp only [p, q]
    rw [abs_mul, abs_of_pos (div_pos hl hr)]
    have h := mul_le_mul_of_nonneg_left hforcing (div_pos hl hr).le
    have hnonneg := mul_nonneg (sq_nonneg ‖S₁.theta 0 v / S₁.lam 0 v‖)
      (by positivity : 0 ≤ 8 * ε * δ)
    have hscale := mul_le_mul_of_nonneg_left (by nlinarith only [hnonneg, hε, hδ] :
      4 * ε * δ + 3 * ε * δ ≤ (1 + ‖S₁.theta 0 v / S₁.lam 0 v‖ ^ 2) * (8 * ε * δ))
      (div_pos hl hr).le
    nlinarith only [h, hscale]
  exact abs_real_transport_le_barrier hs₁.pos hf h₀ hd hp hq

end EmcsfAcExtension.Local.Stab
