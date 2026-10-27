module

public import EmcsfAcExtension.Local.Stability.DifferenceMomentsFieldForcing
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Incoming difference forcing, including the connection

The first connection cancels in the norm equation. Its difference is
bounded using the finite potential distance and the fixed geometric box.
-/

public section

open Set
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The radial part of the incoming difference forcing has the universal
coefficients `4`, `16`, `20`, independently of every solution parameter
and the minimum radius. The connection is estimated separately. -/
theorem stab_in_difference_radial_forcing_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ≤ 1)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖kC1 e (triangle 0 T) S₁ u v / ((1 - S₁.mu u v : ℝ) : ℂ) -
      kC1 e (triangle 0 T) S₂ u v / ((1 - S₂.mu u v : ℝ) : ℂ) -
      (S₁.nu u v / S₁.r u v - S₂.nu u v / S₂.r u v) •
        (S₂.xi u v / (S₂.nu u v : ℂ) -
          ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2 •
            (S₂.xi u v / (S₂.nu u v : ℂ)))‖ ≤
      4 * ‖kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v‖ +
      16 * (supDist T S₁.mu S₂.mu).toReal * ‖kC1 e (triangle 0 T) S₂ u v‖ +
      20 * (geomDist T S₁ S₂).toReal * (-S₁.nu u v / S₁.r u v) *
        ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hb₁ := h₁s.box.2 (u, v) hp
  have hb₂ := h₂s.box.2 (u, v) hp
  have hx : ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ≤ 1 :=
    ((le_add_of_nonneg_left (norm_nonneg (S₂.theta u v / (S₂.lam u v : ℂ)))).trans
      hb₂.2.2.2.2.2.1).trans hε
  have hf := stab_radial_difference_forcing_le hb₁.2.2.2.2.1 hb₂.2.2.2.2.1 hx
    (j₁ := kC1 e (triangle 0 T) S₁ u v) (j₂ := kC1 e (triangle 0 T) S₂ u v)
    (a₁ := S₁.nu u v / S₁.r u v) (a₂ := S₂.nu u v / S₂.r u v)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (stab_mu_sub_le h₁s h₂s hp) (by norm_num : (0 : ℝ) ≤ 16))
    (norm_nonneg (kC1 e (triangle 0 T) S₂ u v))
  have hw := stab_in_weight_sub_le h₁s h₂s hu huv hvT
  have hw' : |S₁.nu u v / S₁.r u v - S₂.nu u v / S₂.r u v| ≤
      20 * (geomDist T S₁ S₂).toReal * (-S₁.nu u v / S₁.r u v) := by
    simpa only [neg_div, neg_sub_neg, abs_sub_comm] using hw
  have hg := mul_le_mul_of_nonneg_right hw'
    (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))
  exact hf.trans (add_le_add (add_le_add le_rfl hm) hg)

/-- The potential distance is finite by classical continuity, before any
potential comparison estimate or absorption is available. -/
theorem stab_potentialDist_ne_top
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) : supDist T S₁.A S₂.A ≠ ⊤ :=
  supDist_ne_top_of_continuousOn h₁s.c1.c1_A.continuousOn h₂s.c1.c1_A.continuousOn

/-- The incoming connection difference is bounded by `4PB`, where
`P = T|e|‖δA‖∞` and `B = -ν₁/r₁`. The literal coefficient `4` is
uniform in all parameters and the pair; no potential estimate is assumed. -/
theorem stab_connection_difference_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |e * (S₁.A u v - S₂.A u v)| ≤
      4 * (T * |e| * (supDist T S₁.A S₂.A).toReal) * (-S₁.nu u v / S₁.r u v) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := h₁s.c1.r_pos (u, v) hp huv
  have hrT : S₁.r u v ≤ T := by
    have hb := (stab_radius_bounds h₁s hu huv.le hvT).2
    linarith only [hb, hu, hvT]
  have hB : 1 ≤ 4 * T * (-S₁.nu u v / S₁.r u v) := by
    rw [← mul_div_assoc, le_div_iff₀ hr]
    have hn := mul_le_mul_of_nonneg_left (h₁s.box.2 (u, v) hp).2.2.1 h₁s.pos.le
    linarith only [hn, hrT]
  have hA : |S₁.A u v - S₂.A u v| ≤ (supDist T S₁.A S₂.A).toReal := by
    have hh : ‖S₁.A u v - S₂.A u v‖ₑ ≤ supDist T S₁.A S₂.A :=
      le_iSup₂_of_le (u, v) hp le_rfl
    rw [← ofReal_norm, Real.norm_eq_abs] at hh
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using
      ENNReal.toReal_mono (stab_potentialDist_ne_top h₁s h₂s) hh
  rw [abs_mul]
  calc
    _ ≤ |e| * (supDist T S₁.A S₂.A).toReal :=
      mul_le_mul_of_nonneg_left hA (abs_nonneg e)
    _ ≤ (|e| * (supDist T S₁.A S₂.A).toReal) *
        (4 * T * (-S₁.nu u v / S₁.r u v)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hB
        (mul_nonneg (abs_nonneg e) ENNReal.toReal_nonneg)
    _ = _ := by ring

/-- The full incoming forcing is bounded by the label density with
coefficients `4`, `16`, `20`, with `G+P` as its geometric coefficient.
All coefficients are universal; the potential feedback remains explicit. -/
theorem stab_in_difference_forcing_enorm_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ≤ 1)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ENNReal.ofReal
      ‖kC1 e (triangle 0 T) S₁ u v / ((1 - S₁.mu u v : ℝ) : ℂ) -
        kC1 e (triangle 0 T) S₂ u v / ((1 - S₂.mu u v : ℝ) : ℂ) -
        (S₁.nu u v / S₁.r u v - S₂.nu u v / S₂.r u v) •
          (S₂.xi u v / (S₂.nu u v : ℂ) -
            ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2 • (S₂.xi u v / (S₂.nu u v : ℂ))) -
        (e * (S₁.A u v - S₂.A u v)) • (Complex.I * (S₂.xi u v / (S₂.nu u v : ℂ)))‖ ≤
      4 * inEnv T (fun u v => kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v) u +
      16 * ENNReal.ofReal (supDist T S₁.mu S₂.mu).toReal *
        inEnv T (kC1 e (triangle 0 T) S₂) u +
      20 * ENNReal.ofReal ((geomDist T S₁ S₂).toReal +
        T * |e| * (supDist T S₁.A S₂.A).toReal) *
        ENNReal.ofReal (-S₁.nu u v / S₁.r u v) *
          ENNReal.ofReal ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ := by
  let z := S₂.xi u v / (S₂.nu u v : ℂ)
  let f := kC1 e (triangle 0 T) S₁ u v / ((1 - S₁.mu u v : ℝ) : ℂ) -
    kC1 e (triangle 0 T) S₂ u v / ((1 - S₂.mu u v : ℝ) : ℂ) -
    (S₁.nu u v / S₁.r u v - S₂.nu u v / S₂.r u v) • (z - ‖z‖ ^ 2 • z)
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hB : 0 ≤ -S₁.nu u v / S₁.r u v := div_nonneg
    (neg_pos.mpr (h₁s.c1.nu_neg (u, v) hp)).le (h₁s.c1.r_pos (u, v) hp huv).le
  have hT := h₁s.pos
  have hP : 0 ≤ T * |e| * (supDist T S₁.A S₂.A).toReal := by positivity
  have hconn : ‖(e * (S₁.A u v - S₂.A u v)) • (Complex.I * z)‖ ≤
      4 * (T * |e| * (supDist T S₁.A S₂.A).toReal) *
        (-S₁.nu u v / S₁.r u v) * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul]
    exact mul_le_mul_of_nonneg_right (stab_connection_difference_le h₁s h₂s hu huv hvT)
      (norm_nonneg z)
  have hraw := stab_in_difference_radial_forcing_le h₁s h₂s hε hu huv hvT
  have hcoef : 4 * (T * |e| * (supDist T S₁.A S₂.A).toReal) *
      (-S₁.nu u v / S₁.r u v) * ‖z‖ ≤
      20 * (T * |e| * (supDist T S₁.A S₂.A).toReal) *
        (-S₁.nu u v / S₁.r u v) * ‖z‖ := by
    gcongr
    norm_num
  have hf : ‖f - (e * (S₁.A u v - S₂.A u v)) • (Complex.I * z)‖ ≤
      4 * ‖kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v‖ +
      16 * (supDist T S₁.mu S₂.mu).toReal * ‖kC1 e (triangle 0 T) S₂ u v‖ +
      20 * ((geomDist T S₁ S₂).toReal + T * |e| * (supDist T S₁.A S₂.A).toReal) *
        (-S₁.nu u v / S₁.r u v) * ‖z‖ := by
    calc
      _ ≤ ‖f‖ + ‖(e * (S₁.A u v - S₂.A u v)) • (Complex.I * z)‖ := norm_sub_le _ _
      _ ≤ (4 * ‖kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v‖ +
          16 * (supDist T S₁.mu S₂.mu).toReal * ‖kC1 e (triangle 0 T) S₂ u v‖ +
          20 * (geomDist T S₁ S₂).toReal * (-S₁.nu u v / S₁.r u v) * ‖z‖) +
          4 * (T * |e| * (supDist T S₁.A S₂.A).toReal) *
            (-S₁.nu u v / S₁.r u v) * ‖z‖ := add_le_add hraw hconn
      _ ≤ (4 * ‖kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v‖ +
          16 * (supDist T S₁.mu S₂.mu).toReal * ‖kC1 e (triangle 0 T) S₂ u v‖ +
          20 * (geomDist T S₁ S₂).toReal * (-S₁.nu u v / S₁.r u v) * ‖z‖) +
          20 * (T * |e| * (supDist T S₁.A S₂.A).toReal) *
            (-S₁.nu u v / S₁.r u v) * ‖z‖ := add_le_add le_rfl hcoef
      _ = _ := by ring
  have he := ENNReal.ofReal_le_ofReal hf
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)] at he
  repeat rw [ENNReal.ofReal_mul (by positivity)] at he
  norm_num only [ENNReal.ofReal_ofNat] at he
  have hD : ENNReal.ofReal ‖kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v‖ ≤
      inEnv T (fun u v => kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v) u := by
    rw [ofReal_norm]
    exact le_iSup₂_of_le v ⟨huv.le, hvT⟩ le_rfl
  have hK : ENNReal.ofReal ‖kC1 e (triangle 0 T) S₂ u v‖ ≤
      inEnv T (kC1 e (triangle 0 T) S₂) u := by
    rw [ofReal_norm]
    exact le_iSup₂_of_le v ⟨huv.le, hvT⟩ le_rfl
  exact he.trans (add_le_add (add_le_add (mul_le_mul' le_rfl hD)
    (mul_le_mul' le_rfl hK)) le_rfl)

end EmcsfAcExtension.Local
