module

public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Stability.DifferenceMomentsForcing

/-! # Algebra for characteristic derivative differences

The reconstructions in approved internal project record, (S2)–(S4), keep the inverse-gap
and cubic differences separate. These are pointwise auxiliary lemmas;
the section integrals and comparison closure are separate obligations.
-/

public section

namespace EmcsfAcExtension.Local

/-- The moving-weight cubic difference has coefficients `3` and `1`,
uniformly in the weights, radius of the scalar ball and scalar values. -/
theorem stab_weighted_cubic_sub_le {a b ε : ℝ} {z w : ℂ}
    (ha : 0 ≤ a) (hz : ‖z‖ ≤ ε) (hw : ‖w‖ ≤ ε) :
    ‖a • (‖z‖ ^ 2 • z) - b • (‖w‖ ^ 2 • w)‖ ≤
      3 * ε ^ 2 * (a * ‖z - w‖) + |a - b| * ε ^ 2 * ‖w‖ := by
  have hsplit : a • (‖z‖ ^ 2 • z) - b • (‖w‖ ^ 2 • w) =
      a • (‖z‖ ^ 2 • z - ‖w‖ ^ 2 • w) + (a - b) • (‖w‖ ^ 2 • w) := by
    rw [smul_sub, sub_smul]
    abel
  have hw2 : ‖w‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  calc
    _ ≤ ‖a • (‖z‖ ^ 2 • z - ‖w‖ ^ 2 • w)‖ +
        ‖(a - b) • (‖w‖ ^ 2 • w)‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ = a * ‖‖z‖ ^ 2 • z - ‖w‖ ^ 2 • w‖ +
        |a - b| * (‖w‖ ^ 2 * ‖w‖) := by
      rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
        abs_of_nonneg (sq_nonneg ‖w‖)]
    _ ≤ a * (3 * ε ^ 2 * ‖z - w‖) +
        |a - b| * (ε ^ 2 * ‖w‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (stab_cubic_sub_le hz hw) ha)
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hw2 (norm_nonneg _)) (abs_nonneg _))
    _ = _ := by ring

/-- Reconstructed characteristic derivatives have the explicit inverse-gap
and cubic difference bound of internal project record (S3)–(S4). All coefficients are
universal for the fixed gap `1/4`; neither scalar is used as a divisor. -/
theorem stab_reconstructed_derivative_sub_le
    {d₁ d₂ j₁ j₂ z₁ z₂ : ℂ} {μ₁ μ₂ a₁ a₂ ε : ℝ}
    (hg₁ : 1 / 4 ≤ 1 - μ₁) (hg₂ : 1 / 4 ≤ 1 - μ₂)
    (ha : 0 ≤ a₁) (hz₁ : ‖z₁‖ ≤ ε) (hz₂ : ‖z₂‖ ≤ ε)
    (hd₁ : d₁ = j₁ / ((1 - μ₁ : ℝ) : ℂ) + a₁ • (‖z₁‖ ^ 2 • z₁))
    (hd₂ : d₂ = j₂ / ((1 - μ₂ : ℝ) : ℂ) + a₂ • (‖z₂‖ ^ 2 • z₂)) :
    ‖d₁ - d₂‖ ≤ 4 * ‖j₁ - j₂‖ + 16 * |μ₁ - μ₂| * ‖j₂‖ +
      3 * ε ^ 2 * (a₁ * ‖z₁ - z₂‖) + |a₁ - a₂| * ε ^ 2 * ‖z₂‖ := by
  have hquot := stab_radial_difference_forcing_le
    (j₁ := j₁) (j₂ := j₂) (z₂ := 0) (a₁ := 0) (a₂ := 0)
    hg₁ hg₂ (by norm_num)
  simp only [sub_self, zero_smul, sub_zero, norm_zero, mul_zero, add_zero] at hquot
  have hcubic := stab_weighted_cubic_sub_le (b := a₂) ha hz₁ hz₂
  have hsplit : d₁ - d₂ =
      (j₁ / ((1 - μ₁ : ℝ) : ℂ) - j₂ / ((1 - μ₂ : ℝ) : ℂ)) +
        (a₁ • (‖z₁‖ ^ 2 • z₁) - a₂ • (‖z₂‖ ^ 2 • z₂)) := by
    rw [hd₁, hd₂]
    abel
  rw [hsplit]
  exact (norm_add_le _ _).trans (by
    simpa only [add_assoc] using add_le_add hquot hcubic)

/-- The definition of `jC1` reconstructs the outgoing derivative wherever
the mass gap is nonzero, with no estimate or regularity assumption. -/
theorem stab_out_derivative_reconstruction {D : Set (ℝ × ℝ)} {S : Fields}
    {u v : ℝ} (hgap : 1 - S.mu u v ≠ 0) :
    pdV D S.a u v = jC1 D S u v / ((1 - S.mu u v : ℝ) : ℂ) +
      (S.lam u v / S.r u v) •
        (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 •
          (S.theta u v / (S.lam u v : ℂ))) := by
  have hgapC : (1 - (S.mu u v : ℂ)) ≠ 0 := by exact_mod_cast hgap
  simp only [jC1, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_one]
  rw [mul_div_cancel_left₀ _ hgapC]
  ring

/-- The definition of `kC1` reconstructs the incoming derivative in its
own connection. The mass gap is the only divisor required to be nonzero. -/
theorem stab_in_derivative_reconstruction {D : Set (ℝ × ℝ)} {S : Fields}
    {e u v : ℝ} (hgap : 1 - S.mu u v ≠ 0) :
    pdU D S.b u v + Complex.I * e * S.A u v * S.b u v =
      kC1 e D S u v / ((1 - S.mu u v : ℝ) : ℂ) +
        (S.nu u v / S.r u v) •
          (‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 •
            (S.xi u v / (S.nu u v : ℂ))) := by
  have hgapC : (1 - (S.mu u v : ℂ)) ≠ 0 := by exact_mod_cast hgap
  simp only [kC1, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_one]
  rw [mul_div_cancel_left₀ _ hgapC]
  ring

/-- Converting the difference of two own-connection incoming derivatives
to an ordinary derivative retains both connection errors. The coefficients
are exactly one, uniformly in the scalar background and coupling. -/
theorem stab_ordinary_incoming_derivative_sub_le
    (D : Set (ℝ × ℝ)) (S₁ S₂ : Fields) (e u v : ℝ) :
    ‖pdU D S₁.b u v - pdU D S₂.b u v‖ ≤
      ‖(pdU D S₁.b u v + Complex.I * e * S₁.A u v * S₁.b u v) -
        (pdU D S₂.b u v + Complex.I * e * S₂.A u v * S₂.b u v)‖ +
      |e| * (|S₁.A u v - S₂.A u v| * ‖S₁.b u v‖ +
        |S₂.A u v| * ‖S₁.b u v - S₂.b u v‖) := by
  have hsplit : pdU D S₁.b u v - pdU D S₂.b u v =
      ((pdU D S₁.b u v + Complex.I * e * S₁.A u v * S₁.b u v) -
        (pdU D S₂.b u v + Complex.I * e * S₂.A u v * S₂.b u v)) -
      (Complex.I * e * ((S₁.A u v - S₂.A u v : ℝ) : ℂ) * S₁.b u v +
        Complex.I * e * S₂.A u v * (S₁.b u v - S₂.b u v)) := by
    push_cast
    ring
  rw [hsplit]
  apply (norm_sub_le _ _).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ‖Complex.I * e * ((S₁.A u v - S₂.A u v : ℝ) : ℂ) * S₁.b u v‖ +
        ‖Complex.I * e * S₂.A u v * (S₁.b u v - S₂.b u v)‖ := norm_add_le _ _
    _ = _ := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      ring

end EmcsfAcExtension.Local
