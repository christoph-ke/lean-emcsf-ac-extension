module

public import EmcsfAcExtension.Global.Defs.Renormalized
public import EmcsfAcExtension.Global.Calculus.Normalized
public import EmcsfAcExtension.Global.Calculus.Gauge
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Algebra.JTransport

/-! # Incoming normalized transport and complex cancellations

The incoming system and both complex cancellations of
`charged_SF_new_version.tex:L3212–L3253`. All field identities use the frozen AC class.
The commutator is the AC test-section product identity `main_gauge`.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Renormalized

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [node lem:ct-renormalized#incoming-system]
The two incoming normalized scalar equations in the original AC class.
The first equation is `normalized_in_section`; subtracting `φ_u` gives
this equation for `θ/λ`, with the connection term displayed. -/
theorem incoming_ratio_section (hS : IsSolution e S D) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b < v) (hs : inSeg a b v ⊆ D) :
    AbsolutelyContinuousOnInterval (fun u => S.theta u v / S.lam u v) a b ∧
    ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt
      (fun x => S.theta x v / S.lam x v)
      ((-(S.nu u v : ℂ) / S.r u v) *
        (S.xi u v / S.nu u v +
          ((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
            (1 - S.mu u v) * (S.theta u v / S.lam u v) +
          I * e * S.Q u v * S.phi u v / (1 - S.mu u v)) -
        I * e * S.A u v * (S.theta u v / S.lam u v)) u := by
  have ha := Calculus.normalized_in_section hS hab hbv hs
  have h := Local.IsSolution.in_section hS hab hbv hs
  have hy : (fun u => S.theta u v / S.lam u v) =
      (fun u => S.a u v - S.phi u v) := by
    funext u
    simp [Fields.a]
  rw [hy]
  refine ⟨ha.1.sub h.2.2.2.2.1.1, ?_⟩
  filter_upwards [ha.2, h.2.2.2.2.1.2, ae_restrict_mem measurableSet_Icc]
    with u hau hpu hu
  have hp : (u, v) ∈ D := hs ⟨hu.1, hu.2, rfl⟩
  apply (hau.sub hpu).congr_deriv
  dsimp only [Fields.phiU, Fields.a]
  field_simp [Complex.ofReal_ne_zero.mpr (hS.nu_neg (u, v) hp).ne,
    Complex.ofReal_ne_zero.mpr (hS.r_pos (u, v) hp (hu.2.trans_lt hbv)).ne',
    Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) hp).ne',
    show 1 - (S.mu u v : ℂ) ≠ 0 from by
      exact_mod_cast (hS.one_sub_mu_pos (u, v) hp).ne']
  ring

/-- [node lem:ct-renormalized#complex-cubic-cancellation]
Both neutral complex contributions to the cubic derivative are retained;
`2 Re(conj y z) y + |y|² z = y² conj z + 2 |y|² z`.
No field equation, regularity, or real-valued scalar assumption enters. -/
theorem complex_cubic_cancellation (y z : ℂ) :
    2 * (((starRingEnd ℂ y * z).re : ℝ) : ℂ) * y + (‖y‖ : ℂ) ^ 2 * z =
      y ^ 2 * starRingEnd ℂ z + 2 * (‖y‖ : ℂ) ^ 2 * z := by
  rw [← Complex.conj_mul']
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pow_two] <;> ring

/-- [node lem:ct-renormalized#electromagnetic-current-cancellation]
The outgoing Maxwell source is precisely the imaginary-part current in
normalized variables. This is the current substitution in the landed
j-transport algebra, with no derivative of the charge presumed. -/
theorem electromagnetic_current_cancellation (e : ℝ) (S : Fields) (u v : ℝ) :
    (S.QV e u v : ℂ) = I * e * S.r u v / 2 *
      (starRingEnd ℂ (S.phi u v) * S.theta u v -
        S.phi u v * starRingEnd ℂ (S.theta u v)) := by
  apply Complex.ext <;> simp [Fields.QV, Complex.mul_re, Complex.mul_im]
  ring

/-- [node lem:ct-renormalized#electromagnetic-current-cancellation]
The real part retained in the cubic derivative is exactly the negative
charge-current contribution. The normalized radial Maxwell current is
`-e r Im(conj φ y)`; there are no estimate constants. -/
theorem electromagnetic_real_part_cancellation (e r mu Q : ℝ) (phi y : ℂ)
    (hr : r ≠ 0) (hg : 1 - mu ≠ 0) :
    (starRingEnd ℂ y * (I * e * Q * phi / ((1 - mu : ℝ) : ℂ))).re =
      -Q * (-e * r * (starRingEnd ℂ phi * y).im) / ((1 - mu) * r) := by
  simp only [← mul_div_assoc, Complex.div_ofReal_re, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  field_simp [hr, hg]
  ring

/-- [internal] Conjugation preserves complex AC functions. -/
theorem ac_conj {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => starRingEnd ℂ (f x)) a b := by
  exact Complex.conjLIE.isometry.lipschitzWith.comp_absolutelyContinuousOnInterval hf

/-- [internal] Complex conjugation commutes with differentiation in a real
parameter. This is the real derivative rule, with no holomorphic premise. -/
theorem hasDerivAt_conj {f : ℝ → ℂ} {df : ℂ} {u : ℝ} (hf : HasDerivAt f df u) :
    HasDerivAt (fun x => starRingEnd ℂ (f x)) (starRingEnd ℂ df) u := by
  exact Complex.conjCLE.hasFDerivAt.comp_hasDerivAt u hf

/-- [node lem:ct-renormalized#complex-cubic-cancellation]
The cubic derivative in a real parameter includes the conjugate derivative
and both unconjugated contributions. This AC calculus rule is used on
incoming normalized scalar sections. -/
theorem hasDerivAt_cubic {f : ℝ → ℂ} {df : ℂ} {u : ℝ} (hf : HasDerivAt f df u) :
    HasDerivAt (fun x => (‖f x‖ : ℂ) ^ 2 * f x)
      (starRingEnd ℂ df * f u * f u + 2 * starRingEnd ℂ (f u) * f u * df) u := by
  have heq : (fun x => (‖f x‖ : ℂ) ^ 2 * f x) =
      (fun x => starRingEnd ℂ (f x) * f x * f x) := by
    funext x
    rw [← Complex.conj_mul']
  rw [heq]
  apply (((hasDerivAt_conj hf).mul hf).mul hf).congr_deriv
  simp only [Pi.mul_apply]
  ring

/-- [node lem:ct-renormalized#weighted-remainder-evaluation]
The incoming product rule for the renormalized density has exactly the
adopted weighted source. This is the landed `bv_j_trans_complex` algebra
with the derivative-free fixed-density source substituted; `w` is an
arbitrary value of that density, not an assumed derivative or conclusion. -/
theorem weighted_remainder_evaluation (e : ℝ) (S : Fields) (u v : ℝ) (w : ℂ)
    (hr : S.r u v ≠ 0) (hl : S.lam u v ≠ 0) (hn : S.nu u v ≠ 0)
    (hg : 1 - S.mu u v ≠ 0) :
    let y := S.theta u v / (S.lam u v : ℂ)
    let dy := (-(S.nu u v : ℂ) / S.r u v) *
      (S.xi u v / S.nu u v +
        ((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
          (1 - S.mu u v) * y + I * e * S.Q u v * S.phi u v / (1 - S.mu u v)) -
      I * e * S.A u v * y
    S.rUV u v * w + S.lam u v *
      (((-S.nu u v / ((1 - S.mu u v) * S.r u v) *
        (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) : ℝ) - I * e * S.A u v) * w +
        rawDensitySource e S u v) -
      ((2 * S.lam u v * S.rUV u v * S.r u v - S.lam u v ^ 2 * S.nu u v) /
        S.r u v ^ 2 : ℝ) * (‖y‖ : ℂ) ^ 2 * y -
      (S.lam u v ^ 2 / S.r u v : ℝ) *
        (starRingEnd ℂ dy * y * y + 2 * starRingEnd ℂ y * y * dy) =
      weightedJSource e S u v - I * e * S.A u v *
        (S.lam u v * w - (S.lam u v ^ 2 / S.r u v : ℝ) * (‖y‖ : ℂ) ^ 2 * y) := by
  set y := S.theta u v / (S.lam u v : ℂ) with hy
  set z := S.xi u v / (S.nu u v : ℂ) with hz
  have ht : S.theta u v = (S.lam u v : ℂ) * y := by
    dsimp [y]
    field_simp [Complex.ofReal_ne_zero.mpr hl]
  have hx : S.xi u v = (S.nu u v : ℂ) * z := by
    dsimp [z]
    field_simp [Complex.ofReal_ne_zero.mpr hn]
  have hqv : S.QV e u v = -e * S.r u v * S.lam u v *
      (starRingEnd ℂ (S.phi u v) * y).im := by
    rw [Fields.QV, ht]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have h := Local.bv_j_trans_complex (S.r u v) (S.lam u v) (S.nu u v)
    (S.mu u v) (S.Q u v) e y z (S.phi u v) w hr hg
  dsimp only at h ⊢
  unfold weightedJSource Local.curv Local.emSourceJ rawDensitySource
  change _ = _
  simp only [← hy, hqv]
  rw [ht, hx]
  simp only [map_mul, map_add, map_sub, map_div₀, map_neg, map_pow,
    Complex.conj_ofReal, Complex.conj_I, map_one]
  push_cast at h ⊢
  have hr' := Complex.ofReal_ne_zero.mpr hr
  have hl' := Complex.ofReal_ne_zero.mpr hl
  have hn' := Complex.ofReal_ne_zero.mpr hn
  have hg' : 1 - (S.mu u v : ℂ) ≠ 0 := by exact_mod_cast hg
  dsimp only [Fields.rUV]
  push_cast
  simp only [map_mul, map_add, map_sub, Complex.conj_ofReal, map_one,
    starRingEnd_self_apply, ← Complex.conj_mul'] at h ⊢
  linear_combination (norm := (field_simp [hr', hl', hn', hg']; ring))
    ((S.lam u v : ℂ) / (1 - S.mu u v)) * h

/-- [node lem:ct-renormalized#incoming-system]
Both normalized incoming scalar equations in the frozen AC class. The
charged commutator is the companion `incoming_commutator` test identity;
no classical mixed second derivative is asserted. -/
theorem incoming_system (hS : IsSolution e S D) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b < v) (hs : inSeg a b v ⊆ D) :
    (AbsolutelyContinuousOnInterval (fun u => S.a u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b),
        HasDerivAt (fun x => S.a x v)
          ((-(S.nu u v : ℂ) / S.r u v) *
            (((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
              (1 - S.mu u v) * (S.theta u v / S.lam u v) +
              I * e * S.Q u v * S.phi u v / (1 - S.mu u v)) -
            I * e * S.A u v * S.a u v) u) ∧
    (AbsolutelyContinuousOnInterval (fun u => S.theta u v / S.lam u v) a b ∧
    ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt
      (fun x => S.theta x v / S.lam x v)
      ((-(S.nu u v : ℂ) / S.r u v) *
        (S.xi u v / S.nu u v +
          ((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
            (1 - S.mu u v) * (S.theta u v / S.lam u v) +
          I * e * S.Q u v * S.phi u v / (1 - S.mu u v)) -
        I * e * S.A u v * (S.theta u v / S.lam u v)) u) :=
  ⟨Calculus.normalized_in_section hS hab hbv hs, incoming_ratio_section hS hab hbv hs⟩

/-- [node lem:ct-renormalized#incoming-system]
The charged commutator in weak AC test-section form. It is precisely the
landed potential-equation product identity, including the curvature sign
`2ie(-ν)λQ/((1-μ)r²)`. -/
theorem incoming_commutator (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    {f ψ : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hψ : AbsolutelyContinuousOnInterval ψ a b) :
    IntegralForm (fun v => I * e * S.A u v * f v * ψ v)
      (fun v => I * e * S.A u v * (deriv f v * ψ v + f v * deriv ψ v) -
        2 * I * e * (-S.nu u v) * S.lam u v * S.Q u v /
          ((1 - S.mu u v) * S.r u v ^ 2) * f v * ψ v) a b :=
  Calculus.main_gauge hS hua hab hs hf hψ

end EmcsfAcExtension.Global.Renormalized
