module

public import EmcsfAcExtension.Local.Construction.PicardCarrier
public import EmcsfAcExtension.Local.Defs.Recon

/-! # Oscillation bounds and the nondegenerate Picard domain

The explicit charge and mass estimates derive a Hawking gap from scalar
oscillation and the charged radius. All constants are displayed. These
conditional helpers are used to construct the invariant ball; they do not
close a graph node by themselves.
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- The exact rescaled-radius identity on the whole closed wedge. No positive
radius is assumed; both sides vanish on the axis. -/
theorem picard_recon_r_eq_radialAverage (ha : 0 ≤ a) (haL : a ≤ L) (z : PicardCarrier c a L (ℝ × ℂ))
    (p : PicardDomain c a L) :
    Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 = (p.1.2 - p.1.1) *
      picardRadialAverage ⟨fun q => (z.1.1 q).1, z.1.1.continuous.fst⟩ p := by
  have hI : (∫ t in (0 : ℝ)..1,
      picardCandidateLam ha haL z p.1.1 ((p.1.2 - p.1.1) * t + p.1.1)) =
      ∫ t in (0 : ℝ)..1, (z.1.1 (picardRadialPoint p t)).1 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simpa only [picardRadialPoint_of_mem p ht, add_comm, mul_comm] using
      picardCandidateLam_coe ha haL z (picardRadialPoint p t)
  have h := intervalIntegral.smul_integral_comp_mul_add
    (f := picardCandidateLam ha haL z p.1.1) (a := 0) (b := 1) (p.1.2 - p.1.1) p.1.1
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one] at h
  have he : p.1.2 - p.1.1 + p.1.1 = p.1.2 := by ring
  rw [he, hI] at h
  exact h.symm

namespace Recon

open MeasureTheory Complex

variable {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ} {u v ℓ H : ℝ}
private theorem integral_lam_r_pow_aux {lam : ℝ → ℝ → ℝ} {u v : ℝ}
    (hlam : Continuous (lam u)) (n : ℕ) :
    (∫ s in u..v, lam u s * r lam u s ^ n) = r lam u v ^ (n + 1) / (n + 1 : ℝ) := by
  have hr (t : ℝ) : HasDerivAt (r lam u) (lam u t) t :=
    (hlam.integral_hasStrictDerivAt u t).hasDerivAt
  have hc : Continuous (r lam u) :=
    continuous_iff_continuousAt.mpr (fun t => (hr t).continuousAt)
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hd (t : ℝ) : HasDerivAt (fun s => r lam u s ^ (n + 1) / (n + 1 : ℝ))
      (lam u t * r lam u t ^ n) t := by
    convert ((hr t).fun_pow (n + 1)).div_const (n + 1 : ℝ) using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((hlam.mul (hc.pow n)).intervalIntegrable u v)
  simpa [r_def] using hi

private theorem r_lower_aux (huv : u ≤ v) (hlam : Continuous (lam u))
    (hl : ∀ s ∈ Icc u v, ℓ ≤ lam u s) : ℓ * (v - u) ≤ r lam u v := by
  have h := intervalIntegral.integral_mono_on huv
    (intervalIntegrable_const (μ := volume)) (hlam.intervalIntegrable u v) hl
  simpa [r, mul_comm] using h
private theorem r_pos_aux (huv : u < v) (hℓ : 0 < ℓ) (hlam : Continuous (lam u))
    (hl : ∀ s ∈ Icc u v, ℓ ≤ lam u s) : 0 < r lam u v :=
  (mul_pos hℓ (sub_pos.mpr huv)).trans_le (r_lower_aux huv.le hlam hl)
private theorem weighted_norm_aux (huv : u ≤ v) (hlam : Continuous (lam u))
    (hl : ∀ s ∈ Icc u v, 0 ≤ lam u s) (f : ℝ → ℂ)
    (hf : ∀ s ∈ Icc u v, ‖f s‖ ≤ H) :
    ‖∫ s in u..v, (lam u s : ℂ) * f s‖ ≤ r lam u v * H := by
  have hi : IntervalIntegrable (fun s => lam u s * H) volume u v :=
    (hlam.mul continuous_const).intervalIntegrable u v
  have h := intervalIntegral.norm_integral_le_of_norm_le (f := fun s => (lam u s : ℂ) * f s) huv
    (Filter.Eventually.of_forall (fun s hs => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hl s ⟨hs.1.le, hs.2⟩)]
      exact mul_le_mul_of_nonneg_left (hf s ⟨hs.1.le, hs.2⟩) (hl s ⟨hs.1.le, hs.2⟩))) hi
  simpa only [intervalIntegral.integral_mul_const, r_def] using h
private theorem phi_norm_aux (huv : u < v) (hr : 0 < r lam u v)
    (hlam : Continuous (lam u)) (hl : ∀ s ∈ Icc u v, 0 ≤ lam u s)
    (hhb : ∀ s ∈ Icc u v, ‖hh u s‖ ≤ H) : ‖phi lam hh u v‖ ≤ H := by
  rw [phi_def, ite_eq_left huv, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  have h := weighted_norm_aux huv.le hlam hl (hh u) hhb
  calc
    (r lam u v)⁻¹ * ‖∫ s in u..v, (lam u s : ℂ) * hh u s‖ ≤
        (r lam u v)⁻¹ * (r lam u v * H) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hr.le)
    _ = H := by field_simp

private theorem ratio_norm_aux {ω : ℝ} (huv : u < v) (hr : 0 < r lam u v)
    (hlam : Continuous (lam u)) (hhh : Continuous (hh u))
    (hl : ∀ s ∈ Icc u v, 0 ≤ lam u s)
    (hosc : ∀ s ∈ Icc u v, ‖hh u v - hh u s‖ ≤ ω) :
    ‖ratio lam hh u v‖ ≤ ω := by
  have hC : Continuous (fun s => (lam u s : ℂ)) := Complex.continuous_ofReal.comp hlam
  have hiC : IntervalIntegrable (fun s => (lam u s : ℂ) * hh u v) volume u v :=
    (hC.mul continuous_const).intervalIntegrable u v
  have hiH : IntervalIntegrable (fun s => (lam u s : ℂ) * hh u s) volume u v :=
    (hC.mul hhh).intervalIntegrable u v
  have heq : (∫ s in u..v, (lam u s : ℂ) * (hh u v - hh u s)) =
      (r lam u v : ℂ) * hh u v - ∫ s in u..v, (lam u s : ℂ) * hh u s := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hiC hiH, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, r_def]
  have hrC : (r lam u v : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hratio : ratio lam hh u v = (r lam u v : ℂ)⁻¹ *
      ∫ s in u..v, (lam u s : ℂ) * (hh u v - hh u s) := by
    rw [ratio_def, phi_def, ite_eq_left huv, heq]
    field_simp
  rw [hratio, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have h := weighted_norm_aux huv.le hlam hl (fun s => hh u v - hh u s) hosc
  calc
    (r lam u v)⁻¹ * ‖∫ s in u..v, (lam u s : ℂ) * (hh u v - hh u s)‖ ≤
        (r lam u v)⁻¹ * (r lam u v * ω) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hr.le)
    _ = ω := by field_simp

private theorem charge_oscillation_aux {ω e : ℝ} (huv : u < v) (hℓ : 0 < ℓ)
    (hH : 0 ≤ H) (_hω : 0 ≤ ω) (hlam : Continuous (lam u)) (hhh : Continuous (hh u))
    (hl : ∀ s ∈ Icc u v, ℓ ≤ lam u s)
    (hhb : ∀ s ∈ Icc u v, ‖hh u s‖ ≤ H)
    (hosc : ∀ s ∈ Icc u v, ∀ t ∈ Icc u v, ‖hh u s - hh u t‖ ≤ ω) :
    |Q e lam hh u v| ≤ |e| * H * ω * r lam u v ^ 2 / 2 := by
  have hr (s : ℝ) : HasDerivAt (r lam u) (lam u s) s :=
    (hlam.integral_hasStrictDerivAt u s).hasDerivAt
  have hc : Continuous (r lam u) :=
    continuous_iff_continuousAt.mpr (fun s => (hr s).continuousAt)
  have hb : IntervalIntegrable (fun s => (r lam u s * lam u s) * (H * ω)) volume u v :=
    ((hc.mul hlam).mul continuous_const).intervalIntegrable u v
  have hint := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun s => r lam u s * lam u s * (starRingEnd ℂ (phi lam hh u s) * hh u s).im)
    huv.le (Filter.Eventually.of_forall (fun s hs => by
      have hs' : s ∈ Icc u v := ⟨hs.1.le, hs.2⟩
      have hls : ∀ t ∈ Icc u s, 0 ≤ lam u t :=
        fun t ht => hℓ.le.trans (hl t ⟨ht.1, ht.2.trans hs.2⟩)
      have hrs : 0 < r lam u s := r_pos_aux hs.1 hℓ hlam
        (fun t ht => hl t ⟨ht.1, ht.2.trans hs.2⟩)
      have hp := phi_norm_aux hs.1 hrs hlam hls
        (fun t ht => hhb t ⟨ht.1, ht.2.trans hs.2⟩)
      have hf := ratio_norm_aux hs.1 hrs hlam hhh hls
        (fun t ht => hosc s hs' t ⟨ht.1, ht.2.trans hs.2⟩)
      have him : (starRingEnd ℂ (phi lam hh u s) * hh u s).im =
          (starRingEnd ℂ (phi lam hh u s) * ratio lam hh u s).im := by
        simp [ratio_def, mul_sub, Complex.conj_mul', ← Complex.ofReal_pow]
      have hi : |(starRingEnd ℂ (phi lam hh u s) * hh u s).im| ≤ H * ω := by
        rw [him]
        calc
          _ ≤ ‖starRingEnd ℂ (phi lam hh u s) * ratio lam hh u s‖ := Complex.abs_im_le_norm _
          _ = ‖phi lam hh u s‖ * ‖ratio lam hh u s‖ := by rw [norm_mul, Complex.norm_conj]
          _ ≤ H * ω := mul_le_mul hp hf (norm_nonneg _) hH
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hrs,
        abs_of_nonneg (hls s ⟨hs.1.le, le_rfl⟩)]
      exact mul_le_mul_of_nonneg_left hi (mul_nonneg hrs.le (hls s ⟨hs.1.le, le_rfl⟩)))) hb
  have hpow := integral_lam_r_pow_aux (u := u) (v := v) hlam 1
  norm_num at hpow
  have hInt : (∫ s in u..v, (r lam u s * lam u s) * (H * ω)) =
      r lam u v ^ 2 / 2 * (H * ω) := by
    rw [intervalIntegral.integral_mul_const]
    have heq : (fun s => r lam u s * lam u s) = (fun s => lam u s * r lam u s ^ 1) := by
      funext s
      ring
    rw [heq]
    simpa using congrArg (fun x : ℝ => x * (H * ω)) hpow
  rw [hInt, Real.norm_eq_abs] at hint
  calc
    |Q e lam hh u v| = |e| * |∫ s in u..v,
        r lam u s * lam u s * (starRingEnd ℂ (phi lam hh u s) * hh u s).im| := by
      simp [q_def]
    _ ≤ |e| * (r lam u v ^ 2 / 2 * (H * ω)) := mul_le_mul_of_nonneg_left hint (abs_nonneg e)
    _ = |e| * H * ω * r lam u v ^ 2 / 2 := by ring

/-- The quantitative mass bound used to derive the Picard ball's Hawking gap.
All constants are displayed; the bound is uniform in the candidates and section
endpoints, and requires no bound on higher derivatives. This conditional helper
is the estimate (E1) of internal project record, not closure of the invariant-ball node. -/
theorem picard_mu_le_of_oscillation {ω e : ℝ} (huv : u < v) (hℓ : 0 < ℓ)
    (hH : 0 ≤ H) (hω : 0 ≤ ω) (hlam : Continuous (lam u)) (hhh : Continuous (hh u))
    (hl : ∀ s ∈ Icc u v, ℓ ≤ lam u s)
    (hhb : ∀ s ∈ Icc u v, ‖hh u s‖ ≤ H)
    (hosc : ∀ s ∈ Icc u v, ∀ t ∈ Icc u v, ‖hh u s - hh u t‖ ≤ ω) :
    mu e lam hh u v ≤ ω ^ 2 * (1 + e ^ 2 * H ^ 2 * r lam u v ^ 2 / 12) := by
  let C : ℝ := |e| * H * ω / 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hr (s : ℝ) : HasDerivAt (r lam u) (lam u s) s :=
    (hlam.integral_hasStrictDerivAt u s).hasDerivAt
  have hc : Continuous (r lam u) :=
    continuous_iff_continuousAt.mpr (fun s => (hr s).continuousAt)
  have hb : IntervalIntegrable (fun s => lam u s * (ω ^ 2 + C ^ 2 * r lam u s ^ 2))
      volume u v := (hlam.mul (continuous_const.add
        (continuous_const.mul (hc.pow 2)))).intervalIntegrable u v
  have hint := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun s => lam u s * (‖ratio lam hh u s‖ ^ 2 + Q e lam hh u s ^ 2 / r lam u s ^ 2) *
      Real.exp (-∫ t in s..v, lam u t * ‖ratio lam hh u t‖ ^ 2 / r lam u t))
    huv.le (Filter.Eventually.of_forall (fun s hs => by
      have hs' : s ∈ Icc u v := ⟨hs.1.le, hs.2⟩
      have hlower : ∀ t ∈ Icc u s, ℓ ≤ lam u t :=
        fun t ht => hl t ⟨ht.1, ht.2.trans hs.2⟩
      have hls : ∀ t ∈ Icc u s, 0 ≤ lam u t :=
        fun t ht => hℓ.le.trans (hlower t ht)
      have hrs : 0 < r lam u s := r_pos_aux hs.1 hℓ hlam hlower
      have hlams : 0 ≤ lam u s := hℓ.le.trans (hl s hs')
      have hf := ratio_norm_aux hs.1 hrs hlam hhh hls
        (fun t ht => hosc s hs' t ⟨ht.1, ht.2.trans hs.2⟩)
      have hf2 : ‖ratio lam hh u s‖ ^ 2 ≤ ω ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hω).mpr hf
      have hq := charge_oscillation_aux (e := e) hs.1 hℓ hH hω hlam hhh hlower
        (fun t ht => hhb t ⟨ht.1, ht.2.trans hs.2⟩)
        (fun t ht x hx => hosc t ⟨ht.1, ht.2.trans hs.2⟩ x ⟨hx.1, hx.2.trans hs.2⟩)
      have hqr : |Q e lam hh u s| / r lam u s ≤ C * r lam u s := by
        apply (div_le_iff₀ hrs).mpr
        convert hq using 1
        dsimp [C]
        ring
      have hq2 : Q e lam hh u s ^ 2 / r lam u s ^ 2 ≤ C ^ 2 * r lam u s ^ 2 := by
        have h := (sq_le_sq₀ (div_nonneg (abs_nonneg _) hrs.le)
          (mul_nonneg hC hrs.le)).mpr hqr
        simpa only [div_pow, sq_abs, mul_pow] using h
      have hExp : Real.exp (-∫ t in s..v,
          lam u t * ‖ratio lam hh u t‖ ^ 2 / r lam u t) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        apply neg_nonpos.mpr
        apply intervalIntegral.integral_nonneg hs.2
        intro t ht
        have hut : u ≤ t := hs.1.le.trans ht.1
        have hrt : 0 ≤ r lam u t :=
          (mul_nonneg hℓ.le (sub_nonneg.mpr hut)).trans
            (r_lower_aux hut hlam (fun x hx => hl x ⟨hx.1, hx.2.trans ht.2⟩))
        exact div_nonneg (mul_nonneg (hℓ.le.trans (hl t ⟨hut, ht.2⟩))
          (sq_nonneg _)) hrt
      have hbase : 0 ≤ lam u s * (‖ratio lam hh u s‖ ^ 2 +
          Q e lam hh u s ^ 2 / r lam u s ^ 2) :=
        mul_nonneg hlams (add_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) (sq_nonneg _)))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hbase (Real.exp_pos _).le)]
      calc
        _ ≤ lam u s * (‖ratio lam hh u s‖ ^ 2 + Q e lam hh u s ^ 2 / r lam u s ^ 2) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hExp hbase
        _ ≤ lam u s * (ω ^ 2 + C ^ 2 * r lam u s ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hf2 hq2) hlams)) hb
  have hpow := integral_lam_r_pow_aux (u := u) (v := v) hlam 2
  norm_num at hpow
  have hInt : (∫ s in u..v, lam u s * (ω ^ 2 + C ^ 2 * r lam u s ^ 2)) =
      r lam u v * ω ^ 2 + (r lam u v ^ 3 / 3) * C ^ 2 := by
    have heq : (fun s => lam u s * (ω ^ 2 + C ^ 2 * r lam u s ^ 2)) =
        (fun s => lam u s * ω ^ 2 + (lam u s * r lam u s ^ 2) * C ^ 2) := by
      funext s
      ring
    have hi₁ : IntervalIntegrable (fun s => lam u s * ω ^ 2) volume u v :=
      (hlam.mul continuous_const).intervalIntegrable u v
    have hi₂ : IntervalIntegrable (fun s => (lam u s * r lam u s ^ 2) * C ^ 2) volume u v :=
      ((hlam.mul (hc.pow 2)).mul continuous_const).intervalIntegrable u v
    rw [heq, intervalIntegral.integral_add hi₁ hi₂,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, hpow, ← r_def]
  rw [hInt, Real.norm_eq_abs] at hint
  have hm : m e lam hh u v ≤ (1 / 2) *
      (r lam u v * ω ^ 2 + (r lam u v ^ 3 / 3) * C ^ 2) := by
    rw [m_def]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hint) (by norm_num)
  rw [mu_def]
  apply (div_le_iff₀ (r_pos_aux huv hℓ hlam hl)).mpr
  have h := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1
  simp only [C, mul_pow, div_pow, sq_abs]
  ring

/-- A scalar oscillation at most `1/8` and charged radius at most one imply
`1-μ ≥ 3/4`. The numerical thresholds and gap are universal. This derives
nondegeneracy from candidate bounds rather than adding it as a hypothesis. -/
theorem picard_gap_of_oscillation {ω e : ℝ} (huv : u < v) (hℓ : 0 < ℓ)
    (hH : 0 ≤ H) (hω : 0 ≤ ω) (hsmall : ω ≤ 1 / 8)
    (hlam : Continuous (lam u)) (hhh : Continuous (hh u))
    (hl : ∀ s ∈ Icc u v, ℓ ≤ lam u s)
    (hhb : ∀ s ∈ Icc u v, ‖hh u s‖ ≤ H)
    (hosc : ∀ s ∈ Icc u v, ∀ t ∈ Icc u v, ‖hh u s - hh u t‖ ≤ ω)
    (hscale : |e| * H * r lam u v ≤ 1) : 3 / 4 ≤ 1 - mu e lam hh u v := by
  have hm := picard_mu_le_of_oscillation (e := e) huv hℓ hH hω hlam hhh hl hhb hosc
  have hrpos := r_pos_aux huv hℓ hlam hl
  have hnonneg : 0 ≤ |e| * H * r lam u v := by positivity
  have hsquare : e ^ 2 * H ^ 2 * r lam u v ^ 2 ≤ 1 := by
    have hs := (sq_le_sq₀ hnonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr hscale
    simpa only [mul_pow, sq_abs, one_pow] using hs
  have hωsquare := (sq_le_sq₀ hω (by norm_num : (0 : ℝ) ≤ 1 / 8)).mpr hsmall
  have hfactor : 1 + e ^ 2 * H ^ 2 * r lam u v ^ 2 / 12 ≤ 1 + 1 / 12 := by
    linarith
  have hb := (mul_le_mul_of_nonneg_left hfactor (sq_nonneg ω)).trans
    (mul_le_mul_of_nonneg_right hωsquare (by norm_num : (0 : ℝ) ≤ 1 + 1 / 12))
  norm_num at hb
  linarith

/-- Write the scalar remainder as the radial average of its endpoint
increments. This local helper uses no incoming equation or Hawking-gap bound. -/
theorem picard_ratio_eq_phi_increment_aux {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    {u v : ℝ} (huv : u < v) (hr : 0 < r lam u v)
    (hlam : Continuous (lam u)) (hhh : Continuous (hh u)) :
    ratio lam hh u v = phi lam (fun uu s => hh uu v - hh uu s) u v := by
  have hC : Continuous (fun s => (lam u s : ℂ)) := Complex.continuous_ofReal.comp hlam
  have hiC : IntervalIntegrable (fun s => (lam u s : ℂ) * hh u v) volume u v :=
    (hC.mul continuous_const).intervalIntegrable u v
  have hiH : IntervalIntegrable (fun s => (lam u s : ℂ) * hh u s) volume u v :=
    (hC.mul hhh).intervalIntegrable u v
  have heq : (∫ s in u..v, (lam u s : ℂ) * (hh u v - hh u s)) =
      (r lam u v : ℂ) * hh u v - ∫ s in u..v, (lam u s : ℂ) * hh u s := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hiC hiH, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_ofReal, r_def]
  have hrC : (r lam u v : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [ratio_def, phi_def, phi_def, ite_eq_left huv, ite_eq_left huv, heq]
  field_simp

/-- The exact outgoing scalar derivative away from the axis, by FTC and the
quotient rule. This local reconstruction helper is independent of incoming
field equations and of the Hawking gap. -/
theorem phi_hasDerivAt_of_r_pos_aux {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ} {u v : ℝ}
    (huv : u < v) (hr : 0 < r lam u v) (hlam : Continuous (lam u))
    (hhh : Continuous (hh u)) :
    HasDerivAt (phi lam hh u) ((lam u v / r lam u v : ℝ) * ratio lam hh u v) v := by
  have hc : Continuous (fun s => (lam u s : ℂ) * hh u s) :=
    (Complex.continuous_ofReal.comp hlam).mul hhh
  have hN := (hc.integral_hasStrictDerivAt u v).hasDerivAt
  have hR : HasDerivAt (fun t => (r lam u t : ℂ)) (lam u v : ℂ) v :=
    (hlam.integral_hasStrictDerivAt u v).hasDerivAt.ofReal_comp
  have hrC : (r lam u v : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hQ := hN.div hR hrC
  have heq : phi lam hh u =ᶠ[𝓝 v]
      (fun t => (∫ s in u..t, (lam u s : ℂ) * hh u s) / (r lam u t : ℂ)) := by
    filter_upwards [Ioi_mem_nhds huv] with t ht
    rw [phi_def, ite_eq_left (show u < t from ht)]
    ring
  have h := hQ.congr_of_eventuallyEq heq
  convert h using 1
  rw [ratio_def, phi_def, ite_eq_left huv]
  push_cast
  field_simp

end Recon

end EmcsfAcExtension.Local
