module

public import EmcsfAcExtension.Global.Defs.Original
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.RelativeCharge

/-! # Small scalar amplitude on late original rows

The outgoing comparison of charged_SF_new_version.tex:L1048–L1057 uses only the upper
bound for `λ / (1 - μ)`, with no interior gap. The terminal logarithmic
bound and radius collapse then give the uniform conclusion at L1058–L1066.
The `_of_terminal` interfaces leave the terminal packet's outputs explicit;
its unconditional node wrappers are assembled after that packet lands.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global

private theorem integral_cauchy_schwarz {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    (∫ x in a..b, f x * g x) ^ 2 ≤
      (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
  have iff : IntervalIntegrable (fun x => f x ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc hab
  have ifg : IntervalIntegrable (fun x => f x * g x) volume a b :=
    (hf.mul hg).intervalIntegrable_of_Icc hab
  have igg : IntervalIntegrable (fun x => g x ^ 2) volume a b :=
    (hg.pow 2).intervalIntegrable_of_Icc hab
  have hp (t : ℝ) : 0 ≤ (∫ x in a..b, g x ^ 2) * (t * t) +
      (2 * ∫ x in a..b, f x * g x) * t + ∫ x in a..b, f x ^ 2 := by
    have h := intervalIntegral.integral_nonneg (μ := volume) hab
      (fun x _ => sq_nonneg (f x + t * g x))
    have he : (∫ x in a..b, (f x + t * g x) ^ 2) =
        (∫ x in a..b, f x ^ 2) + 2 * t * (∫ x in a..b, f x * g x) +
          t ^ 2 * (∫ x in a..b, g x ^ 2) := by
      calc
        _ = ∫ x in a..b, (f x ^ 2 + (2 * t) * (f x * g x)) + t ^ 2 * g x ^ 2 :=
          intervalIntegral.integral_congr (fun x _ => by ring)
        _ = _ := by
          rw [intervalIntegral.integral_add (iff.add (ifg.const_mul (2 * t)))
            (igg.const_mul (t ^ 2)), intervalIntegral.integral_add iff (ifg.const_mul (2 * t))]
          simp only [intervalIntegral.integral_const_mul]
    rw [he] at h
    nlinarith only [h]
  have hd := discrim_le_zero hp
  dsimp [discrim] at hd
  nlinarith only [hd]

private theorem radius_le_on_row {ui e : ℝ} {S : Fields} (h : OriginalData ui e S)
    {u a b : ℝ} (hu : u ∈ Ico ui 0) (hua : u < a) (hab : a ≤ b) (hb : b ≤ 0) :
    S.r u a ≤ S.r u b := by
  have hs : outSeg u a b ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨rfl, hy⟩
    exact ⟨hu.1, hu.2, hua.le.trans hy.1, hy.2.trans hb⟩
  have hf := (h.solution.eq_out u a b hua hab hs).1
  have hn := intervalIntegral.integral_nonneg (μ := volume) hab
    (fun x hx => (h.solution.lam_pos (u, x) (hs ⟨rfl, hx⟩)).le)
  rw [← hf.2] at hn
  exact sub_nonneg.mp hn

namespace Amplitude

/-- [internal]
Consumes the global optical upper bound of
`prop:charged-terminal-equivalence#lambda-gap-upper-bound` to prove the full
comparison in `lem:charged-rphi-small#outgoing-scalar-comparison`
(charged_SF_new_version.tex:L1048–L1057). The constant `C` is the supplied bound for this
solution, uniform in both labels; no interior gap or lower expansion bound
is assumed. Both proper integrals and both inequalities are retained. -/
theorem outgoing_scalar_comparison_of_terminal (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) (C : ℝ) (hC : 0 < C)
    (hopt : ∀ p ∈ origDomain ui, S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ C)
    (u v : ℝ) (hu : u ∈ Ico ui 0) (hv : v ∈ Ioc u 0) :
    let E := fun s => (1 - S.mu u s) * ‖S.theta u s‖ ^ 2 / S.lam u s
    let W := fun s => S.lam u s / ((1 - S.mu u s) * S.r u s ^ 2)
    IntervalIntegrable E volume v 0 ∧ IntervalIntegrable W volume v 0 ∧
      ‖S.phi u v - S.phi u 0‖ ^ 2 ≤ (∫ s in v..0, E s) * (∫ s in v..0, W s) ∧
      (∫ s in v..0, E s) * (∫ s in v..0, W s) ≤
        2 * C * S.m u 0 * (-v) / S.r u v ^ 2 := by
  dsimp only
  let E := fun s => (1 - S.mu u s) * ‖S.theta u s‖ ^ 2 / S.lam u s
  let W := fun s => S.lam u s / ((1 - S.mu u s) * S.r u s ^ 2)
  have hs : outSeg u v 0 ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨rfl, hy⟩
    exact ⟨hu.1, hu.2, hv.1.le.trans hy.1, hy.2⟩
  have hp (s : ℝ) (hs' : s ∈ Icc v 0) : (u, s) ∈ origDomain ui := hs ⟨rfl, hs'⟩
  have hr (s : ℝ) (hs' : s ∈ Icc v 0) : 0 < S.r u s :=
    h.solution.r_pos (u, s) (hp s hs') (hv.1.trans_le hs'.1)
  have hl (s : ℝ) (hs' : s ∈ Icc v 0) : 0 < S.lam u s :=
    h.solution.lam_pos (u, s) (hp s hs')
  have hg (s : ℝ) (hs' : s ∈ Icc v 0) : 0 < 1 - S.mu u s :=
    h.solution.one_sub_mu_pos (u, s) (hp s hs')
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have ct := Calculus.continuousOn_out_section h.solution.cont_theta hs
  have cg : ContinuousOn (fun s => 1 - S.mu u s) (Icc v 0) := continuousOn_const.sub
    ((Local.continuousOn_mu_out h.solution hu.2
      ((outSeg_axis_subset_origDomain_iff hu.2.le).2 ⟨hu.1, hu.2, le_rfl⟩)).mono
        (Icc_subset_Icc hv.1.le le_rfl))
  have cE : ContinuousOn E (Icc v 0) :=
    (cg.mul (ct.norm.pow 2)).div cl (fun s hs' => (hl s hs').ne')
  have cW : ContinuousOn W (Icc v 0) :=
    cl.div (cg.mul (cr.pow 2)) (fun s hs' =>
      mul_ne_zero (hg s hs').ne' (pow_ne_zero _ (hr s hs').ne'))
  have iE := cE.intervalIntegrable_of_Icc hv.2 (μ := volume)
  have iW := cW.intervalIntegrable_of_Icc hv.2 (μ := volume)
  have nE (s : ℝ) (hs' : s ∈ Icc v 0) : 0 ≤ E s :=
    div_nonneg (mul_nonneg (hg s hs').le (sq_nonneg _)) (hl s hs').le
  have nW (s : ℝ) (hs' : s ∈ Icc v 0) : 0 ≤ W s :=
    div_nonneg (hl s hs').le (mul_nonneg (hg s hs').le (sq_nonneg _))
  have iEn : 0 ≤ ∫ s in v..0, E s := intervalIntegral.integral_nonneg hv.2 nE
  have iWn : 0 ≤ ∫ s in v..0, W s := intervalIntegral.integral_nonneg hv.2 nW
  let w := fun s => Real.sqrt (S.lam u s / (1 - S.mu u s))
  have cw : ContinuousOn w (Icc v 0) := (cl.div cg (fun s hs' => (hg s hs').ne')).sqrt
  have wp (s : ℝ) (hs' : s ∈ Icc v 0) : 0 < w s :=
    Real.sqrt_pos.2 (div_pos (hl s hs') (hg s hs'))
  have wsq (s : ℝ) (hs' : s ∈ Icc v 0) : w s ^ 2 = S.lam u s / (1 - S.mu u s) :=
    Real.sq_sqrt (div_nonneg (hl s hs').le (hg s hs').le)
  have cf := ct.norm.div cw (fun s hs' => (wp s hs').ne')
  have cd := cw.div cr (fun s hs' => (hr s hs').ne')
  have heqf (s : ℝ) (hs' : s ∈ Icc v 0) : (‖S.theta u s‖ / w s) ^ 2 = E s := by
    rw [div_pow, wsq s hs']
    dsimp [E]
    field_simp [(hl s hs').ne', (hg s hs').ne']
  have heqg (s : ℝ) (hs' : s ∈ Icc v 0) : (w s / S.r u s) ^ 2 = W s := by
    rw [div_pow, wsq s hs', div_div]
  have heqfg (s : ℝ) (hs' : s ∈ Icc v 0) :
      (‖S.theta u s‖ / w s) * (w s / S.r u s) = ‖S.phiV u s‖ := by
    simp only [Fields.phiV, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hr s hs')]
    field_simp [(wp s hs').ne']
  have hcs := integral_cauchy_schwarz hv.2 cf cd
  simp only [Pi.div_apply] at hcs
  rw [intervalIntegral.integral_congr (fun s hs' => heqf s ((uIcc_of_le hv.2) ▸ hs')),
    intervalIntegral.integral_congr (fun s hs' => heqg s ((uIcc_of_le hv.2) ▸ hs')),
    intervalIntegral.integral_congr (fun s hs' => heqfg s ((uIcc_of_le hv.2) ▸ hs'))] at hcs
  have forms := h.solution.eq_out u v 0 hv.1 hv.2 hs
  have hnorm : ‖S.phi u v - S.phi u 0‖ ≤ ∫ s in v..0, ‖S.phiV u s‖ := by
    rw [norm_sub_rev, forms.2.2.2.2.2.1.2]
    exact intervalIntegral.norm_integral_le_integral_norm hv.2
  have hfirst : ‖S.phi u v - S.phi u 0‖ ^ 2 ≤
      (∫ s in v..0, E s) * (∫ s in v..0, W s) :=
    (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs
  have hmass : (∫ s in v..0, E s) ≤ 2 * S.m u 0 := by
    have hle := intervalIntegral.integral_mono_on hv.2 iE (forms.2.2.1.1.const_mul 2)
      (fun s hs' => show E s ≤ 2 * S.mV u s from by
        have he : 2 * S.mV u s = E s + S.Q u s ^ 2 * S.lam u s / S.r u s ^ 2 := by
          dsimp [Fields.mV, E]
          field_simp [(hl s hs').ne', (hr s hs').ne']
        rw [he]
        exact le_add_of_nonneg_right (div_nonneg
          (mul_nonneg (sq_nonneg _) (hl s hs').le) (sq_nonneg _)))
    rw [intervalIntegral.integral_const_mul, ← forms.2.2.1.2] at hle
    have hm : 0 ≤ S.m u v := by
      have := (h.mu (u, v) (hp v ⟨le_rfl, hv.2⟩)).1
      dsimp [Fields.mu] at this
      have := (le_div_iff₀ (hr v ⟨le_rfl, hv.2⟩)).mp this
      linarith
    linarith
  have hweight : (∫ s in v..0, W s) ≤ C * (-v) / S.r u v ^ 2 := by
    have hle := intervalIntegral.integral_mono_on hv.2 iW
      (intervalIntegrable_const (c := C / S.r u v ^ 2)) (fun s hs' => by
        have hrs := radius_le_on_row h hu hv.1 hs'.1 hs'.2
        have hsq := pow_le_pow_left₀ (hr v ⟨le_rfl, hv.2⟩).le hrs 2
        calc
          W s = (S.lam u s / (1 - S.mu u s)) / S.r u s ^ 2 := by dsimp [W]; rw [div_div]
          _ ≤ C / S.r u s ^ 2 := div_le_div_of_nonneg_right (hopt (u, s) (hp s hs')) (sq_nonneg _)
          _ ≤ C / S.r u v ^ 2 := div_le_div_of_nonneg_left hC.le
            (sq_pos_of_pos (hr v ⟨le_rfl, hv.2⟩)) hsq)
    simpa [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv, mul_comm,
      mul_left_comm, mul_assoc] using hle
  refine ⟨iE, iW, hfirst, ?_⟩
  calc
    _ ≤ (2 * S.m u 0) * (C * (-v) / S.r u v ^ 2) :=
      mul_le_mul hmass hweight iWn (iEn.trans hmass)
    _ = _ := by ring

private theorem terminal_mass_bounds {ui e : ℝ} {S : Fields} (h : OriginalData ui e S)
    {u : ℝ} (hu : u ∈ Ico ui 0) : 0 ≤ S.m u 0 ∧ S.m u 0 ≤ S.r u 0 / 2 := by
  have hp : (u, 0) ∈ origDomain ui := ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have hr := h.solution.r_pos (u, 0) hp hu.2
  have hm := h.mu (u, 0) hp
  dsimp [Fields.mu] at hm
  have hlo := (le_div_iff₀ hr).mp hm.1
  have hhi := (div_lt_iff₀ hr).mp hm.2
  constructor <;> linarith

/-- [internal]
The quantitative row estimate in `lem:charged-rphi-small#row-amplitude-limit`,
charged_SF_new_version.tex:L1058–L1061, consuming only the terminal packet's global optical
upper bound. The supplied `C` is uniform in the row and point. The axis is
included using its frozen zero-radius trace. -/
theorem row_amplitude_bound_of_terminal (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) (C : ℝ) (hC : 0 < C)
    (hopt : ∀ p ∈ origDomain ui, S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ C)
    (p : ℝ × ℝ) (hp : p ∈ origDomain ui) :
    S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤
      S.r p.1 0 * ‖S.phi p.1 0‖ + Real.sqrt (2 * C * S.m p.1 0 * (-p.1)) := by
  rcases p with ⟨u, v⟩
  change ui ≤ u ∧ u < 0 ∧ u ≤ v ∧ v ≤ 0 at hp
  change S.r u v * ‖S.phi u v‖ ≤
    S.r u 0 * ‖S.phi u 0‖ + Real.sqrt (2 * C * S.m u 0 * (-u))
  have hu : u ∈ Ico ui 0 := ⟨hp.1, hp.2.1⟩
  have hm := (terminal_mass_bounds h hu).1
  rcases hp.2.2.1.eq_or_lt with rfl | huv
  · rw [(h.solution.axis u hp).1, zero_mul]
    exact add_nonneg (mul_nonneg (h.solution.r_pos (u, 0)
      ⟨hu.1, hu.2, hu.2.le, le_rfl⟩ hu.2).le (norm_nonneg _)) (Real.sqrt_nonneg _)
  · have hr := h.solution.r_pos (u, v) hp huv
    have hcomp := (outgoing_scalar_comparison_of_terminal ui e S h C hC hopt
      u v hu ⟨huv, hp.2.2.2⟩).2.2
    have hsq := (le_div_iff₀ (sq_pos_of_pos hr)).1 (hcomp.1.trans hcomp.2)
    have hlen : 2 * C * S.m u 0 * (-v) ≤ 2 * C * S.m u 0 * (-u) :=
      mul_le_mul_of_nonneg_left (neg_le_neg huv.le) (by positivity)
    have hdiff : S.r u v * ‖S.phi u v - S.phi u 0‖ ≤
        Real.sqrt (2 * C * S.m u 0 * (-u)) := by
      apply Real.le_sqrt_of_sq_le
      calc
        _ = ‖S.phi u v - S.phi u 0‖ ^ 2 * S.r u v ^ 2 := by ring
        _ ≤ _ := hsq.trans hlen
    have hnorm : ‖S.phi u v‖ ≤ ‖S.phi u 0‖ + ‖S.phi u v - S.phi u 0‖ := by
      simpa only [add_sub_cancel] using norm_add_le (S.phi u 0) (S.phi u v - S.phi u 0)
    calc
      _ ≤ S.r u v * (‖S.phi u 0‖ + ‖S.phi u v - S.phi u 0‖) :=
        mul_le_mul_of_nonneg_left hnorm hr.le
      _ ≤ _ := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right
          (radius_le_on_row h hu huv hp.2.2.2 le_rfl) (norm_nonneg _)) hdiff

private theorem radius_sqrt_log_tendsto {R : ℝ → ℝ} {Ri : ℝ} (hRi : Ri ≠ 0)
    (hR : Tendsto R (𝓝[<] 0) (𝓝 0)) (hp : ∀ᶠ u in 𝓝[<] 0, 0 < R u) :
    Tendsto (fun u => R u * Real.sqrt (Real.log (Ri / R u))) (𝓝[<] 0) (𝓝 0) := by
  have hlog : Tendsto (fun u => R u * Real.log (R u)) (𝓝[<] 0) (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      Real.continuous_mul_log.continuousAt.tendsto.comp hR
  have ht := ((hR.pow 2).mul_const (Real.log Ri)).sub (hR.mul hlog)
  have ht' : Tendsto (fun u => Real.sqrt (R u ^ 2 * Real.log Ri -
      R u * (R u * Real.log (R u)))) (𝓝[<] 0) (𝓝 0) := by
    simpa using ht.sqrt
  apply ht'.congr'
  filter_upwards [hp] with u hu
  calc
    _ = Real.sqrt (R u ^ 2 * Real.log (Ri / R u)) := by
      congr 1
      rw [Real.log_div hRi hu.ne']
      ring
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg (R u)), Real.sqrt_sq hu.le]

/-- [internal]
The row estimate and its vanishing majorant in
`lem:charged-rphi-small#row-amplitude-limit`, charged_SF_new_version.tex:L1058–L1064.
Consumes radius collapse and the exact terminal logarithmic bound from
`Terminal.hypotheses`, plus the global optical upper bound. `C` and `K` may
depend on the original solution and coupling and are uniform in all labels. -/
theorem row_amplitude_limit_of_terminal (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) (C K : ℝ) (hC : 0 < C)
    (hopt : ∀ p ∈ origDomain ui, S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ C)
    (hR : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hlog : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      K * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    (∀ p ∈ origDomain ui, S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤
      S.r p.1 0 * ‖S.phi p.1 0‖ + Real.sqrt (2 * C * S.m p.1 0 * (-p.1))) ∧
    Tendsto (fun u => S.r u 0 * ‖S.phi u 0‖ + Real.sqrt (2 * C * S.m u 0 * (-u)))
      (𝓝[<] 0) (𝓝 0) := by
  have hi : ∀ᶠ u in 𝓝[<] 0, u ∈ Ico ui 0 := Ico_mem_nhdsLT h.ui_neg
  have hp : ∀ᶠ u in 𝓝[<] 0, 0 < S.r u 0 := hi.mono fun u hu =>
    h.solution.r_pos (u, 0) ⟨hu.1, hu.2, hu.2.le, le_rfl⟩ hu.2
  have hRi := h.solution.r_pos (ui, 0)
    (show (ui, 0) ∈ origDomain ui from ⟨le_rfl, h.ui_neg, h.ui_neg.le, le_rfl⟩) h.ui_neg
  have hscale := radius_sqrt_log_tendsto hRi.ne' hR hp
  have hmajor : Tendsto (fun u => S.r u 0 *
      (K * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))) (𝓝[<] 0) (𝓝 0) := by
    convert (hR.add hscale).mul_const K using 1
    · ext u; ring
    · simp
  have hscalar : Tendsto (fun u => S.r u 0 * ‖S.phi u 0‖) (𝓝[<] 0) (𝓝 0) := by
    apply squeeze_zero' (hp.mono fun u hu => mul_nonneg hu.le (norm_nonneg _))
      ?_ hmajor
    filter_upwards [hi, hp] with u hu hr
    exact mul_le_mul_of_nonneg_left (hlog u hu) hr.le
  have hmass : Tendsto (fun u => S.m u 0) (𝓝[<] 0) (𝓝 0) := by
    apply squeeze_zero' (hi.mono fun u hu => (terminal_mass_bounds h hu).1)
      (hi.mono fun u hu => (terminal_mass_bounds h hu).2)
    simpa using hR.div_const 2
  have ht : Tendsto (fun u : ℝ => u) (𝓝[<] 0) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hroot : Tendsto (fun u => Real.sqrt (2 * C * S.m u 0 * (-u)))
      (𝓝[<] 0) (𝓝 0) := by
    simpa using ((hmass.const_mul (2 * C)).mul ht.neg).sqrt
  exact ⟨row_amplitude_bound_of_terminal ui e S h C hC hopt, by simpa using hscalar.add hroot⟩

end Amplitude

namespace Terminal

/-- [internal]
The exact `Terminal.scalar_amplitude` interface of internal project record, conditional
on the terminal packet's §3 `hypotheses` output and its global optical upper
bound. It proves `lem:charged-rphi-small` on every late row, including the
existing axis, with no interior gap. All solution-dependent witnesses are
extracted after the original data and the signed terminal premise. -/
theorem scalar_amplitude_of_terminal (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S)
    (hterminal :
      (SignedTerminalBound ui S ↔ PositiveTerminalFinite ui S) ∧
      (SignedTerminalBound ui S →
        ∃ δ K lam₀ : ℝ, 0 < δ ∧ 0 < K ∧ 0 < lam₀ ∧
        (∀ u ∈ Ico ui 0, δ ≤ 1 - S.mu u 0) ∧
        (∫⁻ u in Ico ui 0,
          ENNReal.ofReal ((-S.nu u 0) * ‖S.xi u 0 / (S.nu u 0 : ℂ)‖ ^ 2 / S.r u 0)) < ⊤ ∧
        (∫⁻ u in Ico ui 0, ENNReal.ofReal ((-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2)) < ⊤ ∧
        Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
        Tendsto (fun u => S.m u 0 / S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
        Tendsto (fun u => S.lam u 0) (𝓝[<] 0) (𝓝 lam₀) ∧
        (∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
          K * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))))
    (hopt : ∃ C : ℝ, 0 < C ∧
      ∀ p ∈ origDomain ui, S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ C) :
    ∀ η : ℝ, 0 < η → ∃ u₀ ∈ Ioo ui 0,
      ∀ p ∈ origDomain ui, u₀ ≤ p.1 → S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ η := by
  obtain ⟨δ, K, lam₀, hδ, hK, hlam, hgap, hflux, hmass, hR, htail, hlimit, hlog⟩ :=
    hterminal.2 hs
  obtain ⟨C, hC, hopt⟩ := hopt
  obtain ⟨hbound, hzero⟩ := Amplitude.row_amplitude_limit_of_terminal ui e S h C K hC hopt hR hlog
  intro η hη
  have hev := hzero.eventually (Iio_mem_nhds hη)
  obtain ⟨a, ha, hab⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset h.ui_neg).1 hev
  refine ⟨(a + 0) / 2, ⟨by linarith [ha.1, ha.2], by linarith [ha.2]⟩, ?_⟩
  intro p hp hlate
  exact (hbound p hp).trans (hab ⟨by linarith [ha.2], hp.2.1⟩).le

end Terminal

/-- [internal]
The two conclusions of `lem:charged-rphi-small` (charged_SF_new_version.tex:L1038–L1046),
conditional on exactly the terminal outputs consumed by
`Terminal.scalar_amplitude_of_terminal`. The coupling is any fixed real
number; the late row may depend on it and on the requested tolerance. -/
theorem charged_rphi_small_of_terminal (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S)
    (hterminal :
      (SignedTerminalBound ui S ↔ PositiveTerminalFinite ui S) ∧
      (SignedTerminalBound ui S →
        ∃ δ K lam₀ : ℝ, 0 < δ ∧ 0 < K ∧ 0 < lam₀ ∧
        (∀ u ∈ Ico ui 0, δ ≤ 1 - S.mu u 0) ∧
        (∫⁻ u in Ico ui 0,
          ENNReal.ofReal ((-S.nu u 0) * ‖S.xi u 0 / (S.nu u 0 : ℂ)‖ ^ 2 / S.r u 0)) < ⊤ ∧
        (∫⁻ u in Ico ui 0, ENNReal.ofReal ((-S.nu u 0) * S.m u 0 / S.r u 0 ^ 2)) < ⊤ ∧
        Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
        Tendsto (fun u => S.m u 0 / S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
        Tendsto (fun u => S.lam u 0) (𝓝[<] 0) (𝓝 lam₀) ∧
        (∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
          K * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))))
    (hopt : ∃ C : ℝ, 0 < C ∧
      ∀ p ∈ origDomain ui, S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ C) :
    (∀ η : ℝ, 0 < η → ∃ u₀ ∈ Ioo ui 0,
      ∀ p ∈ origDomain ui, u₀ ≤ p.1 → S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ η) ∧
    (∀ η : ℝ, 0 < η → ∃ u₀ ∈ Ioo ui 0,
      ∀ p ∈ origDomain ui, u₀ ≤ p.1 → |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ η) := by
  have hamp := Terminal.scalar_amplitude_of_terminal ui e S h hs hterminal hopt
  refine ⟨hamp, ?_⟩
  intro η hη
  obtain ⟨u₀, hu₀, hsmall⟩ := hamp (η / (|e| + 1)) (div_pos hη (by positivity))
  refine ⟨u₀, hu₀, ?_⟩
  intro p hp hlate
  have hmul := mul_le_mul_of_nonneg_left (hsmall p hp hlate) (abs_nonneg e)
  calc
    _ = |e| * (S.r p.1 p.2 * ‖S.phi p.1 p.2‖) := by ring
    _ ≤ |e| * (η / (|e| + 1)) := hmul
    _ ≤ η := by
      rw [← mul_div_assoc, div_le_iff₀ (show 0 < |e| + 1 by positivity)]
      nlinarith only [hη.le]

end EmcsfAcExtension.Global
