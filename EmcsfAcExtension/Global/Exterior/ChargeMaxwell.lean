module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Domains
import EmcsfAcExtension.Global.Exterior.Main
import EmcsfAcExtension.Global.Exterior.Charge

/-! # Maxwell integral on the selected exterior annulus

Complete the annular oscillation export with the intermediate Maxwell
integral from `charged_SF_new_version.tex:L1170–1177` and internal project record, supporting
optics.
The radial measure is written in labels as `dr = λ dv`.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Exterior

variable {ui e : ℝ} {S : Fields}

/-- [internal]
Maxwell FTC on any two points of a proper annulus, followed by integral
monotonicity onto that same annulus. The prescribed scalar bound `L` is
uniform on the annulus; the coefficient is exactly `|e| L`. The final
integrand retains the radial Jacobian `λ`. -/
theorem annular_maxwell_integral_of_envelope (h : OriginalData ui e S)
    {u a b L : ℝ} (hua : u < a) (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ origDomain ui) (hL : 0 ≤ L)
    (hphi : ∀ v ∈ Icc a b, ‖S.phi u v‖ ≤ L) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |S.Q u s - S.Q u t| ≤ |e| * L *
        (∫ v in a..b, S.r u v * ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) := by
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hseg
  have ct := Calculus.continuousOn_out_section h.solution.cont_theta hseg
  have hi := (cr.mul ct.norm).intervalIntegrable_of_Icc (μ := volume) hab
  have hr (v : ℝ) (hv : v ∈ Icc a b) :=
    h.solution.r_pos (u, v) (hseg ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hc (v : ℝ) (hv : v ∈ Icc a b) :
      ‖S.QV e u v‖ ≤ (|e| * L) * (S.r u v * ‖S.theta u v‖) := by
    have him := Complex.abs_im_le_norm (starRingEnd ℂ (S.phi u v) * S.theta u v)
    rw [norm_mul, Complex.norm_conj] at him
    simp only [Fields.QV, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (hr v hv)]
    calc
      _ ≤ |e| * S.r u v * (‖S.phi u v‖ * ‖S.theta u v‖) :=
        mul_le_mul_of_nonneg_left him (mul_nonneg (abs_nonneg _) (hr v hv).le)
      _ ≤ |e| * S.r u v * (L * ‖S.theta u v‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hphi v hv) (norm_nonneg _))
          (mul_nonneg (abs_nonneg _) (hr v hv).le)
      _ = _ := by ring
  have hnonneg : ∀ᵐ v ∂volume.restrict (Ioc a b), 0 ≤ S.r u v * ‖S.theta u v‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact mul_nonneg (hr v ⟨hv.1.le, hv.2⟩).le (norm_nonneg _)
  have hlocal {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      |S.Q u s - S.Q u t| ≤ (|e| * L) * (∫ v in a..b, S.r u v * ‖S.theta u v‖) := by
    have hsub : outSeg u s t ⊆ origDomain ui :=
      fun _ hp => hseg (outSeg_subset_outSeg hs.1 ht.2 hp)
    have hQ := (h.solution.eq_out u s t (hua.trans_le hs.1) hst hsub).2.2.2.1
    have hist : IntervalIntegrable (fun v => S.r u v * ‖S.theta u v‖) volume s t :=
      hi.mono_set (by
        simpa only [uIcc_of_le hst, uIcc_of_le hab] using (Icc_subset_Icc hs.1 ht.2))
    rw [abs_sub_comm, ← Real.norm_eq_abs, hQ.2]
    calc
      _ ≤ ∫ v in s..t, ‖S.QV e u v‖ := intervalIntegral.norm_integral_le_integral_norm hst
      _ ≤ ∫ v in s..t, (|e| * L) * (S.r u v * ‖S.theta u v‖) :=
        intervalIntegral.integral_mono_on hst hQ.1.norm
          (hist.const_mul _) (fun v hv => hc v ⟨hs.1.trans hv.1, hv.2.trans ht.2⟩)
      _ = (|e| * L) * (∫ v in s..t, S.r u v * ‖S.theta u v‖) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (intervalIntegral.integral_mono_interval hs.1 hst ht.2 hnonneg hi)
        (mul_nonneg (abs_nonneg _) hL)
  have hj : (∫ v in a..b, S.r u v * ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) =
      ∫ v in a..b, S.r u v * ‖S.theta u v‖ := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    have hl := h.solution.lam_pos (u, v) (hseg ⟨rfl, hv'⟩)
    dsimp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
    field_simp [hl.ne']
  rw [hj]
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact hlocal hs ht hst
  · simpa only [abs_sub_comm] using hlocal ht hs hts

/-- [internal]
Cauchy–Schwarz bounds the Maxwell integral on a comparable proper annulus
(`charged_SF_new_version.tex:L1170–1177`), with the radial Jacobian `dr = λ dv` retained.
The numerical coefficient `4` is universal, uniformly in the solution,
coupling and annulus. The consumer discharges the scalar-energy premise
from the late exterior energy estimate; no scalar envelope is needed. -/
theorem annular_maxwell_integral_le_of_energy (h : OriginalData ui e S) {u a b r : ℝ}
    (hr : 0 < r) (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ origDomain ui)
    (hrb : ∀ v ∈ Icc a b, S.r u v ≤ 2 * r)
    (hlen : S.r u b - S.r u a ≤ r)
    (hE : (∫ v in a..b, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
      4 * terminalMass S u) :
    (∫ v in a..b, S.r u v * ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) ≤
      4 * r * Real.sqrt (terminalMass S u * r) := by
  have hrpos (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have ct := Calculus.continuousOn_out_section h.solution.cont_theta hs
  let f := fun v => ‖S.theta u v‖ / Real.sqrt (S.lam u v)
  let g := fun v => S.r u v * Real.sqrt (S.lam u v)
  have hf : ContinuousOn f (Icc a b) := ct.norm.div cl.sqrt
    (fun v hv => (Real.sqrt_pos.mpr (hl v hv)).ne')
  have hg : ContinuousOn g (Icc a b) := cr.mul cl.sqrt
  have hc := integral_cauchy_schwarz hab hf hg
  have heq : (∫ v in a..b, f v ^ 2) =
      ∫ v in a..b, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    dsimp [f]
    rw [div_pow, Real.sq_sqrt (hl v hv').le,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl v hv'), div_pow]
    field_simp [(hl v hv').ne']
  have hgeq : (∫ v in a..b, g v ^ 2) = ∫ v in a..b, S.r u v ^ 2 * S.lam u v := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (hl v hv').le]
  have hfg : (∫ v in a..b, f v * g v) = ∫ v in a..b, S.r u v * ‖S.theta u v‖ := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    dsimp [f, g]
    field_simp [(Real.sqrt_pos.mpr (hl v hv')).ne']
  rw [heq, hgeq, hfg] at hc
  have hiB : IntervalIntegrable (fun v => S.r u v ^ 2 * S.lam u v) volume a b :=
    ((cr.pow 2).mul cl).intervalIntegrable_of_Icc hab
  have hiB' : IntervalIntegrable (fun v => (2 * r) ^ 2 * S.lam u v) volume a b :=
    (cl.const_mul _).intervalIntegrable_of_Icc hab
  have hB := intervalIntegral.integral_mono_on hab hiB hiB'
    (fun v hv => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hrpos v hv).le (hrb v hv) 2) (hl v hv).le)
  have hrad := (h.solution.eq_out u a b hua hab hs).1
  rw [intervalIntegral.integral_const_mul, ← hrad.2] at hB
  have hB' : (∫ v in a..b, S.r u v ^ 2 * S.lam u v) ≤ 4 * r ^ 3 := by
    nlinarith only [hB, mul_nonneg (sq_nonneg (2 * r)) (sub_nonneg.mpr hlen)]
  have hB0 : 0 ≤ ∫ v in a..b, S.r u v ^ 2 * S.lam u v :=
    intervalIntegral.integral_nonneg (μ := volume) hab
      (fun v hv => mul_nonneg (sq_nonneg _) (hl v hv).le)
  have hbp : (u, b) ∈ origDomain ui := hs ⟨rfl, hab, le_rfl⟩
  have hM : 0 ≤ terminalMass S u := mass_nonneg h
    (show (u, 0) ∈ origDomain ui from
      ⟨hbp.1, hbp.2.1, hbp.2.1.le, le_rfl⟩)
  have hprod := mul_le_mul hE hB' hB0 (mul_nonneg (by norm_num) hM)
  have hsqrt := Real.sq_sqrt (mul_nonneg hM hr.le)
  have hsqrtR : (4 * r * Real.sqrt (terminalMass S u * r)) ^ 2 =
      16 * terminalMass S u * r ^ 3 := by
    rw [mul_pow, hsqrt]
    ring
  have hI : (∫ v in a..b, S.r u v * ‖S.theta u v‖) ≤
      4 * r * Real.sqrt (terminalMass S u * r) := by
    have hsq := hc.trans hprod
    nlinarith only [hsq, hsqrtR,
      mul_nonneg hr.le (Real.sqrt_nonneg (terminalMass S u * r))]
  calc
    (∫ v in a..b, S.r u v * ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) =
        ∫ v in a..b, S.r u v * ‖S.theta u v‖ := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
      dsimp only
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl v hv')]
      field_simp [(hl v hv').ne']
    _ ≤ _ := hI

/-- [internal]
At every sufficiently late adaptive exterior point, the selected source
annulus satisfies both Maxwell's integral inequality and the numerical
oscillation bound (`charged_SF_new_version.tex:L1162–1177`). The same scalar envelope
`L = C (1 + sqrt(log(Ri/R)))` occurs in both inequalities. The positive
constant and cutoff depend on the fixed development, signed bound and
admissible profile, uniformly in the exterior point and both annular
labels. The numerical coefficient `4` is universal. -/
theorem annular_charge_oscillation_with_maxwell (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ C > 0, ∃ u₀ ∈ Ioo ui 0, ∀ u v,
      (u, v) ∈ adaptiveExterior S ui u₀ ell →
      ∃ a b, u < a ∧ a ≤ v ∧ v ≤ b ∧ b ≤ 0 ∧ ell (terminalRadius S u) ≤ S.r u a ∧
        S.r u v / 2 ≤ S.r u a ∧ S.r u b ≤ 2 * S.r u v ∧
        S.r u v / 2 ≤ S.r u b - S.r u a ∧ S.r u b - S.r u a ≤ S.r u v ∧
        ((a = v ∧ S.r u b = 2 * S.r u v) ∨
          (b = 0 ∧ S.r u a = terminalRadius S u / 2)) ∧
        (let L := C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))
         ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
          |S.Q u s - S.Q u t| ≤ |e| * L *
            (∫ w in a..b, S.r u w * ‖S.theta u w / (S.lam u w : ℂ)‖ * S.lam u w) ∧
          |S.Q u s - S.Q u t| ≤
            4 * |e| * L * S.r u v * Real.sqrt (terminalMass S u * S.r u v)) := by
  obtain ⟨Co, hCo, uo, huo, hosc⟩ :=
    annular_charge_oscillation_at_point h hs M ell hR hmass hell hellsmall hsmall
  obtain ⟨Cs, _, hCs, us, hus, hscalar⟩ :=
    scalar_log_envelope h hs M ell hR hmass hell hsmall
  let C := max Co (Cs + 2)
  refine ⟨C, hCo.trans_le (le_max_left _ _), max uo us,
    ⟨lt_max_of_lt_left huo.1, max_lt huo.2 hus.2⟩, ?_⟩
  intro u v hp
  obtain ⟨a, b, hua, hav, hvb, hb, hℓa, hra, hrb, hlo, hhi, hcase, hn⟩ :=
    hosc u v ⟨hp.1, (le_max_left _ _).trans hp.2.1, hp.2.2⟩
  have hab := hav.trans hvb
  have hseg : outSeg u a b ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hab).2 ⟨hp.1.1, hp.1.2.1, hua.le, hb⟩
  let L := C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))
  have hphi (w : ℝ) (hw : w ∈ Icc a b) : ‖S.phi u w‖ ≤ L := by
    apply (hscalar (u, w) ⟨hseg ⟨rfl, hw⟩, (le_max_right _ _).trans hp.2.1,
      hℓa.trans (outgoing_radius_mono h hua.le hw.1
        (fun _ hq => hseg (outSeg_subset_outSeg le_rfl hw.2 hq)))⟩).trans
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hm := annular_maxwell_integral_of_envelope h hua hab hseg
    (show 0 ≤ L by dsimp [L, C]; positivity) hphi
  refine ⟨a, b, hua, hav, hvb, hb, hℓa, hra, hrb, hlo, hhi, hcase, ?_⟩
  dsimp only
  intro s hs' t ht'
  refine ⟨hm s hs' t ht', (hn s hs' t ht').trans ?_⟩
  have hr := h.solution.r_pos (u, v) hp.1 (hua.trans_le hav)
  dsimp only [L, C]
  gcongr
  exact le_max_left _ _

/-- [node c:exterior#annular-charge-oscillation]
On the selected source annulus, export the complete Maxwell chain:
oscillation ≤ Maxwell integral ≤ the numerical bound, retaining the
previous numerical oscillation conclusion (`charged_SF_new_version.tex:L1162–1177`).
One scalar envelope `L = C (1 + sqrt(log(Ri/R)))` is used throughout.
The positive constant and cutoff may depend on the fixed development,
signed bound and admissible profile, uniformly in all subsequent exterior
points and annular labels. The coefficient `4` is universal. -/
theorem annular_charge_oscillation_with_maxwell_bound (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ C > 0, ∃ u₀ ∈ Ioo ui 0, ∀ u v,
      (u, v) ∈ adaptiveExterior S ui u₀ ell →
      ∃ a b, u < a ∧ a ≤ v ∧ v ≤ b ∧ b ≤ 0 ∧ ell (terminalRadius S u) ≤ S.r u a ∧
        S.r u v / 2 ≤ S.r u a ∧ S.r u b ≤ 2 * S.r u v ∧
        S.r u v / 2 ≤ S.r u b - S.r u a ∧ S.r u b - S.r u a ≤ S.r u v ∧
        ((a = v ∧ S.r u b = 2 * S.r u v) ∨
          (b = 0 ∧ S.r u a = terminalRadius S u / 2)) ∧
        (let L := C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))
         ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
          |S.Q u s - S.Q u t| ≤ |e| * L *
            (∫ w in a..b, S.r u w * ‖S.theta u w / (S.lam u w : ℂ)‖ * S.lam u w) ∧
          |S.Q u s - S.Q u t| ≤
            4 * |e| * L * S.r u v * Real.sqrt (terminalMass S u * S.r u v) ∧
          |e| * L *
            (∫ w in a..b, S.r u w * ‖S.theta u w / (S.lam u w : ℂ)‖ * S.lam u w) ≤
            4 * |e| * L * S.r u v * Real.sqrt (terminalMass S u * S.r u v)) := by
  obtain ⟨C, hC, uo, huo, hosc⟩ :=
    annular_charge_oscillation_with_maxwell h hs M ell hR hmass hell hellsmall hsmall
  obtain ⟨ue, hue, henergy⟩ :=
    charged_exterior_scalar_energy h hs M ell hR hmass hell hsmall
  refine ⟨C, hC, max uo ue, ⟨lt_max_of_lt_left huo.1, max_lt huo.2 hue.2⟩, ?_⟩
  intro u v hp
  obtain ⟨a, b, hua, hav, hvb, hb, hℓa, hra, hrb, hlo, hhi, hcase, hn⟩ :=
    hosc u v ⟨hp.1, (le_max_left _ _).trans hp.2.1, hp.2.2⟩
  have hab := hav.trans hvb
  have hseg : outSeg u a 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff (hab.trans hb)).2
      ⟨hp.1.1, hp.1.2.1, hua.le, le_rfl⟩
  have hsub : outSeg u a b ⊆ origDomain ui :=
    fun _ hx => hseg (outSeg_subset_outSeg le_rfl hb hx)
  have hc := ((Calculus.continuousOn_out_section h.solution.cont_theta hseg).div
    (Complex.continuous_ofReal.comp_continuousOn
      (Calculus.continuousOn_out_section h.solution.cont_lam hseg))
    (fun w hw => Complex.ofReal_ne_zero.mpr
      (h.solution.lam_pos (u, w) (hseg ⟨rfl, hw⟩)).ne')).norm.pow 2
  have hi := (hc.mul
    (Calculus.continuousOn_out_section h.solution.cont_lam hseg)).intervalIntegrable_of_Icc
    (μ := volume) (hab.trans hb)
  have hE := (intervalIntegral.integral_mono_interval le_rfl hab hb
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun w hw =>
      mul_nonneg (sq_nonneg _) (h.solution.lam_pos (u, w)
        (hseg ⟨rfl, hw.1.le, hw.2⟩)).le)) hi).trans
    (henergy u a ⟨hseg ⟨rfl, le_rfl, hab.trans hb⟩,
      (le_max_right _ _).trans hp.2.1, hℓa⟩).1
  have hr := h.solution.r_pos (u, v) hp.1 (hua.trans_le hav)
  have hI := annular_maxwell_integral_le_of_energy h hr hua hab hsub
    (fun w hw => (outgoing_radius_mono h (hua.trans_le hw.1).le hw.2
      (fun _ hx => hsub (outSeg_subset_outSeg hw.1 le_rfl hx))).trans hrb) hhi hE
  refine ⟨a, b, hua, hav, hvb, hb, hℓa, hra, hrb, hlo, hhi, hcase, ?_⟩
  dsimp only
  intro s hs' t ht'
  refine ⟨(hn s hs' t ht').1, (hn s hs' t ht').2, ?_⟩
  calc
    _ ≤ (|e| * (C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))) *
        (4 * S.r u v * Real.sqrt (terminalMass S u * S.r u v)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by ring

end EmcsfAcExtension.Global.Exterior
