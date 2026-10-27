module

public import EmcsfAcExtension.Frozen.SignedExpIntegrand
public import EmcsfAcExtension.Frozen.PositiveExpIntegrand
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Api.Finite
public import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Exact incoming flux identity

The identity of charged_SF_new_version.tex:L972–980 follows directly from the frozen
incoming radius and mass equations, as detailed in approved internal project record (T1).
All logarithms are taken on proper positive-radius sections. No terminal
integrability premise enters the identity.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Terminal

/-- [internal] Both frozen exponents and their charge correction are continuous
on each proper incoming positive-radius section. -/
theorem incoming_integrands_continuousOn {e : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D) {a b v : ℝ}
    (hbv : b < v) (hseg : inSeg a b v ⊆ D) :
    ContinuousOn (fun s => signedExpIntegrand S s v) (Icc a b) ∧
    ContinuousOn (fun s => positiveExpIntegrand S s v) (Icc a b) ∧
    ContinuousOn (fun s => -S.nu s v * S.Q s v ^ 2 /
      ((1 - S.mu s v) * S.r s v ^ 3)) (Icc a b) := by
  have cr := Calculus.continuousOn_in_section hS.cont_r hseg
  have cm := Calculus.continuousOn_in_section hS.cont_m hseg
  have cn := Calculus.continuousOn_in_section hS.cont_nu hseg
  have cq := Calculus.continuousOn_in_section hS.cont_Q hseg
  have hr : ∀ s ∈ Icc a b, S.r s v ≠ 0 := fun s hs =>
    (hS.r_pos (s, v) (hseg ⟨hs.1, hs.2, rfl⟩) (hs.2.trans_lt hbv)).ne'
  have hg : ∀ s ∈ Icc a b, 1 - S.mu s v ≠ 0 := fun s hs =>
    (hS.one_sub_mu_pos (s, v) (hseg ⟨hs.1, hs.2, rfl⟩)).ne'
  have cμ : ContinuousOn (fun s => S.mu s v) (Icc a b) :=
    (continuousOn_const.mul cm).div cr hr
  have cg : ContinuousOn (fun s => 1 - S.mu s v) (Icc a b) :=
    continuousOn_const.sub cμ
  refine ⟨?_, ?_, ?_⟩
  · exact (cn.neg.mul (cμ.sub ((cq.pow 2).div (cr.pow 2)
      (fun s hs => pow_ne_zero _ (hr s hs))))).div (cg.mul cr)
      (fun s hs => mul_ne_zero (hg s hs) (hr s hs))
  · exact (cn.neg.mul cμ).div (cg.mul cr)
      (fun s hs => mul_ne_zero (hg s hs) (hr s hs))
  · exact (cn.neg.mul (cq.pow 2)).div (cg.mul (cr.pow 3))
      (fun s hs => mul_ne_zero (hg s hs) (pow_ne_zero _ (hr s hs)))


/-- [internal] The scalar flux density is continuous on every proper incoming
positive-radius section. -/
theorem incoming_flux_continuousOn {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hbv : b < v)
    (hseg : inSeg a b v ⊆ D) :
    ContinuousOn (fun s => ‖S.xi s v‖ ^ 2 / ((-S.nu s v) * S.r s v)) (Icc a b) := by
  have cx := Calculus.continuousOn_in_section hS.cont_xi hseg
  have cn := Calculus.continuousOn_in_section hS.cont_nu hseg
  have cr := Calculus.continuousOn_in_section hS.cont_r hseg
  exact (cx.norm.pow 2).div (cn.neg.mul cr) (fun s hs =>
    mul_ne_zero (neg_ne_zero.mpr (hS.nu_neg (s, v) (hseg ⟨hs.1, hs.2, rfl⟩)).ne)
      (hS.r_pos (s, v) (hseg ⟨hs.1, hs.2, rfl⟩) (hs.2.trans_lt hbv)).ne')

/-- [internal] The logarithmic gap equation in integral form, derived from
`r_u = ν` and the literal ordinary mass equation on a proper section. -/
theorem incoming_log_gap_integralForm {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg a b v ⊆ D) :
    IntegralForm (fun s => Real.log (1 - S.mu s v))
      (fun s => ‖S.xi s v‖ ^ 2 / ((-S.nu s v) * S.r s v) -
        signedExpIntegrand S s v) a b := by
  have cr := Calculus.continuousOn_in_section hS.cont_r hseg
  have cm := Calculus.continuousOn_in_section hS.cont_m hseg
  have hr : ∀ s ∈ Icc a b, 0 < S.r s v := fun s hs =>
    hS.r_pos (s, v) (hseg ⟨hs.1, hs.2, rfl⟩) (hs.2.trans_lt hbv)
  have hg : ∀ s ∈ Icc a b, 0 < 1 - S.mu s v := fun s hs =>
    hS.one_sub_mu_pos (s, v) (hseg ⟨hs.1, hs.2, rfl⟩)
  have cμ : ContinuousOn (fun s => S.mu s v) (Icc a b) :=
    (continuousOn_const.mul cm).div cr (fun s hs => (hr s hs).ne')
  obtain ⟨c, hc, hcl⟩ := isCompact_Icc.exists_forall_le' cr hr
  obtain ⟨d, hd, hdl⟩ := isCompact_Icc.exists_forall_le'
    (continuousOn_const.sub cμ) hg
  have hac := hS.ac_in a b v hab hseg
  have acμ : AbsolutelyContinuousOnInterval (fun s => S.mu s v) a b :=
    (hac.2.1.const_mul 2).div_of_le_norm hac.1 hc (by
      intro s hs
      rw [uIcc_of_le hab] at hs
      exact (hcl s hs).trans (le_abs_self _))
  have ac1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  have acg := (ac1.sub acμ).log_of_pos_le hd (by
    simpa only [uIcc_of_le hab] using hdl)
  have hi := ((incoming_flux_continuousOn hS hbv hseg).sub
    (incoming_integrands_continuousOn hS hbv hseg).1).intervalIntegrable_of_Icc (μ := volume) hab
  have hs := Local.IsSolution.in_section hS hab hbv hseg
  apply integralForm_of_ac_of_ae_hasDerivAt acg hi
  rw [uIcc_of_le hab]
  apply (ae_restrict_iff' measurableSet_Icc).mp
  filter_upwards [hs.1.2, hs.2.2.1.2, ae_restrict_mem measurableSet_Icc]
    with s hdr hdm hmem
  have hn := (hS.nu_neg (s, v) (hseg ⟨hmem.1, hmem.2, rfl⟩)).ne
  have hrr := (hr s hmem).ne'
  have hgg := (hg s hmem).ne'
  have hder := ((hasDerivAt_const s (1 : ℝ)).sub
    ((hdm.const_mul 2).div hdr hrr)).log hgg
  apply hder.congr_deriv
  change ((0 - (2 * S.mU s v * S.r s v - 2 * S.m s v * S.nu s v) / S.r s v ^ 2) /
    (1 - S.mu s v)) =
      ‖S.xi s v‖ ^ 2 / ((-S.nu s v) * S.r s v) - signedExpIntegrand S s v
  have hm : 2 * S.m s v = S.mu s v * S.r s v := by
    dsimp [Fields.mu]
    rw [div_mul_cancel₀ _ hrr]
  dsimp [Fields.mU, signedExpIntegrand]
  rw [hm]
  field_simp [hrr, hn, hgg]
  ring

/-- [internal] The exact scalar flux identity on an arbitrary proper incoming
section of a frozen solution. -/
theorem incoming_flux_identity {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg a b v ⊆ D) :
    (∫ s in a..b, signedExpIntegrand S s v) =
      (∫ s in a..b, ‖S.xi s v‖ ^ 2 / ((-S.nu s v) * S.r s v)) -
        Real.log (1 - S.mu b v) + Real.log (1 - S.mu a v) := by
  have he := (incoming_log_gap_integralForm hS hab hbv hseg).2
  rw [intervalIntegral.integral_sub
    ((incoming_flux_continuousOn hS hbv hseg).intervalIntegrable_of_Icc hab)
    ((incoming_integrands_continuousOn hS hbv hseg).1.intervalIntegrable_of_Icc hab)] at he
  linarith only [he]

/-- [internal]
The exact terminal identity, charged_SF_new_version.tex:L972–980 and approved
internal project record (T1). It requires no signed terminal bound or finite terminal flux. -/
theorem flux_identity (ui e : ℝ) (S : Fields) (_hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (_hgauge : ∀ t, ui ≤ t → t < 0 → S.A t t = 0)
    (_hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (_hr : ∀ v ∈ Icc ui 0, S.r ui v = (v - ui) / 2)
    (_hdata : AbsolutelyContinuousOnInterval (S.a ui) ui 0)
    (u : ℝ) (hu : u ∈ Ioo ui 0) :
    (∫ s in ui..u, signedExpIntegrand S s 0) =
      (∫ s in ui..u, ‖S.xi s 0‖ ^ 2 / ((-S.nu s 0) * S.r s 0)) -
        Real.log (1 - S.mu u 0) + Real.log (1 - S.mu ui 0) := by
  exact incoming_flux_identity hS hu.1.le hu.2
    ((inSeg_subset_origDomain_iff hu.1.le).2 ⟨le_rfl, hu.2, hu.2.le, le_rfl⟩)

/-- [node prop:charged-terminal-equivalence#terminal-gap-and-flux]
A signed terminal upper bound gives a positive terminal gap and finite
nonnegative scalar flux (charged_SF_new_version.tex:L981–990). The gap witness depends
on the fixed solution and its signed bound, uniformly in the terminal label. -/
theorem terminal_gap_and_flux (ui e : ℝ) (S : Fields) (hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (hgauge : ∀ t, ui ≤ t → t < 0 → S.A t t = 0)
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (hr : ∀ v ∈ Icc ui 0, S.r ui v = (v - ui) / 2)
    (hdata : AbsolutelyContinuousOnInterval (S.a ui) ui 0)
    (hs : BddAbove ((fun u => ∫ s in ui..u, signedExpIntegrand S s 0) '' Ioo ui 0)) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ Ico ui 0, δ ≤ 1 - S.mu u 0) ∧
    (∫⁻ u in Ico ui 0, ENNReal.ofReal
      (‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0))) < ⊤ := by
  obtain ⟨B, hB⟩ := hs
  let B' := max B 0
  have hB0 : 0 ≤ B' := le_max_right _ _
  have hb (u : ℝ) (hu : u ∈ Ioo ui 0) :
      (∫ s in ui..u, signedExpIntegrand S s 0) ≤ B' :=
    (hB (mem_image_of_mem _ hu)).trans (le_max_left _ _)
  have hpi : (ui, 0) ∈ origDomain ui := ⟨le_rfl, hui, hui.le, le_rfl⟩
  have hgi := hS.one_sub_mu_pos (ui, 0) hpi
  have fnonneg (u : ℝ) (hu : u ∈ Ico ui 0) :
      0 ≤ ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0) :=
    div_nonneg (sq_nonneg _) (mul_nonneg
      (neg_nonneg.mpr (hS.nu_neg (u, 0) ⟨hu.1, hu.2, hu.2.le, le_rfl⟩).le)
      (hS.r_pos (u, 0) ⟨hu.1, hu.2, hu.2.le, le_rfl⟩ hu.2).le)
  have hproper (u : ℝ) (hu : u ∈ Ioo ui 0) :
      (∫ s in ui..u, ‖S.xi s 0‖ ^ 2 / ((-S.nu s 0) * S.r s 0)) -
        Real.log (1 - S.mu u 0) ≤ B' - Real.log (1 - S.mu ui 0) := by
    have he := flux_identity ui e S hui hS hgauge hmu hr hdata u hu
    have hh := hb u hu
    linarith only [he, hh]
  have hlog (u : ℝ) (hu : u ∈ Ioo ui 0) : Real.log (1 - S.mu u 0) ≤ 0 :=
    Real.log_nonpos (hS.one_sub_mu_pos (u, 0)
      ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩).le
      (by linarith only [(hmu (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩).1])
  constructor
  · refine ⟨Real.exp (Real.log (1 - S.mu ui 0) - B'), Real.exp_pos _, ?_⟩
    intro u hu
    apply (Real.exp_le_exp.mpr ?_).trans_eq
      (Real.exp_log (hS.one_sub_mu_pos (u, 0) ⟨hu.1, hu.2, hu.2.le, le_rfl⟩))
    rcases eq_or_lt_of_le hu.1 with rfl | hui'
    · linarith only [hB0]
    · have hF : 0 ≤ ∫ s in ui..u, ‖S.xi s 0‖ ^ 2 / ((-S.nu s 0) * S.r s 0) :=
        intervalIntegral.integral_nonneg hui'.le
          (fun s hs => fnonneg s ⟨hs.1, hs.2.trans_lt hu.2⟩)
      have hh := hproper u ⟨hui', hu.2⟩
      linarith only [hF, hh]
  · obtain ⟨v, hvmono, hv, hvlim⟩ := exists_seq_strictMono_tendsto' hui
    apply lt_top_iff_ne_top.mpr
    apply lintegral_ofReal_Ico_ne_top_of_intervalIntegral_bounds
      (C := B' - Real.log (1 - S.mu ui 0))
      hvmono.monotone (fun n => (hv n).2) hvlim (fun n => (hv n).1.le)
      (fun n => (incoming_flux_continuousOn hS (hv n).2
        ((inSeg_subset_origDomain_iff (hv n).1.le).2
          ⟨le_rfl, (hv n).2, (hv n).2.le, le_rfl⟩)).intervalIntegrable_of_Icc (hv n).1.le)
      fnonneg
    intro n
    have hh := hproper (v n) (hv n)
    have hl := hlog (v n) (hv n)
    linarith only [hh, hl]

end EmcsfAcExtension.Global.Terminal

namespace EmcsfAcExtension.Global

/-- [node eq:charged-terminal-flux-identity]
Canonical exact flux identity, charged_SF_new_version.tex:L972–980. -/
theorem charged_terminal_flux_identity (ui e : ℝ) (S : Fields) (_hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (_hgauge : ∀ t, ui ≤ t → t < 0 → S.A t t = 0)
    (_hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (_hr : ∀ v ∈ Icc ui 0, S.r ui v = (v - ui) / 2)
    (_hdata : AbsolutelyContinuousOnInterval (S.a ui) ui 0)
    (u : ℝ) (hu : u ∈ Ioo ui 0) :
    (∫ s in ui..u, signedExpIntegrand S s 0) =
      (∫ s in ui..u, ‖S.xi s 0‖ ^ 2 / ((-S.nu s 0) * S.r s 0)) -
        Real.log (1 - S.mu u 0) + Real.log (1 - S.mu ui 0) := by
  exact Terminal.flux_identity ui e S _hui hS _hgauge _hmu _hr _hdata u hu

end EmcsfAcExtension.Global
