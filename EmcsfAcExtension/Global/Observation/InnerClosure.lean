module

public import Mathlib
public import EmcsfAcExtension.Global.Observation.InnerTransport
public import EmcsfAcExtension.Global.Observation.IncomingTrace
import EmcsfAcExtension.Infra.Gronwall
import EmcsfAcExtension.Global.Observation.InnerMass

/-! # Removal of the inner scalar comparison stop

The coefficient and smallness threshold are chosen before the actual
comparison functions, member-dependent depth, coupling and boundary
errors. Source: charged_SF_new_version.tex:L2727–L2735; internal project record inner closure.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

variable {rStar rho Lzero delta c K G Qmax Cscalar Bcharge Amax : ℝ}
variable {S : Fields} {D : Set (ℝ × ℝ)} {H : ℂ}
variable {yStar : ℝ → ℂ} {mStar : ℝ → ℝ} {a b qStar e eta etheta em exi : ℝ}

/-- [internal]
The two inner profiles are continuous actual maxima on the same complete
sideways truncations. Their nonnegativity and pointwise envelopes follow
from compact attainment, before any Volterra or scalar-stop assumption. -/
theorem Observation.inner_depth_profiles_of_normalization (hc : 0 < c)
    (h : Observation.InnerComparisonData rho Lzero delta c K G Qmax Cscalar Bcharge Amax
      S D H yStar mStar a b qStar e eta etheta em exi) :
    let R := sidewaysTruncation S D a b rho Lzero
    let Y := fun u v => S.theta u v / (S.lam u v : ℂ) - yStar (S.r u v)
    let Z := fun u v => S.xi u v / (S.nu u v : ℂ) - yStar (S.r u v)
    let F := fun d => sSup ((fun p : ℝ × ℝ => ‖Y p.1 p.2‖) ''
      sidewaysTruncation S D a b (Lzero - d) Lzero)
    let N := fun d => sSup ((fun p : ℝ × ℝ => ‖massComparison S mStar p.1 p.2‖) ''
      sidewaysTruncation S D a b (Lzero - d) Lzero)
    ContinuousOn (Function.uncurry Y) R ∧ ContinuousOn (Function.uncurry Z) R ∧
    ContinuousOn F (Icc 0 (Lzero - rho)) ∧ ContinuousOn N (Icc 0 (Lzero - rho)) ∧
    (∀ s, 0 ≤ F s ∧ 0 ≤ N s) ∧
    ∀ p ∈ R, ‖Y p.1 p.2‖ ≤ F (Lzero - S.r p.1 p.2) ∧
      ‖massComparison S mStar p.1 p.2‖ ≤ N (Lzero - S.r p.1 p.2) := by
  dsimp only
  let R := sidewaysTruncation S D a b rho Lzero
  let Y := fun u v => S.theta u v / (S.lam u v : ℂ) - yStar (S.r u v)
  let Z := fun u v => S.xi u v / (S.nu u v : ℂ) - yStar (S.r u v)
  rcases h.fields with ⟨cr, cn, cl, _ca, _cp, ct, cm, _cq, cx⟩
  have hn (p) (hp : p ∈ R) : S.nu p.1 p.2 < 0 := by linarith only [(h.box p hp).1.1, hc]
  have hl (p) (hp : p ∈ R) : 0 < S.lam p.1 p.2 := hc.trans_le (h.box p hp).2.1.1
  have cyr := h.static_continuous.1.comp cr (fun p hp => hp.2)
  have cY : ContinuousOn (Function.uncurry Y) R :=
    (ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
      (fun p hp => Complex.ofReal_ne_zero.mpr (hl p hp).ne')).sub cyr
  have cZ : ContinuousOn (Function.uncurry Z) R :=
    (cx.div (Complex.continuous_ofReal.comp_continuousOn cn)
      (fun p hp => Complex.ofReal_ne_zero.mpr (hn p hp).ne)).sub cyr
  have cM : ContinuousOn (Function.uncurry (massComparison S mStar)) R :=
    cm.sub (h.static_continuous.2.comp cr (fun p hp => hp.2))
  have hbase : ∃ p ∈ R, S.r p.1 p.2 = Lzero :=
    ⟨(a, a), h.boundary_mem a ⟨le_rfl, h.ordered⟩, (h.boundary a ⟨le_rfl, h.ordered⟩).1⟩
  have hdiag (p) (hp : p ∈ R) : S.r p.2 p.2 = Lzero :=
    (h.boundary p.2 ⟨hp.1.2.1, hp.1.2.2.1.trans hp.1.2.2.2⟩).1
  have hFY := continuousOn_outer_radius_maximum h.compact cr cY hbase h.triangles hdiag
    (fun p hp => (h.equations p hp).1) hn
  have hNM := continuousOn_outer_radius_maximum h.compact cr cM hbase h.triangles hdiag
    (fun p hp => (h.equations p hp).1) hn
  have hnonneg {E : Type} [NormedAddCommGroup E] (f : ℝ → ℝ → E) (s : ℝ) :
      0 ≤ sSup ((fun p : ℝ × ℝ => ‖f p.1 p.2‖) ''
        sidewaysTruncation S D a b (Lzero - s) Lzero) :=
    Real.sSup_nonneg (by rintro _ ⟨p, hp, rfl⟩; exact norm_nonneg _)
  refine ⟨cY, cZ, hFY.1, hNM.1, fun s => ⟨hnonneg Y s, hnonneg _ s⟩, ?_⟩
  intro p hp
  have hdepth : Lzero - S.r p.1 p.2 ∈ Icc 0 (Lzero - rho) :=
    ⟨sub_nonneg.mpr hp.2.2, sub_le_sub_left hp.2.1 Lzero⟩
  have hmem : p ∈ sidewaysTruncation S D a b (Lzero - (Lzero - S.r p.1 p.2)) Lzero := by
    simpa only [sub_sub_cancel] using
      (show p ∈ sidewaysTruncation S D a b (S.r p.1 p.2) Lzero from ⟨hp.1, le_rfl, hp.2.2⟩)
  exact ⟨norm_le_of_comparisonNorm_le (hnonneg Y _) hmem (hFY.2.2 _ hdepth).le,
    norm_le_of_comparisonNorm_le (hnonneg _ _) hmem (hNM.2.2 _ hdepth).le⟩

/-- [internal]
The incoming scalar error on the actual inner region retains its same
outgoing-label boundary value. Constants depend only on the displayed
fixed annulus and primitive bounds, before the fields, reference member,
background, coupling, errors and clock window. The outgoing equation and
all source/coordinate inputs of the radial transport helper are derived. -/
theorem Observation.inner_incoming_transport_of_normalization
    (hrStar : 0 < rStar) (hLzero : rStar ≤ Lzero) (hdelta : 0 < delta) (hc : 0 < c)
    (hK : 0 ≤ K) (hQmax : 0 ≤ Qmax) (hCs : 0 ≤ Cscalar)
    (hBq : 0 ≤ Bcharge) (hAm : 0 ≤ Amax) :
    ∃ Cz > 0, ∀ (rho : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ)
      (yStar : ℝ → ℂ) (mStar : ℝ → ℝ) (a b qStar e eta etheta em exi : ℝ),
    let R := sidewaysTruncation S D a b rho Lzero
    let Y := fun u v => S.theta u v / (S.lam u v : ℂ) - yStar (S.r u v)
    let Z := fun u v => S.xi u v / (S.nu u v : ℂ) - yStar (S.r u v)
    let F := fun d => sSup ((fun p : ℝ × ℝ => ‖Y p.1 p.2‖) ''
      sidewaysTruncation S D a b (Lzero - d) Lzero)
    let N := fun d => sSup ((fun p : ℝ × ℝ => ‖massComparison S mStar p.1 p.2‖) ''
      sidewaysTruncation S D a b (Lzero - d) Lzero)
    rStar ≤ rho → rho ≤ Lzero →
    Observation.InnerComparisonData rho Lzero delta c K G Qmax Cscalar Bcharge Amax
      S D H yStar mStar a b qStar e eta etheta em exi →
    ∀ p ∈ R, ‖Z p.1 p.2‖ ≤ Cz * ‖S.xi p.1 p.1 / S.nu p.1 p.1 - yStar Lzero‖ +
      Cz * eta + Cz * ∫ s in 0..(Lzero - S.r p.1 p.2), F s + N s := by
  obtain ⟨A, B, _E, hA, hB, _hE, hsources⟩ := Observation.inner_sources_of_normalization
    rStar delta c K Qmax Cscalar Bcharge Amax hrStar hdelta hc hK hQmax hCs hBq hAm
  obtain ⟨Cz, hCz, htransport⟩ := Observation.inner_incoming_transport_of_source_bounds
    A B Lzero hA.le hB.le (hrStar.trans_le hLzero).le
  refine ⟨Cz, hCz, ?_⟩
  intro rho S D H yStar mStar a b qStar e eta etheta em exi
  dsimp only
  intro hrho _hrhoL h
  let R := sidewaysTruncation S D a b rho Lzero
  let Y := fun u v => S.theta u v / (S.lam u v : ℂ) - yStar (S.r u v)
  let Z := fun u v => S.xi u v / (S.nu u v : ℂ) - yStar (S.r u v)
  let F := fun d => sSup ((fun p : ℝ × ℝ => ‖Y p.1 p.2‖) ''
    sidewaysTruncation S D a b (Lzero - d) Lzero)
  let N := fun d => sSup ((fun p : ℝ × ℝ => ‖massComparison S mStar p.1 p.2‖) ''
    sidewaysTruncation S D a b (Lzero - d) Lzero)
  rcases Observation.inner_depth_profiles_of_normalization hc h with ⟨cY, cZ, cF, cN, hNN, hprof⟩
  rcases h.fields with ⟨cr, cn, cl, _ca, cp, _ct, cm, cq, _cx⟩
  have hsrc := hsources rho Lzero G S D H yStar mStar a b qStar e eta etheta em exi hrho h
  intro p hp
  have hpath := (sidewaysTruncation_paths (h.triangles p hp)).2
  have hsec {T : Type} [TopologicalSpace T] {f : ℝ → ℝ → T}
      (cf : ContinuousOn (Function.uncurry f) R) :=
    continuousOn_outgoing_of_subtriangle cf (h.triangles p hp)
  have hrp : 0 < S.r p.1 p.2 := hrStar.trans_le (hrho.trans hp.2.1)
  have hRL := (h.boundary p.1 ⟨hp.1.2.1.trans hp.1.2.2.1, hp.1.2.2.2⟩).1
  have hl (s) (hs : s ∈ Icc p.2 p.1) : 0 < S.lam p.1 s :=
    hc.trans_le (h.box (p.1, s) (hpath s hs)).2.1.1
  obtain ⟨inv, _hmono, ci, himem, hi, hleft, hright, hdi⟩ :=
    radial_section_inverse_of_normalization hp.1.2.2.1 (hsec cr)
      (fun s hs => (h.equations (p.1, s) (hpath s (Ioo_subset_Icc_self hs))).2.1)
      (fun s hs => hl s (Ioo_subset_Icc_self hs))
  simp only [hRL] at hi hright hdi
  let m := fun s => S.m p.1 (inv s)
  let Q := fun s => S.Q p.1 (inv s)
  let phi := fun s => S.phi p.1 (inv s)
  let g := fun s => 1 - 2 * m s / s
  let k := fun s => (2 * m s / s - Q s ^ 2 / s ^ 2) / g s
  let ks := fun s => (2 * mStar s / s - qStar ^ 2 / s ^ 2) / (1 - 2 * mStar s / s)
  let Yr := fun s => Y p.1 (inv s)
  let Zr := fun s => Z p.1 (inv s)
  let source := fun s => -((1 / s : ℝ) : ℂ) * Yr s -
    (((k s - ks s) / s : ℝ) : ℂ) * yStar s + I * e * Q s * phi s / (g s * s : ℝ)
  have hmem (s) : (p.1, inv s) ∈ R := hpath (inv s) (himem s)
  have hrad (s) (hs : s ∈ Icc (S.r p.1 p.2) Lzero) : s ∈ Icc rho Lzero :=
    ⟨hp.2.1.trans hs.1, hs.2⟩
  have hpos (s) (hs : s ∈ Icc (S.r p.1 p.2) Lzero) : 0 < s := hrp.trans_le hs.1
  have hgp (s) (hs : s ∈ Icc (S.r p.1 p.2) Lzero) : 0 < g s := by
    have hh := (h.box (p.1, inv s) (hmem s)).2.2.2
    dsimp only [Fields.mu] at hh
    rw [hi s hs] at hh
    exact hdelta.trans_le hh
  have cy : ContinuousOn Yr (Icc (S.r p.1 p.2) Lzero) :=
    (hsec cY).comp ci.continuousOn (fun s _ => himem s)
  have cz : ContinuousOn Zr (Icc (S.r p.1 p.2) Lzero) :=
    (hsec cZ).comp ci.continuousOn (fun s _ => himem s)
  have cmm : ContinuousOn m (Icc (S.r p.1 p.2) Lzero) :=
    (hsec cm).comp ci.continuousOn (fun s _ => himem s)
  have cqq : ContinuousOn Q (Icc (S.r p.1 p.2) Lzero) :=
    (hsec cq).comp ci.continuousOn (fun s _ => himem s)
  have cpp : ContinuousOn phi (Icc (S.r p.1 p.2) Lzero) :=
    (hsec cp).comp ci.continuousOn (fun s _ => himem s)
  have cg : ContinuousOn g (Icc (S.r p.1 p.2) Lzero) :=
    continuousOn_const.sub ((continuousOn_const.mul cmm).div continuousOn_id
      (fun s hs => (hpos s hs).ne'))
  have ck : ContinuousOn k (Icc (S.r p.1 p.2) Lzero) :=
    (((continuousOn_const.mul cmm).div continuousOn_id (fun s hs => (hpos s hs).ne')).sub
      ((cqq.pow 2).div (continuousOn_id.pow 2) (fun s hs => pow_ne_zero 2 (hpos s hs).ne'))).div cg
      (fun s hs => (hgp s hs).ne')
  have cms := h.static_continuous.2.mono (fun s hs => hrad s hs)
  have cys := h.static_continuous.1.mono (fun s hs => hrad s hs)
  have cks : ContinuousOn ks (Icc (S.r p.1 p.2) Lzero) := by
    have cMu : ContinuousOn (fun s => 2 * mStar s / s) (Icc (S.r p.1 p.2) Lzero) :=
      (continuousOn_const.mul cms).div continuousOn_id (fun s hs => (hpos s hs).ne')
    exact (cMu.sub (continuousOn_const.div (continuousOn_id.pow 2)
      (fun s hs => pow_ne_zero 2 (hpos s hs).ne'))).div (continuousOn_const.sub cMu)
      (fun s hs => (hdelta.trans_le (h.static_bounds s (hrad s hs)).2.1).ne')
  have ca := ck.div continuousOn_id (fun s hs => (hpos s hs).ne')
  have cs : ContinuousOn source (Icc (S.r p.1 p.2) Lzero) :=
    (((Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.div continuousOn_id
      (fun s hs => (hpos s hs).ne'))).neg.mul cy).sub
      ((Complex.continuous_ofReal.comp_continuousOn ((ck.sub cks).div continuousOn_id
        (fun s hs => (hpos s hs).ne'))).mul cys)).add
      ((((Complex.continuous_ofReal.comp_continuousOn cqq).const_mul (I * e)).mul cpp).div
        (Complex.continuous_ofReal.comp_continuousOn (cg.mul continuousOn_id))
        (fun s hs => Complex.ofReal_ne_zero.mpr (mul_ne_zero (hgp s hs).ne' (hpos s hs).ne')))
  have hd (s) (hs : s ∈ Ioo (S.r p.1 p.2) Lzero) :
      HasDerivAt Zr (-((k s / s : ℝ) : ℂ) * Zr s + source s) s := by
    have hsm := Ioo_subset_Icc_self hs
    have hs' : s ∈ Ioo rho Lzero := ⟨lt_of_le_of_lt hp.2.1 hs.1, hs.2⟩
    have hl0 := (hc.trans_le (h.box (p.1, inv s) (hmem s)).2.1.1).ne'
    have hn0 : S.nu p.1 (inv s) ≠ 0 := by linarith only [(h.box (p.1, inv s) (hmem s)).1.1, hc]
    have hg0 : 1 - S.mu p.1 (inv s) ≠ 0 := (hdelta.trans_le (h.box (p.1, inv s) (hmem s)).2.2.2).ne'
    have hyD : HasDerivAt yStar
        (((-(1 + ks (S.r p.1 (inv s))) / S.r p.1 (inv s) : ℝ) : ℂ) *
          yStar (S.r p.1 (inv s))) (S.r p.1 (inv s)) := by
      rw [hi s hsm]
      exact (h.static_equations s hs').1
    have hzD := co_inner_z S e yStar ks (by rw [hi s hsm]; exact (hpos s hsm).ne') hl0 hn0 hg0
      (h.equations (p.1, inv s) (hmem s)).2.1
      (h.equations (p.1, inv s) (hmem s)).2.2.2.2.2.1
      (h.equations (p.1, inv s) (hmem s)).2.2.2.2.2.2 hyD
    convert hzD.scomp s (hdi s hs).2 using 1
    · rfl
    · dsimp only [source, k, g, m, Q, phi, Yr, Zr, Y, Z, Fields.mu]
      rw [hi s hsm]
      simp only [real_smul]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hl0, Complex.ofReal_ne_zero.mpr hn0,
        Complex.ofReal_ne_zero.mpr (hpos s hsm).ne']
      ring
  have hbounds (s) (hs : s ∈ Icc (S.r p.1 p.2) Lzero) := hsrc (p.1, inv s) (hmem s)
  have hsBound (s) (hs : s ∈ Icc (S.r p.1 p.2) Lzero) :
      ‖source s‖ ≤ B * (F (Lzero - s) + N (Lzero - s) + eta) := by
    have hp' := hprof (p.1, inv s) (hmem s)
    have hpy : ‖Yr s‖ ≤ F (Lzero - s) := by
      simpa only [Yr, Y, hi s hs] using hp'.1
    have hpm : |massComparison S mStar p.1 (inv s)| ≤ N (Lzero - s) := by
      simpa only [N, hi s hs, Real.norm_eq_abs] using hp'.2
    have hh : ‖source s‖ ≤ B * (‖Yr s‖ + |massComparison S mStar p.1 (inv s)| + eta) := by
      simpa only [source, k, ks, g, m, Q, phi, Yr, Y, Fields.mu, hi s hs] using (hbounds s hs).2.1
    exact hh.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hpy hpm) le_rfl) hB.le)
  have hco (s) (hs : s ∈ Icc (S.r p.1 p.2) Lzero) : k s / s ≤ A := by
    have hh := (hbounds s hs).1
    simpa only [k, g, m, Q, hi s hs, Fields.mu] using (le_abs_self _).trans hh
  have ht := htransport Zr source (fun s => k s / s) F N (S.r p.1 p.2) eta hrp.le hp.2.2
    h.errors.1 cz cs ca (cF.mono (Icc_subset_Icc le_rfl (sub_le_sub_left hp.2.1 Lzero)))
    (cN.mono (Icc_subset_Icc le_rfl (sub_le_sub_left hp.2.1 Lzero)))
    (fun s _ => hNN s) hco hd hsBound
  simpa only [Zr, Z, hleft, hright, hRL] using ht

/-- [internal]
The finite-depth double Volterra integral is bounded with the exact
coefficient `Lzero`, uniformly in every continuous nonnegative profile. -/
theorem Observation.inner_double_integral_le {f : ℝ → ℝ} {d Lzero : ℝ}
    (hd : 0 ≤ d) (hL : d ≤ Lzero) (cf : ContinuousOn f (Icc 0 d)) (hf : ∀ s, 0 ≤ f s) :
    (∫ s in 0..d, ∫ t in 0..s, f t) ≤ Lzero * ∫ t in 0..d, f t := by
  have hi := cf.intervalIntegrable_of_Icc (μ := volume) hd
  have cJ : ContinuousOn (fun s => ∫ t in 0..s, f t) (Icc 0 d) := by
    simpa only [uIcc_of_le hd] using
      (hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
  have hmono (s) (hs : s ∈ Icc 0 d) : (∫ t in 0..s, f t) ≤ ∫ t in 0..d, f t :=
    intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
      (Filter.Eventually.of_forall hf) hi
  have hh := intervalIntegral.integral_mono_on hd
    (cJ.intervalIntegrable_of_Icc (μ := volume) hd) intervalIntegrable_const hmono
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hL
    (intervalIntegral.integral_nonneg hd (fun s _ => hf s)))

/-- [internal]
The actual scalar/mass depth maxima satisfy the coupled Volterra bound.
Constants are fixed after the annulus and primitive reference/source
bounds, uniformly in the selected stopping radius `rho`, window, fields,
background and errors. The incoming transport, clock L² contribution,
finite double integral and mass inequality are all discharged here. -/
theorem Observation.inner_coupled_volterra_of_normalization
    (hrStar : 0 < rStar) (hLzero : rStar ≤ Lzero) (hdelta : 0 < delta) (hc : 0 < c)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hQmax : 0 ≤ Qmax) (hCs : 0 ≤ Cscalar)
    (hBq : 0 ≤ Bcharge) (hAm : 0 ≤ Amax) :
    ∃ C > 0, ∀ (rho : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ)
      (yStar : ℝ → ℂ) (mStar : ℝ → ℝ) (a b qStar e eta etheta em exi : ℝ),
    let Y := fun u v => S.theta u v / (S.lam u v : ℂ) - yStar (S.r u v)
    let F := fun d => sSup ((fun p : ℝ × ℝ => ‖Y p.1 p.2‖) ''
      sidewaysTruncation S D a b (Lzero - d) Lzero)
    let N := fun d => sSup ((fun p : ℝ × ℝ => ‖massComparison S mStar p.1 p.2‖) ''
      sidewaysTruncation S D a b (Lzero - d) Lzero)
    rStar ≤ rho → rho ≤ Lzero →
    Observation.InnerComparisonData rho Lzero delta c K G Qmax Cscalar Bcharge Amax
      S D H yStar mStar a b qStar e eta etheta em exi →
    F 0 ≤ C * (etheta + em + exi + eta) ∧
    ∀ d ∈ Icc 0 (Lzero - rho), (∀ s ∈ Icc 0 d, F s ≤ 1) →
      F d + N d ≤ C * (etheta + em + exi + eta) + C * ∫ s in 0..d, F s + N s := by
  obtain ⟨_A, B, E, _hA, hB, hE, hsources⟩ := Observation.inner_sources_of_normalization
    rStar delta c K Qmax Cscalar Bcharge Amax hrStar hdelta hc hK hQmax hCs hBq hAm
  obtain ⟨Cz, hCz, hIncoming⟩ := Observation.inner_incoming_transport_of_normalization
    (G := G) hrStar hLzero hdelta hc hK hQmax hCs hBq hAm
  obtain ⟨Cm, hCm, hMass⟩ := Observation.inner_mass_volterra_of_charge_bound
    rStar Lzero K G E hrStar hLzero hK hG hE.le
  let X := B * Cz * Real.sqrt (Lzero / 2)
  let T := B * (Cz + 1) * Lzero
  let J := B * Cz * Lzero + B
  let CY := 1 + X + T + J
  have hLz : 0 < Lzero := hrStar.trans_le hLzero
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hCY : 0 < CY := by dsimp [CY]; positivity
  have hCY1 : 1 ≤ CY := by dsimp only [CY]; linarith only [hX, hT, hJ]
  have hCYX : X ≤ CY := by dsimp only [CY]; linarith only [hT, hJ]
  have hCYT : T ≤ CY := by dsimp only [CY]; linarith only [hX, hJ]
  have hCYJ : J ≤ CY := by dsimp only [CY]; linarith only [hX, hT]
  refine ⟨CY + Cm, by positivity, ?_⟩
  intro rho S D H yStar mStar a b qStar e eta etheta em exi
  dsimp only
  intro hrho hrhoL h
  let R := sidewaysTruncation S D a b rho Lzero
  let Y := fun u v => S.theta u v / (S.lam u v : ℂ) - yStar (S.r u v)
  let Z := fun u v => S.xi u v / (S.nu u v : ℂ) - yStar (S.r u v)
  let F := fun d => sSup ((fun p : ℝ × ℝ => ‖Y p.1 p.2‖) ''
    sidewaysTruncation S D a b (Lzero - d) Lzero)
  let N := fun d => sSup ((fun p : ℝ × ℝ => ‖massComparison S mStar p.1 p.2‖) ''
    sidewaysTruncation S D a b (Lzero - d) Lzero)
  rcases Observation.inner_depth_profiles_of_normalization hc h with ⟨cY, cZ, cF, cN, hNN, hprof⟩
  rcases h.fields with ⟨cr, cn, cl, ca, cp, ct, cm, cq, cx⟩
  have hsrc := hsources rho Lzero G S D H yStar mStar a b qStar e eta etheta em exi hrho h
  have hz := hIncoming rho S D H yStar mStar a b qStar e eta etheta em exi hrho hrhoL h
  have hn (p) (hp : p ∈ R) : S.nu p.1 p.2 < 0 := by linarith only [(h.box p hp).1.1, hc]
  have hl (p) (hp : p ∈ R) : 0 < S.lam p.1 p.2 := hc.trans_le (h.box p hp).2.1.1
  have hIn {T : Type} [TopologicalSpace T] {f : ℝ → ℝ → T}
      (cf : ContinuousOn (Function.uncurry f) R) (p) (hp : p ∈ R) :
      ContinuousOn (fun s => f s p.2) (Icc p.2 p.1) :=
    cf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => h.triangles p hp (sidewaysTriangle_incoming hs))
  have hanti := strictAntiOn_radius_incoming_of_normalization cr h.triangles
    (fun p hp => (h.equations p hp).1) hn
  have cHb : ContinuousOn (fun u => S.xi u u / (S.nu u u : ℂ) - yStar Lzero) (Icc a b) :=
    ((cx.comp (continuousOn_id.prodMk continuousOn_id) h.boundary_mem).div
      (Complex.continuous_ofReal.comp_continuousOn
        (cn.comp (continuousOn_id.prodMk continuousOn_id) h.boundary_mem))
      (fun u hu => Complex.ofReal_ne_zero.mpr (hn (u, u) (h.boundary_mem u hu)).ne)).sub
      continuousOn_const
  have hI (d) (hd : 0 ≤ d) : 0 ≤ ∫ s in 0..d, F s + N s :=
    intervalIntegral.integral_nonneg hd (fun s _ => add_nonneg (hNN s).1 (hNN s).2)
  have hFbound (d) (hd : d ∈ Icc 0 (Lzero - rho)) :
      F d ≤ CY * (etheta + exi + eta) + CY * ∫ s in 0..d, F s + N s := by
    have hpoint (p) (hp : p ∈ sidewaysTruncation S D a b (Lzero - d) Lzero) :
        ‖Y p.1 p.2‖ ≤ CY * (etheta + exi + eta) + CY * ∫ s in 0..d, F s + N s := by
      have hpR : p ∈ R := sidewaysTruncation_mono_radius S D a b Lzero (by linarith only [hd.2]) hp
      have hpath := (sidewaysTruncation_paths (h.triangles p hpR)).1
      let dp := Lzero - S.r p.1 p.2
      have hdp : dp ∈ Icc 0 (Lzero - rho) :=
        ⟨sub_nonneg.mpr hpR.2.2, sub_le_sub_left hpR.2.1 Lzero⟩
      have hdpd : dp ≤ d := by dsimp only [dp]; linarith only [hp.2.1]
      have hdpL : dp ≤ Lzero := by linarith only [hdp.2, hrho, hrStar]
      have hv : p.2 ∈ Icc a b := ⟨hpR.1.2.1, hpR.1.2.2.1.trans hpR.1.2.2.2⟩
      have hRL := (h.boundary p.2 hv).1
      have hdep (s) (hs : s ∈ Icc p.2 p.1) : Lzero - S.r s p.2 ∈ Icc 0 dp := by
        have h1 := (hanti p hpR).antitoneOn ⟨le_rfl, hpR.1.2.2.1⟩ hs hs.1
        have h2 := (hanti p hpR).antitoneOn hs ⟨hpR.1.2.2.1, le_rfl⟩ hs.2
        rw [hRL] at h1
        exact ⟨sub_nonneg.mpr h1, sub_le_sub_left h2 Lzero⟩
      let k := fun s => (S.mu s p.2 - S.Q s p.2 ^ 2 / S.r s p.2 ^ 2) / (1 - S.mu s p.2)
      let ks := fun r => (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
      let electric := fun s => I * e * S.Q s p.2 * S.phi s p.2 /
        ((1 - S.mu s p.2) * S.r s p.2 : ℝ)
      let source := fun s => ((-S.nu s p.2 : ℝ) : ℂ) *
        (((1 / S.r s p.2 : ℝ) : ℂ) * Z s p.2 + ((k s / S.r s p.2 : ℝ) : ℂ) * Y s p.2 +
          (((k s - ks (S.r s p.2)) / S.r s p.2 : ℝ) : ℂ) * yStar (S.r s p.2) + electric s) -
        I * e * S.A s p.2 * yStar (S.r s p.2)
      have crs := hIn cr p hpR
      have cns := hIn cn p hpR
      have cls := hIn cl p hpR
      have cms := hIn cm p hpR
      have cqs := hIn cq p hpR
      have cas := hIn ca p hpR
      have cps := hIn cp p hpR
      have cys := h.static_continuous.1.comp crs (fun s hs => (hpath s hs).2)
      have cmss := h.static_continuous.2.comp crs (fun s hs => (hpath s hs).2)
      have hr0 (s) (hs : s ∈ Icc p.2 p.1) := (hrStar.trans_le (hrho.trans (hpath s hs).2.1)).ne'
      have hg0 (s) (hs : s ∈ Icc p.2 p.1) :=
        (hdelta.trans_le (h.box (s, p.2) (hpath s hs)).2.2.2).ne'
      have cmu : ContinuousOn (fun s => S.mu s p.2) (Icc p.2 p.1) :=
        (continuousOn_const.mul cms).div crs hr0
      have cmus : ContinuousOn (fun s => 2 * mStar (S.r s p.2) / S.r s p.2)
          (Icc p.2 p.1) :=
        (continuousOn_const.mul cmss).div crs hr0
      have ck : ContinuousOn k (Icc p.2 p.1) :=
        (cmu.sub ((cqs.pow 2).div (crs.pow 2) (fun s hs => pow_ne_zero 2 (hr0 s hs)))).div
          (continuousOn_const.sub cmu) hg0
      have cks : ContinuousOn (fun s => ks (S.r s p.2)) (Icc p.2 p.1) :=
        (cmus.sub (continuousOn_const.div (crs.pow 2) (fun s hs => pow_ne_zero 2 (hr0 s hs)))).div
          (continuousOn_const.sub cmus) (fun s hs =>
            (hdelta.trans_le (h.static_bounds (S.r s p.2) (hpath s hs).2).2.1).ne')
      have lift {f : ℝ → ℝ} (cf : ContinuousOn f (Icc p.2 p.1)) :=
        Complex.continuous_ofReal.comp_continuousOn cf
      have cElec : ContinuousOn electric (Icc p.2 p.1) :=
        (((lift cqs).const_mul (I * e)).mul cps).div
          (lift ((continuousOn_const.sub cmu).mul crs))
          (fun s hs => Complex.ofReal_ne_zero.mpr (mul_ne_zero (hg0 s hs) (hr0 s hs)))
      have cSource : ContinuousOn source (Icc p.2 p.1) :=
        ((lift cns.neg).mul
          (((((lift (continuousOn_const.div crs hr0)).mul (hIn cZ p hpR)).add
            ((lift (ck.div crs hr0)).mul (hIn cY p hpR))).add
            ((lift ((ck.sub cks).div crs hr0)).mul cys)).add cElec)).sub
          (((lift cas).const_mul (I * e)).mul cys)
      have hdY (s) (hs : s ∈ Ioo p.2 p.1) : HasDerivAt (fun u => Y u p.2)
          (-I * (e * S.A s p.2 : ℝ) * Y s p.2 + source s) s := by
        have hsm := Ioo_subset_Icc_self hs
        have hrLow := hanti p hpR hsm ⟨hpR.1.2.2.1, le_rfl⟩ hs.2
        have hrHigh := hanti p hpR ⟨le_rfl, hpR.1.2.2.1⟩ hsm hs.1
        change S.r p.1 p.2 < S.r s p.2 at hrLow
        change S.r s p.2 < S.r p.2 p.2 at hrHigh
        rw [hRL] at hrHigh
        have hyD := (h.static_equations (S.r s p.2) ⟨lt_of_le_of_lt hpR.2.1 hrLow, hrHigh⟩).1
        convert co_inner_y S e yStar ks (hr0 s hsm) (hl (s, p.2) (hpath s hsm)).ne'
          (hn (s, p.2) (hpath s hsm)).ne (hg0 s hsm)
          (h.equations (s, p.2) (hpath s hsm)).1
          (h.equations (s, p.2) (hpath s hsm)).2.2.2.1
          (h.equations (s, p.2) (hpath s hsm)).2.2.2.2.1 hyD using 1
        dsimp only [source, electric, k, Y, Z]
        push_cast
        field_simp [Complex.ofReal_ne_zero.mpr (hr0 s hsm)]
        ring
      have hy := Observation.inner_scalar_ray_of_source_bounds B Cz hB.le hCz.le
        (Y := fun s => Y s p.2) (Z := fun s => Z s p.2) (source := source)
        (h := fun s => S.xi s s / (S.nu s s : ℂ) - yStar Lzero)
        (connection := fun s => e * S.A s p.2) (depth := fun s => Lzero - S.r s p.2)
        (w := fun s => -S.nu s p.2) (etheta := etheta)
        hpR.1.2.1 hpR.1.2.2.1 hpR.1.2.2.2 hdp.1 h.errors.1 h.errors.2.2.2
        (hIn cY p hpR) cSource ((hIn ca p hpR).const_mul e) cns.neg cHb
        (cF.mono (Icc_subset_Icc le_rfl hdp.2)) (cN.mono (Icc_subset_Icc le_rfl hdp.2))
        (fun s hs => by
          simpa only [sub_eq_add_neg, add_comm, Pi.neg_apply] using
            ((h.equations (s, p.2) (hpath s hs)).1).neg.const_add Lzero)
        hdep (by simp only [hRL, sub_self]) rfl
        (fun s hs => ⟨hc.le.trans (h.box (s, p.2) (hpath s hs)).1.1,
          (h.box (s, p.2) (hpath s hs)).1.2⟩)
        (fun s _ => hNN s) h.trace
        (by simpa only [Y, hRL] using (h.boundary p.2 hv).2.1) hdY
        (fun s hs => hz (s, p.2) (hpath s hs))
        (fun s hs => by
          have hh := (hsrc (s, p.2) (hpath s hs)).2.2.1
          have hp' := hprof (s, p.2) (hpath s hs)
          simp only [Real.norm_eq_abs] at hp'
          exact hh.trans (mul_le_mul_of_nonneg_left
            (add_le_add (add_le_add (add_le_add le_rfl hp'.1) hp'.2) le_rfl)
            (mul_nonneg (hc.le.trans (h.box (s, p.2) (hpath s hs)).1.1) hB.le)))
      have hiGrow := intervalIntegral.integral_mono_interval (f := fun s => F s + N s)
        le_rfl hdp.1 hdpd
        (Filter.Eventually.of_forall (fun s => add_nonneg (hNN s).1 (hNN s).2))
        (((cF.add cN).mono (Icc_subset_Icc le_rfl hd.2)).intervalIntegrable_of_Icc
          (μ := volume) hd.1)
      have hdouble := Observation.inner_double_integral_le (f := fun s => F s + N s) hdp.1 hdpL
        ((cF.add cN).mono (Icc_subset_Icc le_rfl hdp.2))
        (fun s => add_nonneg (hNN s).1 (hNN s).2)
      have hXi := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt
          (div_le_div_of_nonneg_right hdpL (by norm_num : (0 : ℝ) ≤ 2)))
          h.errors.2.2.2) (mul_nonneg hB.le hCz.le)
      have hEta := mul_le_mul_of_nonneg_left hdpL
        (mul_nonneg (mul_nonneg hB.le (by positivity : 0 ≤ Cz + 1)) h.errors.1)
      have hDouble := mul_le_mul_of_nonneg_left hdouble (mul_nonneg hB.le hCz.le)
      have hGrow := mul_le_mul_of_nonneg_left hiGrow (by dsimp [J]; positivity : 0 ≤ J)
      have h1 := mul_le_mul_of_nonneg_right hCY1 h.errors.2.1
      have h2 := mul_le_mul_of_nonneg_right hCYX h.errors.2.2.2
      have h3 := mul_le_mul_of_nonneg_right hCYT h.errors.1
      have h4 := mul_le_mul_of_nonneg_right hCYJ (hI d hd.1)
      dsimp only [X, T, J] at h2 h3 h4 hGrow
      linarith only [hy, hXi, hEta, hDouble, hGrow, h1, h2, h3, h4]
    exact Real.sSup_le (by rintro _ ⟨p, hp, rfl⟩; exact hpoint p hp)
      (add_nonneg (mul_nonneg hCY.le (by linarith only [h.errors.2.1, h.errors.2.2.2, h.errors.1]))
        (mul_nonneg hCY.le (hI d hd.1)))
  constructor
  · have hh := hFbound 0 ⟨le_rfl, sub_nonneg.mpr hrhoL⟩
    rw [intervalIntegral.integral_same, mul_zero, add_zero] at hh
    have he := mul_le_mul (le_add_of_nonneg_right hCm.le)
      (show etheta + exi + eta ≤ etheta + em + exi + eta by linarith only [h.errors.2.2.1])
      (by linarith only [h.errors.2.1, h.errors.2.2.2, h.errors.1]) (by positivity : 0 ≤ CY + Cm)
    exact hh.trans he
  · intro d hd hstop
    have hm := hMass rho S D yStar mStar a b qStar eta em d hrho hrhoL h.errors.1 h.errors.2.2.1 hd
      h.compact cr cl ct cm cq h.static_continuous.1 h.static_continuous.2
      (fun s hs => (h.static_equations s hs).2)
      ⟨(a, a), h.boundary_mem a ⟨le_rfl, h.ordered⟩, (h.boundary a ⟨le_rfl, h.ordered⟩).1⟩
      h.triangles (fun p hp => (h.equations p hp).1) hn
      (fun p hp => ⟨(h.equations p hp).2.1, (h.equations p hp).2.2.1⟩)
      (fun p hp => ⟨hl p hp, (h.static_bounds (S.r p.1 p.2) hp.2).1,
        (h.static_bounds (S.r p.1 p.2) hp.2).2.2, (hsrc p hp).2.2.2⟩)
      (fun t ht => by
        have hb := h.boundary t ⟨ht.1.2.1, ht.1.2.2.2⟩
        exact ⟨hb.1, by simpa only [massComparison, hb.1] using hb.2.2⟩) hstop
    have hf := hFbound d hd
    change N d ≤ Cm * em + Cm * eta + Cm * ∫ s in 0..d, F s at hm
    have hi := intervalIntegral.integral_mono_on hd.1
      ((cF.mono (Icc_subset_Icc le_rfl hd.2)).intervalIntegrable_of_Icc (μ := volume) hd.1)
      (((cF.add cN).mono (Icc_subset_Icc le_rfl hd.2)).intervalIntegrable_of_Icc (μ := volume) hd.1)
      (fun s _ => le_add_of_nonneg_right (hNN s).2)
    simp only [Pi.add_apply] at hi
    change (∫ s in 0..d, F s) ≤ ∫ s in 0..d, F s + N s at hi
    have hi' := mul_le_mul_of_nonneg_left hi hCm.le
    have h1 := mul_nonneg hCY.le h.errors.2.2.1
    have h2 := mul_nonneg hCm.le (add_nonneg h.errors.2.1 h.errors.2.2.2)
    change F d + N d ≤ (CY + Cm) * (etheta + em + exi + eta) +
      (CY + Cm) * ∫ s in 0..d, F s + N s
    linarith only [hm, hf, hi', h1, h2]

/-- [internal]
Remove the scalar stop on the entire actual inner region through each
selected member's own cutoff `rho`. Constants are fixed after the common
annulus, primitive/reference bounds and the three outer boundary-error
coefficients, before `rho`, fields, background, coupling and errors.
The boundary coefficients are the outgoing outer comparison, mass outer
comparison and transferred clock L² trace; no inner estimate is a premise.
The actual coupled Volterra inequality is derived and discharged here. -/
theorem Observation.inner_comparison_closure_of_normalization
    (hrStar : 0 < rStar) (hLzero : rStar ≤ Lzero) (hdelta : 0 < delta) (hc : 0 < c)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hQmax : 0 ≤ Qmax) (hCs : 0 ≤ Cscalar)
    (hBq : 0 ≤ Bcharge) (hAm : 0 ≤ Amax)
    (Ctheta Cmass Cxi : ℝ) (hCt : 0 ≤ Ctheta) (hCm : 0 ≤ Cmass) (hCx : 0 ≤ Cxi) :
    ∃ C > 0, ∃ sigma > 0,
    ∀ (rho : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ)
      (yStar : ℝ → ℂ) (mStar : ℝ → ℝ) (a b qStar e epsilon eta : ℝ),
    let R := sidewaysTruncation S D a b rho Lzero
    let Y := fun u v => S.theta u v / (S.lam u v : ℂ) - yStar (S.r u v)
    let F := fun d => sSup ((fun p : ℝ × ℝ => ‖Y p.1 p.2‖) ''
      sidewaysTruncation S D a b (Lzero - d) Lzero)
    let N := fun d => sSup ((fun p : ℝ × ℝ => ‖massComparison S mStar p.1 p.2‖) ''
      sidewaysTruncation S D a b (Lzero - d) Lzero)
    rStar ≤ rho → rho ≤ Lzero → 0 ≤ epsilon →
    Observation.InnerComparisonData rho Lzero delta c K G Qmax Cscalar Bcharge Amax
      S D H yStar mStar a b qStar e eta (Ctheta * (epsilon + eta))
        (Cmass * (epsilon + eta)) (Cxi * (epsilon + eta)) →
    epsilon + eta ≤ sigma →
    (∀ d ∈ Icc 0 (Lzero - rho), F d + N d ≤ C * (epsilon + eta) ∧ F d < 1) ∧
    ∀ p ∈ R, ‖Y p.1 p.2‖ + |massComparison S mStar p.1 p.2| ≤ C * (epsilon + eta) := by
  obtain ⟨C1, hC1, hcoupled⟩ := Observation.inner_coupled_volterra_of_normalization
    hrStar hLzero hdelta hc hK hG hQmax hCs hBq hAm
  let A := C1 * (Ctheta + Cmass + Cxi + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨C, hC, sigma, hsigma, hclose⟩ := Observation.inner_comparison_closure_of_volterra
    A C1 Lzero hA hC1.le (hrStar.trans_le hLzero).le
  refine ⟨C, hC, sigma, hsigma, ?_⟩
  intro rho S D H yStar mStar a b qStar e epsilon eta
  dsimp only
  intro hrho hrhoL hepsilon h hsmall
  let Y := fun u v => S.theta u v / (S.lam u v : ℂ) - yStar (S.r u v)
  let F := fun d => sSup ((fun p : ℝ × ℝ => ‖Y p.1 p.2‖) ''
    sidewaysTruncation S D a b (Lzero - d) Lzero)
  let N := fun d => sSup ((fun p : ℝ × ℝ => ‖massComparison S mStar p.1 p.2‖) ''
    sidewaysTruncation S D a b (Lzero - d) Lzero)
  rcases Observation.inner_depth_profiles_of_normalization hc h with ⟨_cY, _cZ, cF, cN, hNN, hprof⟩
  have hv := hcoupled rho S D H yStar mStar a b qStar e eta
    (Ctheta * (epsilon + eta)) (Cmass * (epsilon + eta)) (Cxi * (epsilon + eta)) hrho hrhoL h
  have hforcing : C1 * (Ctheta * (epsilon + eta) + Cmass * (epsilon + eta) +
      Cxi * (epsilon + eta) + eta) ≤ A * (epsilon + eta) := by
    have hh := mul_nonneg hC1.le hepsilon
    dsimp only [A]
    nlinarith only [hh]
  have hg := hclose epsilon eta (Lzero - rho) F N hepsilon h.errors.1
    (sub_nonneg.mpr hrhoL) (by linarith only [hrho, hrStar]) hsmall cF cN
    (fun s _ => (hNN s).1) (fun s _ => (hNN s).2) (hv.1.trans hforcing)
    (fun d hd hstop => (hv.2 d hd hstop).trans (add_le_add hforcing le_rfl))
  refine ⟨hg, ?_⟩
  intro p hp
  have hd : Lzero - S.r p.1 p.2 ∈ Icc 0 (Lzero - rho) :=
    ⟨sub_nonneg.mpr hp.2.2, sub_le_sub_left hp.2.1 Lzero⟩
  have hm : |massComparison S mStar p.1 p.2| ≤ N (Lzero - S.r p.1 p.2) := by
    simpa only [N, Real.norm_eq_abs] using (hprof p hp).2
  exact (add_le_add (hprof p hp).1 hm).trans (hg _ hd).1

end EmcsfAcExtension.Global
