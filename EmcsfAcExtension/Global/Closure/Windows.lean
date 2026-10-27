module

public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Closure.Profiles
public import EmcsfAcExtension.Global.Closure.CutoffContinuity
public import EmcsfAcExtension.Global.Closure.Parameters
public import EmcsfAcExtension.Frozen.Triangle
public import EmcsfAcExtension.Frozen.OutSeg
public import EmcsfAcExtension.Frozen.Fields.Mu
public import EmcsfAcExtension.Frozen.Fields.NormalizedOut
import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Global.Observation.CylinderClock
import EmcsfAcExtension.Global.Closure.Stages
import EmcsfAcExtension.Global.Closure.ParametersProper
import EmcsfAcExtension.Global.Closure.Continuation
public import EmcsfAcExtension.Global.Closure.Optics
import EmcsfAcExtension.Global.Closure.Clock
import EmcsfAcExtension.Global.Gap.LateMain
import EmcsfAcExtension.Global.Terminal.OpticalUpper
import Mathlib.Tactic

/-! # Charged scale and literal finite stopping

The logarithmic background is reexported from `Optics`. It supplies charged
smallness uniformly on every finite weakly stopped exterior. Compact
extrema connect the literal stops to cutoff continuity; the actual-clock
identity connects their variation with restricted finite-stage budgets.
The enclosing-triangle lemmas are exported from `CutoffContinuity`.
Source: `charged_SF_new_version.tex:L4086–L4102` and internal project record (O1)–(O2).
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
For each fixed development, the logarithmic amplitude coefficient is
chosen before the observation tolerance and entry row. At every sufficiently
late entry, all finite weakly stopped exteriors satisfy the actual charged
observation condition uniformly in stages, duration, radius and boundary
point. The amplitude is derived from the actual incoming envelope and its
stop; no scalar profile or scalar translation is an input.
Source: charged_SF_new_version.tex:L4086–L4091. -/
theorem observation_physical_scale (ui e c F Jstop : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S)
    (hc : 0 < c) (hF : 0 ≤ F) (hF1 : F < 1) (hJstop : 0 ≤ Jstop) :
    ∃ C > 0, 1 ≤ C ∧ ∀ η > 0, ∀ᶠ a in 𝓝[<] (0 : ℝ),
      ∀ (b v₀ ρ δ Λ ε : ℝ) (vb : ℝ → ℝ) (N : ℕ)
        (_B : FiniteBoundary S ui a b v₀ ρ vb N),
      ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε →
      (∀ u ∈ Icc a b, S.r a 0 / 2 ≤ S.r u 0) →
      (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal ≤ Jstop →
      let M := C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r a 0)))
      1 ≤ M ∧ ∀ u ∈ Icc a b, ∀ v ∈ Icc (vb u) 0, ∀ r ∈ Icc 0 (S.r a 0),
        ‖S.phi u v‖ ≤ M ∧ |e| * r * (1 + ‖S.a u v‖) < η := by
  obtain ⟨C, hC, hC1, hamp⟩ := amplitude_scale ui e c F Jstop S h hs hc hF hF1 hJstop
  refine ⟨C, hC, hC1, ?_⟩
  intro η hη
  have hηsq : 0 < (η / 3) ^ 2 := sq_pos_of_pos (div_pos hη (by norm_num))
  have hsmall := (cc_zeta ui e S h hs C).eventually (Iio_mem_nhds hηsq)
  filter_upwards [Ioo_mem_nhdsLT h.ui_neg, hsmall] with a ha hζ
  intro b v₀ ρ δ Λ ε vb N B hstop hhalf hJ
  dsimp only
  have ha' : a ∈ Ico ui 0 := ⟨ha.1.le, ha.2⟩
  let M := C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r a 0)))
  have hM : 1 ≤ M := (hamp a ha').1
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  refine ⟨hM, ?_⟩
  have hR : 0 < S.r a 0 := h.solution.r_pos (a, 0)
    ⟨ha.1.le, ha.2, ha.2.le, le_rfl⟩ ha.2
  have hζeq : (|e| * M * S.r a 0) ^ 2 = e ^ 2 * M ^ 2 * S.r a 0 ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
  have hbound : 3 * (|e| * M * S.r a 0) < η := by
    have hh : |e| * M * S.r a 0 < η / 3 := by
      apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
      rwa [hζeq]
    linarith only [hh]
  obtain ⟨_, hg, hg0, hmajor, hint, _⟩ := incoming_envelope h B
  let g := fun v => (incomingEnvelope e S (exteriorDomain ui a b vb) a v).toReal
  intro u hu v hv r hr
  have hb0 := (B.mem u hu).2.2.2
  have hv₀ : v₀ ≤ vb u := by
    rw [← B.entry_label]
    exact B.mono ⟨le_rfl, hu.1.trans hu.2⟩ hu hu.1
  have hgfull : IntervalIntegrable g volume v₀ 0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hv₀.trans hb0)).mpr hg
  have hgrow : IntervalIntegrable g volume (vb u) 0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hb0).mpr
      (hg.mono_set (Icc_subset_Icc hv₀ le_rfl))
  have hm : ∀ᵐ x ∂volume.restrict (Icc (vb u) 0), ‖weightedJ S u x‖ ≤ g x := by
    have hm := hmajor.filter_mono (ae_mono
      (Measure.restrict_mono (Icc_subset_Icc hv₀ le_rfl) le_rfl))
    filter_upwards [hm, ae_restrict_mem measurableSet_Icc] with x hx hxm
    exact (hx u hu hxm.1).2
  have hj : (∫ x in vb u..0, g x) ≤ Jstop := by
    apply le_trans (intervalIntegral.integral_mono_interval hv₀ hb0 le_rfl
      (Eventually.of_forall hg0) hgfull)
    exact hint.trans_le hJ
  have hrow (x : ℝ) (hx : x ∈ Icc (vb u) 0) :
      (u, x) ∈ exteriorDomain ui a b vb := by
    exact ⟨⟨(B.mem u hu).1, (B.mem u hu).2.1,
      (B.off_axis u hu).le.trans hx.1, hx.2⟩, hu.1, hu.2, hx.1⟩
  have hp : ‖S.phi u v‖ ≤ M :=
    ((hamp a ha').2 u ⟨(B.mem u hu).1, (B.mem u hu).2.1⟩ (hhalf u hu)).2
      (vb u) (B.off_axis u hu) hb0
      (fun x hx => (hstop (u, x) (hrow x hx)).2.2.1)
      (fun x hx => (hstop (u, x) (hrow x hx)).2.2.2.2.1) g hgrow hm hj v hv
  exact ⟨hp, (observation_physical_scale_of_profile hr.1 hr.2 hM hF1.le hp
    (hstop (u, v) (hrow v hv)).2.2.2.2.1).2.trans_lt hbound⟩

/-- [internal]
Connect the literal weak and strict cutoff predicates to five continuous
residuals. The extrema are attained on each proper compact exterior,
including the singleton incoming entry interval. The independent gap,
charge and global expansion upper bounds are retained as fixed geometry.
Strict improvement is an input of this helper and precedes continuation.
There are no estimate constants. Source: charged_SF_new_version.tex:L4104–L4106. -/
theorem finite_stopping_continuation_of_continuity {ui e a b v₀ ρ R₀ : ℝ}
    {S : Fields} (h : OriginalData ui e S) {vb J Svar : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) {δ c Λ F ε εstop : ℝ}
    (hJ : ContinuousOn J (Icc a b)) (hSvar : ContinuousOn Svar (Icc a b))
    (hfixed : ∀ p ∈ exteriorDomain ui a b vb,
      0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2 ∧ S.lam p.1 p.2 ≤ Λ ∧
        S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 / 2)
    (hentry : StrictFiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F ε εstop a)
    (himprove : ∀ t ∈ Icc a b,
      FiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F ε εstop t →
        StrictFiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F ε εstop t) :
    ∀ t ∈ Icc a b, StrictFiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F ε εstop t := by
  have hab : a ≤ b := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hia := (B.mem a ⟨le_rfl, hab⟩).1
  have hb := (B.mem b ⟨hab, le_rfl⟩).2.1
  have hproper (u : ℝ) (hu : u ∈ Icc a b) : u < vb u ∧ vb u ≤ 0 :=
    ⟨B.off_axis u hu, (B.mem u hu).2.2.2⟩
  let K := exteriorDomain ui a b vb
  have hr (p : ℝ × ℝ) (hp : p ∈ K) : 0 < S.r p.1 p.2 :=
    h.solution.r_pos p hp.1 ((B.off_axis p.1 ⟨hp.2.1, hp.2.2.1⟩).trans_le hp.2.2.2)
  have cl := h.solution.cont_lam.mono (show K ⊆ origDomain ui from fun _ hp => hp.1)
  have ct := h.solution.cont_theta.mono (show K ⊆ origDomain ui from fun _ hp => hp.1)
  have cm := h.solution.cont_m.mono (show K ⊆ origDomain ui from fun _ hp => hp.1)
  have cr := h.solution.cont_r.mono (show K ⊆ origDomain ui from fun _ hp => hp.1)
  have cμ : ContinuousOn (fun p : ℝ × ℝ => S.mu p.1 p.2) K :=
    (continuousOn_const.mul cm).div cr (fun p hp => (hr p hp).ne')
  have cy := (ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun p hp => Complex.ofReal_ne_zero.mpr (h.solution.lam_pos p hp.1).ne')).norm
  have cq := cμ.div (continuousOn_const.sub cμ)
    (fun p hp => (h.solution.one_sub_mu_pos p hp.1).ne')
  have ce {f : ℝ × ℝ → ℝ} (cf : ContinuousOn f K) :=
    continuousOn_exterior_extrema hab hia hb B.cont B.mono hproper cf
  have cR : ContinuousOn (fun t => S.r t 0) (Icc a b) :=
    h.solution.cont_r.comp (continuousOn_id.prodMk continuousOn_const)
      (fun u hu => ⟨(B.mem u hu).1, (B.mem u hu).2.1, (B.mem u hu).2.1.le, le_rfl⟩)
  let f : Fin 5 → ℝ → ℝ := ![
    (fun t => c - sInf ((Function.uncurry S.lam) '' exteriorDomain ui a t vb)),
    (fun t => R₀ / 2 - S.r t 0),
    (fun t => sSup ((fun p : ℝ × ℝ =>
      ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖) '' exteriorDomain ui a t vb) - F),
    (fun t => sSup ((fun p : ℝ × ℝ =>
      S.mu p.1 p.2 / (1 - S.mu p.1 p.2)) '' exteriorDomain ui a t vb) - ε),
    (fun t => J t + Svar t - εstop)]
  have hf : ∀ i, ContinuousOn (f i) (Icc a b) := by
    intro i
    fin_cases i
    · exact continuousOn_const.sub (ce cl).2
    · exact continuousOn_const.sub cR
    · exact (ce cy).1.sub continuousOn_const
    · exact (ce cq).1.sub continuousOn_const
    · exact (hJ.add hSvar).sub continuousOn_const
  have hchar (t : ℝ) (ht : t ∈ Icc a b) :
      (FiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F ε εstop t ↔ ∀ i, f i t ≤ 0) ∧
      (StrictFiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F ε εstop t ↔ ∀ i, f i t < 0) := by
    let Kt := exteriorDomain ui a t vb
    have hsub : Kt ⊆ K := fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1.trans ht.2, hp.2.2.2⟩
    have hKt : IsCompact Kt := isCompact_exteriorDomain ht.1 hia (ht.2.trans_lt hb)
      (B.cont.mono (Icc_subset_Icc le_rfl ht.2))
      (B.mono.mono (Icc_subset_Icc le_rfl ht.2))
      (fun u hu => hproper u ⟨hu.1, hu.2.trans ht.2⟩)
    have hne : Kt.Nonempty := ⟨(a, vb a), B.mem a ⟨le_rfl, hab⟩, le_rfl, ht.1, le_rfl⟩
    have hl := compact_extrema_bounds hKt hne (cl.mono hsub) c
    have hy := compact_extrema_bounds hKt hne (cy.mono hsub) F
    have hq := compact_extrema_bounds hKt hne (cq.mono hsub) ε
    have hrad (u : ℝ) (hu : u ∈ Icc a t) : S.r t 0 ≤ S.r u 0 :=
      (Terminal.terminal_radius_strictAntiOn h.solution).antitoneOn
        ⟨hia.trans hu.1, hu.2.trans_lt (ht.2.trans_lt hb)⟩
        ⟨hia.trans ht.1, ht.2.trans_lt hb⟩ hu.2
    have hweak_fields : ExteriorStops S Kt δ c Λ F ε ↔
        c ≤ sInf ((Function.uncurry S.lam) '' Kt) ∧
        sSup ((fun p : ℝ × ℝ => ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖) '' Kt) ≤ F ∧
        sSup ((fun p : ℝ × ℝ => S.mu p.1 p.2 / (1 - S.mu p.1 p.2)) '' Kt) ≤ ε := by
      constructor
      · intro hs
        exact ⟨hl.2.2.1.mpr (fun p hp => (hs p hp).2.2.1),
          hy.1.mpr (fun p hp => (hs p hp).2.2.2.2.1),
          hq.1.mpr (fun p hp => (hs p hp).2.2.2.2.2.1)⟩
      · rintro ⟨hl', hy', hq'⟩ p hp
        have hh := hfixed p (hsub hp)
        exact ⟨hh.1, hh.2.1, hl.2.2.1.mp hl' p hp, hh.2.2.1,
          hy.1.mp hy' p hp, hq.1.mp hq' p hp, hh.2.2.2⟩
    have hstrict_fields :
        (∀ p ∈ Kt, c < S.lam p.1 p.2 ∧
          ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ < F ∧
          S.mu p.1 p.2 / (1 - S.mu p.1 p.2) < ε) ↔
        c < sInf ((Function.uncurry S.lam) '' Kt) ∧
        sSup ((fun p : ℝ × ℝ => ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖) '' Kt) < F ∧
        sSup ((fun p : ℝ × ℝ => S.mu p.1 p.2 / (1 - S.mu p.1 p.2)) '' Kt) < ε := by
      constructor
      · intro hs
        exact ⟨hl.2.2.2.mpr (fun p hp => (hs p hp).1),
          hy.2.1.mpr (fun p hp => (hs p hp).2.1), hq.2.1.mpr (fun p hp => (hs p hp).2.2)⟩
      · rintro ⟨hl', hy', hq'⟩ p hp
        exact ⟨hl.2.2.2.mp hl' p hp, hy.2.1.mp hy' p hp, hq.2.1.mp hq' p hp⟩
    have hwR : (∀ u ∈ Icc a t, R₀ / 2 ≤ S.r u 0) ↔ R₀ / 2 ≤ S.r t 0 :=
      ⟨fun hs => hs t ⟨ht.1, le_rfl⟩, fun hs u hu => hs.trans (hrad u hu)⟩
    have hsR : (∀ u ∈ Icc a t, R₀ / 2 < S.r u 0) ↔ R₀ / 2 < S.r t 0 :=
      ⟨fun hs => hs t ⟨ht.1, le_rfl⟩, fun hs u hu => hs.trans_le (hrad u hu)⟩
    have hfw : (∀ i, f i t ≤ 0) ↔
        c ≤ sInf ((Function.uncurry S.lam) '' Kt) ∧ R₀ / 2 ≤ S.r t 0 ∧
        sSup ((fun p : ℝ × ℝ => ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖) '' Kt) ≤ F ∧
        sSup ((fun p : ℝ × ℝ => S.mu p.1 p.2 / (1 - S.mu p.1 p.2)) '' Kt) ≤ ε ∧
        J t + Svar t ≤ εstop := by
      simp only [f, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.forall_fin_zero, and_true, sub_nonpos]
      rfl
    have hfs : (∀ i, f i t < 0) ↔
        c < sInf ((Function.uncurry S.lam) '' Kt) ∧ R₀ / 2 < S.r t 0 ∧
        sSup ((fun p : ℝ × ℝ => ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖) '' Kt) < F ∧
        sSup ((fun p : ℝ × ℝ => S.mu p.1 p.2 / (1 - S.mu p.1 p.2)) '' Kt) < ε ∧
        J t + Svar t < εstop := by
      simp only [f, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.forall_fin_zero, and_true, sub_neg]
      rfl
    constructor
    · rw [FiniteCutoffStops, hweak_fields, hwR, hfw]
      exact ⟨fun hs => ⟨hs.1.1, hs.2.1, hs.1.2.1, hs.1.2.2, hs.2.2⟩,
        fun hs => ⟨⟨hs.1, hs.2.2.1, hs.2.2.2.1⟩, hs.2.1, hs.2.2.2.2⟩⟩
    · rw [StrictFiniteCutoffStops, hweak_fields, hstrict_fields, hsR, hfs]
      constructor
      · intro hs
        exact ⟨hs.2.1.1, hs.2.2.1, hs.2.1.2.1, hs.2.1.2.2, hs.2.2.2⟩
      · rintro ⟨hl', hR', hy', hq', hbudget⟩
        exact ⟨⟨hl'.le, hy'.le, hq'.le⟩, ⟨hl', hy', hq'⟩, hR', hbudget⟩
  exact finite_stopping_continuation_of_estimates hab f hf
    (fun t ht => (hchar t ht).1) (fun t ht => (hchar t ht).2) hentry himprove

/-- [internal]
Apply the literal first-failure argument to the actual incoming envelope
and actual clipped cylinder variations of a finite available path. Their
continuity is proved by `finite_cutoff_continuity`; no continuity or
extremum characterization is left as an assumption. This helper retains
the independent geometric bounds and the finite strict-improvement task.
Constants: none. Source: charged_SF_new_version.tex:L4104–L4106. -/
theorem actual_finite_stopping_continuation_of_estimates {ui e a b v₀ ρ R₀ : ℝ}
    {S : Fields} (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ)
    (hT : ∀ n, 0 ≤ T n)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
    (hgraph : ∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ)
    (δ c Λ F ε εstop : ℝ)
    (hfixed : ∀ p ∈ exteriorDomain ui a b vb,
      0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2 ∧ S.lam p.1 p.2 ≤ Λ ∧
        S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 / 2) :
    let J := fun t => (interactionNorm e S (exteriorDomain ui a t vb) a v₀).toReal
    let Svar := fun t => ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
      (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) t)))).toReal
    StrictFiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F ε εstop a →
    (∀ t ∈ Icc a b, FiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F ε εstop t →
      StrictFiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F ε εstop t) →
    ∀ t ∈ Icc a b, StrictFiniteCutoffStops S ui a R₀ vb J Svar δ c Λ F ε εstop t := by
  dsimp only
  intro hentry himprove
  obtain ⟨hJ, hSvar, _⟩ := finite_cutoff_continuity h B T hT γ hends hgraph
  exact finite_stopping_continuation_of_continuity h B hJ hSvar hfixed hentry himprove

/-- [node sec:charged-closure#entry-stop-initialization]
Choose the weak stops and every strict entry margin on the same proper
`ell,V` family. The development and the two fixed observation thresholds
precede the profile and stopping bounds; all stopping, energy, clock and
charged-error tolerances precede the eventual entry row. Proper roots,
radius-variable limits and the real initial-density limit are retained.
The incoming norm in the initial stop is the actual source envelope.
Source: charged_SF_new_version.tex:L3854–L3898; approved internal project record (E1). -/
theorem proper_entry_stop_initialization (ui e ηobs ηcool : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S)
    (ho : 0 < ηobs) (hh : 0 < ηcool) :
    ∃ ell V : ℝ → ℝ, ∃ a ∈ Ioo ui 0, ∃ c Λ F ε : ℝ,
      0 < c ∧ 0 < Λ ∧ c ≤ Λ ∧ 0 < F ∧ 0 < ε ∧
      (∀ p ∈ origDomain ui, S.lam p.1 p.2 ≤ Λ) ∧
      (∀ u ∈ Ico a 0, u < V u ∧ V u < 0 ∧
        S.r u (V u) = ell (S.r u 0) ∧
        0 < ell (S.r u 0) ∧ ell (S.r u 0) < S.r u 0) ∧
      0 < S.r a 0 ∧
      (∀ R ∈ Ioo 0 (S.r a 0), 0 < ell R ∧ ell R < R) ∧
      Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0) ∧
      (∃ b ∈ Ioo a 0, ∀ p ∈ adaptiveExterior S ui b ell, 2 * c < S.lam p.1 p.2) ∧
      (∀ ρ : ℝ, 0 < ρ ∧ ρ < 1 → ExteriorBox (gapConstant / 2) c Λ F ε ρ) ∧
      (∀ μ x : ℝ, 0 ≤ μ → μ < 1 → μ / (1 - μ) ≤ ε →
        x ≤ F → μ + x < ηobs ∧ μ + x < ηcool) ∧
      Tendsto (fun u => ∫ v in V u..0, ‖weightedJ S u v‖) (𝓝[<] 0) (𝓝 0) ∧
      ∀ (εstop εentry H ρ χ C η : ℝ),
        0 < εstop → 0 < εentry → εentry ≤ 1 → 0 ≤ H →
        0 < ρ → ρ < χ → 0 < η → ∀ᶠ u₀ in 𝓝[<] (0 : ℝ),
          u₀ ∈ Ioo a 0 ∧ ell (S.r u₀ 0) < S.r u₀ 0 / 2 ∧
          StrictFiniteCutoffStops S ui u₀ (S.r u₀ 0) V
            (fun t => (interactionNorm e S (exteriorDomain ui u₀ t V) u₀ (V u₀)).toReal)
            (fun _ => 0) (gapConstant / 2) c Λ F ε εstop u₀ ∧
          (∀ v ∈ Icc (V u₀) 0, 2 * c ≤ S.lam u₀ v) ∧
          cylinderEnergy S (ell (S.r u₀ 0)) u₀ (V u₀) / ell (S.r u₀ 0) ≤ εentry ∧
          2 * (H * ell (S.r u₀ 0) / (εentry * (1 - ρ / χ)) + ell (S.r u₀ 0)) <
            S.r u₀ 0 / 4 ∧
          e ^ 2 * (C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u₀ 0)))) ^ 2 *
            S.r u₀ 0 ^ 2 < η := by
  obtain ⟨ell, V, a, ha, c, Λ, F, ε, hc, hΛ, hcΛ, hF, hε, hupper, hroot,
    hRa, hproper, hsmallRadius, hadaptive, hbox, hweak, hD, hratio, henergy, hfields⟩ :=
    fixed_stopping_parameters_proper ui e ηobs ηcool S h hs ho hh
  obtain ⟨b, hb, hgap⟩ := Gap.late_from_terminal ui e S h hs
  refine ⟨ell, V, a, ha, c, Λ, F, ε, hc, hΛ, hcΛ, hF, hε, hupper,
    hroot, hRa, hproper, hsmallRadius, hadaptive, hbox, hweak, hD, ?_⟩
  intro εstop εentry H ρ χ C η hstop he he1 hH hρ hρχ hη
  have hχ : 0 < χ := hρ.trans hρχ
  have hg : 0 < 1 - ρ / χ := sub_pos.mpr ((div_lt_one hχ).mpr hρχ)
  have hA : 0 < 1 / (16 * (H / (1 - ρ / χ) + 1)) := by positivity
  filter_upwards [Ioo_mem_nhdsLT ha.2, Ioo_mem_nhdsLT hb.2,
    hfields F hF ε hε, hD.eventually (Iio_mem_nhds hstop),
    henergy.eventually (Iic_mem_nhds he),
    (hratio εentry he).eventually (Iio_mem_nhds hA),
    (cc_zeta ui e S h hs C).eventually (Iio_mem_nhds hη)]
      with u₀ hua hub hfield hD₀ hE hratio₀ hZ
  have hu : u₀ ∈ Ico a 0 := ⟨hua.1.le, hua.2⟩
  have hui : ui ≤ u₀ := ha.1.le.trans hua.1.le
  have hv := hroot u₀ hu
  have hR : 0 < S.r u₀ 0 := h.solution.r_pos (u₀, 0)
    ⟨hui, hua.2, hua.2.le, le_rfl⟩ hua.2
  have hB := hv.2.2.2.1
  have hclock := clock_loss_lt_of_entry_ratio hH ⟨hρ, hρχ⟩ ⟨he, he1⟩ hB.le hR hratio₀
  have hclock0 : 0 ≤ H * ell (S.r u₀ 0) / (εentry * (1 - ρ / χ)) := by positivity
  have hrow : outSeg u₀ (V u₀) 0 ⊆ origDomain ui := by
    rintro ⟨u, v⟩ ⟨rfl, hvl, hvr⟩
    exact ⟨hui, hua.2, hv.1.le.trans hvl, hvr⟩
  have hDreal := initialInteraction_eq h.solution hv.1 hv.2.1.le hrow
  have hJreal :
      (interactionNorm e S (exteriorDomain ui u₀ u₀ V) u₀ (V u₀)).toReal =
        ∫ v in V u₀..0, ‖weightedJ S u₀ v‖ := by
    rw [interactionNorm_initial_cutoff, hDreal, ENNReal.toReal_ofReal]
    exact intervalIntegral.integral_nonneg hv.2.1.le (fun _ _ => norm_nonneg _)
  have hstopFields : ExteriorStops S (exteriorDomain ui u₀ u₀ V)
      (gapConstant / 2) c Λ F ε := by
    intro p hp
    have heq : p.1 = u₀ := le_antisymm hp.2.2.1 hp.2.1
    have hh' := hfield p.2 ⟨by simpa only [heq] using hp.2.2.2, hp.1.2.2.2⟩
    have hlate := hgap p hp.1 (by simpa only [heq] using hub.1.le)
    have hlc : c < S.lam u₀ p.2 := by linarith only [hh'.1, hc]
    simpa only [heq] using
      And.intro (by simpa only [heq] using (h.mu p hp.1).1)
        ⟨by simpa only [heq] using hlate.1, hlc.le, hh'.2.1, hh'.2.2.1.le,
          hh'.2.2.2.le, by simpa only [heq] using hlate.2⟩
  refine ⟨hua, by linarith only [hclock, hclock0, hR], ?_,
    fun v hv' => (hfield v hv').1.le, hE, hclock, hZ⟩
  refine ⟨hstopFields, ?_, ?_, ?_⟩
  · intro p hp
    have heq : p.1 = u₀ := le_antisymm hp.2.2.1 hp.2.1
    have hh' := hfield p.2 ⟨by simpa only [heq] using hp.2.2.2, hp.1.2.2.2⟩
    have hlc : c < S.lam u₀ p.2 := by linarith only [hh'.1, hc]
    simpa only [heq] using And.intro hlc ⟨hh'.2.2.1, hh'.2.2.2⟩
  · intro u hu'
    have heq : u = u₀ := le_antisymm hu'.2 hu'.1
    simpa only [heq] using half_lt_self hR
  · simpa only [hJreal, add_zero] using hD₀

/-- [internal]
Append an available current cylinder capped at the prescribed clock or at
the proper terminal row. Previous cuts, radii and cooling endpoints agree
exactly. The current connector has zero length, so this is a partial-stage
construction before the full endpoint and connector are justified. The
alternative terminal row is retained for contradiction by strict stops.
Constants: none. Source: charged_SF_new_version.tex:L3899–L3907, L4104–L4106. -/
theorem capped_boundary_append {ui e u₀ a v₀ ρ R Rmin T : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui u₀ a v₀ ρ vb N)
    (hia : ui < a) (hρ : 0 < ρ ∧ ρ < 1) (hR : 0 < R)
    (hRmin : R < Rmin) (hstart : S.r a (vb a) = R)
    (hterminal : Rmin < S.r a 0) (hv : vb a < 0) (hT : 0 < T) :
    ∃ W : ℝ → ℝ, ∃ b ∈ Ioo a 0, ∃ t : ℝ, 0 < t ∧ t ≤ T ∧
      ∃ γ : ClockCylinder S (origDomain ui) R 0 t,
      ∃ vb' : ℝ → ℝ,
      ∃ B' : FiniteBoundary S ui u₀ (γ.U t) v₀ ρ vb' (N + 1),
        γ.U 0 = a ∧ γ.V 0 = vb a ∧
        (∀ u ∈ Icc u₀ a, vb' u = vb u) ∧
        (∀ i : Fin (N + 1), B'.cuts i.castSucc = B.cuts i) ∧
        (∀ i : Fin N, B'.cool i.castSucc = B.cool i ∧ B'.radii i.castSucc = B.radii i) ∧
        B'.cool (Fin.last N) = γ.U t ∧ B'.radii (Fin.last N) = R ∧
        (∀ u ∈ Icc a (γ.U t), vb' u = W u) ∧
        (∀ τ ∈ Icc 0 t, vb' (γ.U τ) = γ.V τ) ∧
        (∀ u ∈ Icc a (γ.U t), Rmin ≤ S.r u 0) ∧
        S.r b 0 = Rmin ∧ (t = T ∨ γ.U t = b) := by
  have hcut : u₀ ≤ a := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  obtain ⟨W, b, hb, t, ht, htT, γ, hU, hV, hWa, hend, hW, hWmono, hWr,
    hWrate, hgraph, hretained, hRb, halt⟩ := capped_clock_cylinder h hia
      (B.off_axis a ⟨hcut, le_rfl⟩) hv hR hRmin hstart hterminal hT
  have hsub : Icc a (γ.U t) ⊆ Icc a b := Icc_subset_Icc le_rfl hend.2
  have hrate (u : ℝ) (hu : u ∈ Ioo a (γ.U t)) :
      HasDerivAt W (-S.nu u (W u) / S.lam u (W u)) u :=
    (hWrate u (hsub (Ioo_subset_Icc_self hu))).hasDerivAt
      (Icc_mem_nhds hu.1 (hu.2.trans_le hend.2))
  obtain ⟨vb', B', hold, hcuts, hstages, hcool, hradii, hcyl, _hcon⟩ :=
    appendBoundary_of_levelGraph (W := W) (c := γ.U t) (u₂ := γ.U t)
      B hend.1.le le_rfl hR hWa (hW.mono hsub)
      (hWmono.monotoneOn.mono hsub)
      (fun u hu => ⟨⟨hia.le.trans hu.1, (hu.2.trans hend.2).trans_lt hb.2,
        (hWr u (hsub hu)).1.le, (hWr u (hsub hu)).2.1.le⟩,
        (hWr u (hsub hu)).1⟩)
      (fun u hu => (hWr u (hsub hu)).2.2) hrate (by
        intro u hu
        have heq : u = γ.U t := le_antisymm hu.2 hu.1
        rw [heq, (hWr (γ.U t) ⟨hend.1.le, hend.2⟩).2.2]
        exact ⟨mul_le_of_le_one_left hR.le hρ.2.le, le_rfl⟩)
      (hWr (γ.U t) ⟨hend.1.le, hend.2⟩).1
  refine ⟨W, b, hb, t, ht, htT, γ, vb', B', hU, hV, hold, hcuts, hstages,
    hcool, hradii, hcyl, ?_, (fun u hu => hretained u (hsub hu)), hRb, halt⟩
  intro τ hτ
  have hmono := (γ.strictMonoOn_U h.solution).monotoneOn
  have hlu := hmono ⟨le_rfl, ht.le⟩ hτ hτ.1
  have hru := hmono hτ ⟨ht.le, le_rfl⟩ hτ.2
  rw [hU] at hlu
  exact (hcyl _ ⟨hlu, hru⟩).trans (hgraph τ hτ).2.symm

/-- [internal]
At a cutoff on the last available cylinder, the literal accumulated
variation is the sum of all earlier full variations and the last partial
variation. Earlier clocks have passed their endpoints; the last clock
is its actual parameter, including the singleton start. This is the
restriction/append identity used before applying finite stopped estimates.
No stopping bound, absorption or prescribed duration is used. Constants:
none. Source: charged_SF_new_version.tex:L3919–L3929, L4104–L4106; internal project record
(C1)–(C2). -/
theorem cutoff_variation_on_last_cylinder {ui e a b v₀ ρ : ℝ} {S : Fields}
(h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
(B : FiniteBoundary S ui a b v₀ ρ vb (N + 1))
(T : Fin (N + 1) → ℝ) (hT : ∀ n, 0 < T n)
(γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
(hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
(hgraph : ∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ)
{τ : ℝ} (hτ : τ ∈ Icc 0 (T (Fin.last N))) :
  (∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
    (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc)
      ((γ (Fin.last N)).U τ))))).toReal) =
    (∑ i : Fin N, (curveCovVar e S S.a (γ i.castSucc).U
      (γ i.castSucc).V 0 (T i.castSucc)).toReal) +
    (curveCovVar e S S.a (γ (Fin.last N)).U (γ (Fin.last N)).V 0 τ).toReal := by
  have hab : a ≤ b := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last (N + 1)))
  have hfirst (i : Fin (N + 2)) : a ≤ B.cuts i := B.first.ge.trans (B.ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 2)) : B.cuts i ≤ b := (B.ordered (Fin.le_last i)).trans B.last.le
  have hcool (n : Fin (N + 1)) : B.cool n ∈ Icc a b :=
    ⟨(hfirst _).trans (B.split n).1, (B.split n).2.trans (hlast _)⟩
  have hseg (n : Fin (N + 1)) : Icc ((γ n).U 0) ((γ n).U (T n)) ⊆ Icc a b := by
    rw [(hends n).1, (hends n).2]
    exact Icc_subset_Icc (hfirst _) (hcool n).2
  have hown (n : Fin (N + 1)) {s : ℝ} (hs : s ∈ Icc 0 (T n)) :
      cylinderClock S vb (B.cuts n.castSucc) ((γ n).U s) = s := by
    simpa only [(hends n).1] using cylinder_clock_at_parameter h (hT n).le (γ n) vb
      (B.cont.mono (hseg n)) (fun u hu => B.mem u (hseg n hu)) (hgraph n) hs
  let x := (γ (Fin.last N)).U τ
  have hxlow : B.cuts (Fin.last N).castSucc ≤ x := by
    have hh := ((γ (Fin.last N)).strictMonoOn_U h.solution).monotoneOn
      ⟨le_rfl, (hT _).le⟩ hτ hτ.1
    simpa only [(hends _).1] using hh
  have hx : x ∈ Icc a b := by
    have hh := ((γ (Fin.last N)).strictMonoOn_U h.solution).monotoneOn
      hτ ⟨(hT _).le, le_rfl⟩ hτ.2
    rw [(hends _).2] at hh
    exact ⟨(hfirst _).trans hxlow, hh.trans (hcool _).2⟩
  have cf : ContinuousOn (fun u => -S.nu u (vb u)) (Icc a b) :=
    (h.solution.cont_nu.comp (continuousOn_id.prodMk B.cont) B.mem).neg
  have hi {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
      IntervalIntegrable (fun u => -S.nu u (vb u)) volume u v :=
    (cf.intervalIntegrable_of_Icc (μ := volume) hab).mono_set
      (uIcc_subset_uIcc (by simpa only [uIcc_of_le hab] using hu)
        (by simpa only [uIcc_of_le hab] using hv))
  have hprev (i : Fin N) : T i.castSucc ≤ cylinderClock S vb (B.cuts i.castSucc.castSucc) x := by
    have hind : i.castSucc.succ ≤ (Fin.last N).castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
      omega
    have hle : B.cool i.castSucc ≤ x :=
      (B.split _).2.trans ((B.ordered hind).trans hxlow)
    have hc := hown i.castSucc (right_mem_Icc.mpr (hT _).le)
    rw [(hends _).2] at hc
    calc
      T i.castSucc = cylinderClock S vb (B.cuts i.castSucc.castSucc) (B.cool i.castSucc) := hc.symm
      _ ≤ cylinderClock S vb (B.cuts i.castSucc.castSucc) x := by
        unfold cylinderClock
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hi ⟨hfirst _, hlast _⟩ (hcool _)) (hi (hcool _) hx)]
        apply le_add_of_nonneg_right
        apply intervalIntegral.integral_nonneg hle
        intro u hu
        exact (neg_pos.mpr (h.solution.nu_neg _ (B.mem u ⟨(hcool _).1.trans hu.1,
          hu.2.trans hx.2⟩))).le
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [min_eq_left (hprev i), max_eq_right (hT _).le]
  · rw [hown _ hτ, min_eq_right hτ.2, max_eq_right hτ.1]

end EmcsfAcExtension.Global.Closure
