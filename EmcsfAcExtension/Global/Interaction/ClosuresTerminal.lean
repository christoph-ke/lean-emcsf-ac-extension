module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Infra.Level.OrderIso
import EmcsfAcExtension.Global.Terminal.Charge
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Terminal constraints in the radius coordinate

The decreasing terminal radius is inverted on each proper closed segment.
Both endpoints are included through within derivatives. These segments
cover every positive terminal radius, including the initial radius, without
a terminal finiteness assumption. Source: `charged_SF_new_version.tex:L991–L1004`.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Terminal

private theorem real_section_derivative {f g : ℝ → ℝ} {a b u : ℝ}
    (hg : ContinuousOn g (Icc a b))
    (hform : ∀ x ∈ Icc a b, IntegralForm f g a x) (hu : u ∈ Icc a b) :
    HasDerivWithinAt f (g u) (Icc a b) u := by
  let : Fact (u ∈ Icc a b) := ⟨hu⟩
  have hp := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc a b) (t := Icc a b)
    (hform u hu).1 ⟨Icc a b, self_mem_nhdsWithin, hg.aestronglyMeasurable measurableSet_Icc⟩
    (hg u hu)
  exact (hp.const_add (f a)).congr_of_mem (fun x hx => (hform x hx).eq_add_integral) hu

/-- [internal] A canonical inverse on a proper terminal segment and the
two radius derivatives. No flux, asymptotic bound, or inverse is assumed.
The derivative statements include the segment's endpoints. -/
theorem terminal_radial_constraints {ui e a b : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hia : ui ≤ a) (hab : a ≤ b) (hb : b < 0) :
    ∃ U : ℝ → ℝ, Continuous U ∧
      (∀ R ∈ Icc (S.r b 0) (S.r a 0), U R ∈ Icc a b ∧ S.r (U R) 0 = R) ∧
      ∀ R ∈ Icc (S.r b 0) (S.r a 0),
        HasDerivWithinAt (fun R => S.Q (U R) 0)
          (e * R * (starRingEnd ℂ (S.phi (U R) 0) *
            (S.xi (U R) 0 / (S.nu (U R) 0 : ℂ))).im)
          (Icc (S.r b 0) (S.r a 0)) R ∧
        HasDerivWithinAt (fun R => S.m (U R) 0)
          ((1 - S.mu (U R) 0) / 2 * ‖S.xi (U R) 0 / (S.nu (U R) 0 : ℂ)‖ ^ 2 +
            S.Q (U R) 0 ^ 2 / (2 * R ^ 2))
          (Icc (S.r b 0) (S.r a 0)) R := by
  have hseg : inSeg a b 0 ⊆ origDomain ui := by
    rintro ⟨u, v⟩ ⟨hau, hub, rfl⟩
    exact ⟨hia.trans hau, hub.trans_lt hb, (hub.trans_lt hb).le, le_rfl⟩
  have hp (u : ℝ) (hu : u ∈ Icc a b) : (u, 0) ∈ origDomain ui := hseg ⟨hu.1, hu.2, rfl⟩
  have cr := Calculus.continuousOn_in_section h.solution.cont_r hseg
  have cn := Calculus.continuousOn_in_section h.solution.cont_nu hseg
  have cm := Calculus.continuousOn_in_section h.solution.cont_m hseg
  have cq := Calculus.continuousOn_in_section h.solution.cont_Q hseg
  have cp := Calculus.continuousOn_in_section h.solution.cont_phi hseg
  have cx := Calculus.continuousOn_in_section h.solution.cont_xi hseg
  have hanti : StrictAntiOn (fun u => S.r u 0) (Icc a b) :=
    (terminal_radius_strictAntiOn h.solution).mono
      (fun u hu => ⟨hia.trans hu.1, hu.2.trans_lt hb⟩)
  have hR : S.r b 0 ≤ S.r a 0 := hanti.antitoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  let E := Level.intervalOrderIsoAnti hab cr hanti
  let U : ℝ → ℝ := IccExtend hR (fun R => ((E.symm R).ofDual : ℝ))
  have cU : Continuous U :=
    (continuous_subtype_val.comp E.symm.continuous).Icc_extend'
  have memU (R : ℝ) : U R ∈ Icc a b := by
    simpa only [U, IccExtend, Function.comp_apply] using
      (E.symm (projIcc _ _ hR R)).ofDual.property
  have invU (R : ℝ) (hR' : R ∈ Icc (S.r b 0) (S.r a 0)) : S.r (U R) 0 = R := by
    have he := congrArg Subtype.val (E.apply_symm_apply ⟨R, hR'⟩)
    have hval : U R = ((E.symm ⟨R, hR'⟩).ofDual : ℝ) :=
      IccExtend_val hR _ ⟨R, hR'⟩
    rw [hval]
    exact (Level.intervalOrderIsoAnti_apply hab cr hanti _).symm.trans he
  have nr (u : ℝ) (hu : u ∈ Icc a b) :=
    (h.solution.r_pos (u, 0) (hp u hu) (hu.2.trans_lt hb)).ne'
  have nn (u : ℝ) (hu : u ∈ Icc a b) := (h.solution.nu_neg (u, 0) (hp u hu)).ne
  have cg : ContinuousOn (fun u => 1 - S.mu u 0) (Icc a b) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr nr)
  have cQU : ContinuousOn (fun u => S.QU e u 0) (Icc a b) :=
    (continuousOn_const.mul cr).mul (Complex.continuous_im.comp_continuousOn (cp.star.mul cx))
  have cmU : ContinuousOn (fun u => S.mU u 0) (Icc a b) :=
    ((cg.mul (cx.norm.pow 2)).div (continuousOn_const.mul cn)
      (fun u hu => mul_ne_zero (by norm_num) (nn u hu))).add
      (((cq.pow 2).mul cn).div (continuousOn_const.mul (cr.pow 2))
        (fun u hu => mul_ne_zero (by norm_num) (pow_ne_zero _ (nr u hu))))
  have forms (x : ℝ) (hx : x ∈ Icc a b) := h.solution.eq_in a x 0 hx.1
    (hx.2.trans_lt hb) (fun p hp => hseg ⟨hp.1, hp.2.1.trans hx.2, hp.2.2⟩)
  have dr (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivWithinAt (fun u => S.r u 0) (S.nu x 0) (Icc a b) x :=
    real_section_derivative cn (fun y hy => (forms y hy).1) hx
  have dQ (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivWithinAt (fun u => S.Q u 0) (S.QU e x 0) (Icc a b) x :=
    real_section_derivative cQU (fun y hy => (forms y hy).2.2.2.1) hx
  have dm (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivWithinAt (fun u => S.m u 0) (S.mU x 0) (Icc a b) x :=
    real_section_derivative cmU (fun y hy => (forms y hy).2.2.1) hx
  refine ⟨U, cU, fun R hR' => ⟨memU R, invU R hR'⟩, ?_⟩
  intro R hR'
  have hmap : MapsTo U (Icc (S.r b 0) (S.r a 0)) (Icc a b) := fun x _ => memU x
  have hlim : Tendsto U (𝓝[Icc (S.r b 0) (S.r a 0)] R) (𝓝[Icc a b] (U R)) :=
    cU.continuousAt.continuousWithinAt.tendsto_nhdsWithin hmap
  have hcomp : (fun x => S.r (U x) 0) =ᶠ[𝓝[Icc (S.r b 0) (S.r a 0)] R] id := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact invU x hx
  have dU : HasDerivWithinAt U (S.nu (U R) 0)⁻¹ (Icc (S.r b 0) (S.r a 0)) R := by
    have hd := HasFDerivWithinAt.of_comp_of_leftInverse hlim (dr (U R) (memU R)).hasFDerivWithinAt
      (hasFDerivWithinAt_id R (Icc (S.r b 0) (S.r a 0))) hcomp
      (f'symm := ContinuousLinearMap.toSpanSingleton ℝ (S.nu (U R) 0)⁻¹)
      (fun x => by simp [nn (U R) (memU R)]) hR'
    simpa using hd.hasDerivWithinAt
  constructor
  · apply ((dQ (U R) (memU R)).comp R dU hmap).congr_deriv
    rw [← div_eq_mul_inv, incoming_maxwell_radial_density h.solution (hp (U R) (memU R)),
      invU R hR']
  · apply ((dm (U R) (memU R)).comp R dU hmap).congr_deriv
    have he := incoming_mass_radial_density h.solution (hp (U R) (memU R))
    rw [invU R hR'] at he
    rw [← div_eq_mul_inv]
    linear_combination he / 2

/-- [internal] The two radius constraints on the entire positive terminal
radius range. Proper inverses agree with the canonical half-open inverse,
so the closed-segment endpoint calculus also covers the initial radius. -/
theorem terminal_radial_constraints_global {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) :
    ∃ U : ℝ → ℝ, ContinuousOn U (Ioc 0 (S.r ui 0)) ∧
      (∀ R ∈ Ioc 0 (S.r ui 0), U R ∈ Ico ui 0 ∧ S.r (U R) 0 = R) ∧
      ∀ R ∈ Ioc 0 (S.r ui 0),
        HasDerivWithinAt (fun R => S.Q (U R) 0)
          (e * R * (starRingEnd ℂ (S.phi (U R) 0) *
            (S.xi (U R) 0 / (S.nu (U R) 0 : ℂ))).im)
          (Ioc 0 (S.r ui 0)) R ∧
        HasDerivWithinAt (fun R => S.m (U R) 0)
          ((1 - S.mu (U R) 0) / 2 * ‖S.xi (U R) 0 / (S.nu (U R) 0 : ℂ)‖ ^ 2 +
            S.Q (U R) 0 ^ 2 / (2 * R ^ 2)) (Ioc 0 (S.r ui 0)) R := by
  have cr : ContinuousOn (fun u => S.r u 0) (Ico ui 0) :=
    h.solution.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu.1, hu.2, hu.2.le, le_rfl⟩)
  have ha := terminal_radius_strictAntiOn h.solution
  have hp (u : ℝ) (hu : u ∈ Ico ui 0) : 0 < S.r u 0 :=
    h.solution.r_pos (u, 0) ⟨hu.1, hu.2, hu.2.le, le_rfl⟩ hu.2
  have ht := terminal_radius_collapse h.ui_neg h.solution h.mu
  let E := Level.terminalOrderIso h.ui_neg cr ha hp ht
  let U : ℝ → ℝ := fun R => if hR : R ∈ Ioc 0 (S.r ui 0) then
    ((E.symm ⟨R, hR⟩).ofDual : ℝ) else 0
  have cU : ContinuousOn U (Ioc 0 (S.r ui 0)) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp E.symm.continuous using 1
    funext R
    simp only [U, dite_eq_left R.property, Set.domRestrict_apply]
    rfl
  have memU (R : ℝ) (hR : R ∈ Ioc 0 (S.r ui 0)) : U R ∈ Ico ui 0 := by
    simpa only [U, dite_eq_left hR] using (E.symm ⟨R, hR⟩).ofDual.property
  have invU (R : ℝ) (hR : R ∈ Ioc 0 (S.r ui 0)) : S.r (U R) 0 = R := by
    have he := congrArg Subtype.val (E.apply_symm_apply ⟨R, hR⟩)
    dsimp only [U]
    rw [dite_eq_left hR]
    exact (Level.terminalOrderIso_apply h.ui_neg cr ha hp ht _).symm.trans he
  refine ⟨U, cU, fun R hR => ⟨memU R hR, invU R hR⟩, ?_⟩
  intro R hR
  let b := U R / 2
  have hub : U R < b := by dsimp [b]; linarith only [(memU R hR).2]
  have hb : b < 0 := by dsimp [b]; linarith only [(memU R hR).2]
  have hib : ui ≤ b := (memU R hR).1.trans hub.le
  obtain ⟨V, cV, hV, hd⟩ := terminal_radial_constraints h le_rfl hib hb
  have hbr : S.r b 0 < R := by
    rw [← invU R hR]
    exact ha (memU R hR) ⟨hib, hb⟩ hub
  have hlocal : ∀ x ∈ Icc (S.r b 0) (S.r ui 0), x ∈ Ioc 0 (S.r ui 0) :=
    fun x hx => ⟨(hp b ⟨hib, hb⟩).trans_le hx.1, hx.2⟩
  have hsame (x : ℝ) (hx : x ∈ Icc (S.r b 0) (S.r ui 0)) : V x = U x := by
    apply ha.injOn ⟨(hV x hx).1.1, (hV x hx).1.2.trans_lt hb⟩ (memU x (hlocal x hx))
    exact (hV x hx).2.trans (invU x (hlocal x hx)).symm
  have hn : Icc (S.r b 0) (S.r ui 0) ∈ 𝓝[Ioc 0 (S.r ui 0)] R := by
    apply mem_of_superset (inter_mem_nhdsWithin (Ioc 0 (S.r ui 0)) (Ioi_mem_nhds hbr))
    intro x hx
    exact ⟨hx.2.le, hx.1.2⟩
  have hRloc : R ∈ Icc (S.r b 0) (S.r ui 0) := ⟨hbr.le, hR.2⟩
  have heqQ : (fun x => S.Q (U x) 0) =ᶠ[𝓝[Ioc 0 (S.r ui 0)] R]
      (fun x => S.Q (V x) 0) := by
    filter_upwards [hn] with x hx
    rw [hsame x hx]
  have heqm : (fun x => S.m (U x) 0) =ᶠ[𝓝[Ioc 0 (S.r ui 0)] R]
      (fun x => S.m (V x) 0) := by
    filter_upwards [hn] with x hx
    rw [hsame x hx]
  have hdQ := (hd R hRloc).1.mono_of_mem_nhdsWithin hn
  have hdm := (hd R hRloc).2.mono_of_mem_nhdsWithin hn
  rw [hsame R hRloc] at hdQ hdm
  exact ⟨hdQ.congr_of_eventuallyEq heqQ (by rw [hsame R hRloc]),
    hdm.congr_of_eventuallyEq heqm (by rw [hsame R hRloc])⟩

/-- [node prop:charged-terminal-equivalence#terminal-maxwell-radial]
The terminal Maxwell equation on every `0 < R ≤ Rᵢ`,
charged_SF_new_version.tex:L991–L995. The continuous radius inverse and its defining
identity are proved from the original development. The upper endpoint
uses its one-sided derivative. There are no constants or terminal hypotheses. -/
theorem terminal_maxwell_radial {ui e : ℝ} {S : Fields} (h : OriginalData ui e S) :
    ∃ U : ℝ → ℝ, ContinuousOn U (Ioc 0 (S.r ui 0)) ∧
      (∀ R ∈ Ioc 0 (S.r ui 0), U R ∈ Ico ui 0 ∧ S.r (U R) 0 = R) ∧
      ∀ R ∈ Ioc 0 (S.r ui 0), HasDerivWithinAt (fun R => S.Q (U R) 0)
        (e * R * (starRingEnd ℂ (S.phi (U R) 0) *
          (S.xi (U R) 0 / (S.nu (U R) 0 : ℂ))).im) (Ioc 0 (S.r ui 0)) R := by
  obtain ⟨U, cU, hU, hd⟩ := terminal_radial_constraints_global h
  exact ⟨U, cU, hU, fun R hR => (hd R hR).1⟩

/-- [node prop:charged-terminal-equivalence#terminal-mass-radial]
The terminal mass equation and its electric lower bound for every
`0 < R ≤ Rᵢ`, charged_SF_new_version.tex:L998–L1004. The radius inverse is constructed
from the original development, including one-sided calculus at `Rᵢ`.
There are no constants or signed-terminal premises. -/
theorem terminal_mass_radial {ui e : ℝ} {S : Fields} (h : OriginalData ui e S) :
    ∃ U : ℝ → ℝ, ContinuousOn U (Ioc 0 (S.r ui 0)) ∧
      (∀ R ∈ Ioc 0 (S.r ui 0), U R ∈ Ico ui 0 ∧ S.r (U R) 0 = R) ∧
      ∀ R ∈ Ioc 0 (S.r ui 0),
        HasDerivWithinAt (fun R => S.m (U R) 0)
          ((1 - S.mu (U R) 0) / 2 * ‖S.xi (U R) 0 / (S.nu (U R) 0 : ℂ)‖ ^ 2 +
            S.Q (U R) 0 ^ 2 / (2 * R ^ 2)) (Ioc 0 (S.r ui 0)) R ∧
        S.Q (U R) 0 ^ 2 / (2 * R ^ 2) ≤
          (1 - S.mu (U R) 0) / 2 * ‖S.xi (U R) 0 / (S.nu (U R) 0 : ℂ)‖ ^ 2 +
            S.Q (U R) 0 ^ 2 / (2 * R ^ 2) := by
  obtain ⟨U, cU, hU, hd⟩ := terminal_radial_constraints_global h
  refine ⟨U, cU, hU, ?_⟩
  intro R hR
  refine ⟨(hd R hR).2, le_add_of_nonneg_left (mul_nonneg ?_ (sq_nonneg _))⟩
  have hu := (hU R hR).1
  exact div_nonneg (h.solution.one_sub_mu_pos (U R, 0)
    ⟨hu.1, hu.2, hu.2.le, le_rfl⟩).le (by norm_num)

end EmcsfAcExtension.Global.Terminal
