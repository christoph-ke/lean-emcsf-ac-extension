module

public import EmcsfAcExtension.Global.Exterior.OpticsCoefficients
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Incoming-past invariance of an adaptive exterior

A closed-set induction proves that an incoming characteristic cannot
cross the adaptive frontier towards the past. The comparison uses the
Lipschitz bound for the radius profile, rather than differentiating it
at a possibly nondifferentiable frontier value.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The geometric incoming-past comparison of `charged_SF_new_version.tex:L1192–L1195`.
The two radius derivatives are continuous, the terminal radius decreases,
and the derivative ratio at exterior points exceeds the prescribed
Lipschitz slope. The conclusion includes starting points on the frontier.
All constants are the prescribed slope and outer radius. -/
theorem incoming_past_invariant_of_characteristic
    {r R n nt ell : ℝ → ℝ} {a b R₀ k : ℝ} (_hab : a ≤ b) (hk : 0 ≤ k)
    (cr : ContinuousOn r (Icc a b)) (cR : ContinuousOn R (Icc a b))
    (cn : ContinuousOn n (Icc a b)) (cnt : ContinuousOn nt (Icc a b))
    (hdr : ∀ x ∈ Ioo a b, HasDerivAt r (n x) x)
    (hdR : ∀ x ∈ Ioo a b, HasDerivAt R (nt x) x)
    (hnt : ∀ x ∈ Icc a b, nt x < 0)
    (hRange : ∀ x ∈ Icc a b, R x ∈ Ioc 0 R₀)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hratio : ∀ x ∈ Icc a b, ell (R x) ≤ r x → k < n x / nt x)
    (hb : ell (R b) ≤ r b) : ∀ x ∈ Icc a b, ell (R x) ≤ r x := by
  let E : Set ℝ := {x | ell (R x) ≤ r x}
  have cEll : ContinuousOn (fun x => ell (R x)) (Icc a b) :=
    hLip.continuousOn.comp cR hRange
  have hclosed : IsClosed (E ∩ Icc a b) := by
    convert isClosed_Icc.isClosed_le cEll cr using 1
    ext x
    change (ell (R x) ≤ r x ∧ a ≤ x ∧ x ≤ b) ↔
      ((a ≤ x ∧ x ≤ b) ∧ ell (R x) ≤ r x)
    tauto
  have hRanti : StrictAntiOn R (Icc a b) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc a b) cR
      (fun x hx => (hdR x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt)
    intro x hx
    exact hnt x (interior_subset hx)
  have cratio : ContinuousOn (fun x => n x / nt x) (Icc a b) :=
    cn.div cnt (fun x hx => (hnt x hx).ne)
  have hlocal (t : ℝ) (hEt : t ∈ E) (ht : t ∈ Ioc a b) : E ∈ 𝓝[<] t := by
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
    have hmem : Icc a b ∈ 𝓝[<] t := mem_of_superset (Ioo_mem_nhdsLT ht.1)
      (fun x hx => ⟨hx.1.le, hx.2.le.trans ht.2⟩)
    have hid : Tendsto (fun x : ℝ => x) (𝓝[<] t) (𝓝[Icc a b] t) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto t), hmem⟩
    have he := ((cratio t ht').tendsto.comp hid).eventually
      (Ioi_mem_nhds (hratio t ht' hEt))
    obtain ⟨m, hm, hmb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
    apply mem_nhdsLT_iff_exists_Ioo_subset.mpr
    refine ⟨max m a, max_lt hm ht.1, ?_⟩
    intro s hs
    have hs' : s ∈ Icc a b :=
      ⟨(le_max_right m a).trans hs.1.le, hs.2.le.trans ht.2⟩
    have hst : Icc s t ⊆ Icc a b := Icc_subset_Icc hs'.1 ht.2
    have hG : StrictAntiOn (fun x => r x - k * R x) (Icc s t) := by
      refine strictAntiOn_of_hasDerivWithinAt_neg (f' := fun x => n x - k * nt x)
        (convex_Icc s t) ((cr.sub (cR.const_mul k)).mono hst) ?_ ?_
      · intro x hx
        have hx' : x ∈ Ioo s t := by simpa only [interior_Icc] using hx
        have hx'' : x ∈ Ioo a b :=
          ⟨hs'.1.trans_lt hx'.1, hx'.2.trans_le ht.2⟩
        exact ((hdr x hx'').sub ((hdR x hx'').const_mul k)).hasDerivWithinAt
      · intro x hx
        have hx' : x ∈ Ioo s t := by simpa only [interior_Icc] using hx
        have hxm : x ∈ Ioo m t :=
          ⟨(le_max_left m a).trans_lt (hs.1.trans hx'.1), hx'.2⟩
        have hx'' : x ∈ Icc a b := hst (interior_subset hx)
        exact sub_neg.mpr ((lt_div_iff_of_neg (hnt x hx'')).mp (hmb hxm))
    have hGst := hG ⟨le_rfl, hs.2.le⟩ ⟨hs.2.le, le_rfl⟩ hs.2
    have hRst := hRanti hs' ht' hs.2
    have hL := (lipschitzOnWith_iff_dist_le_mul.mp hLip)
      (R s) (hRange s hs') (R t) (hRange t ht')
    rw [Real.coe_toNNReal _ hk, Real.dist_eq, Real.dist_eq,
      abs_of_pos (sub_pos.mpr hRst)] at hL
    have hL' := (le_abs_self (ell (R s) - ell (R t))).trans hL
    change ell (R s) ≤ r s
    change ell (R t) ≤ r t at hEt
    change r t - k * R t < r s - k * R s at hGst
    linarith only [hGst, hL', hEt]
  have hclosedDual : IsClosed (E ∩ Icc (α := ℝᵒᵈ) b a) := by
    have heq : E ∩ Icc (α := ℝᵒᵈ) b a = E ∩ Icc a b := by
      ext x
      constructor <;> intro hx <;> exact ⟨hx.1, hx.2.2, hx.2.1⟩
    rw [heq]
    exact hclosed
  have hfull : Icc (α := ℝᵒᵈ) b a ⊆ E :=
    IsClosed.Icc_subset_of_forall_mem_nhdsWithin hclosedDual hb
      (fun x hx => hlocal x hx.1 ⟨hx.2.2, hx.2.1⟩)
  intro x hx
  exact hfull ⟨hx.2, hx.1⟩

/-- [internal]
Along a controlled incoming segment the difference between radius and
the adaptive inner radius strictly increases towards the past. The
prescribed slope is the only comparison constant. -/
theorem strict_incoming_separation_of_characteristic
    {r R n nt ell : ℝ → ℝ} {a b R₀ k : ℝ} (hk : 0 ≤ k)
    (cr : ContinuousOn r (Icc a b)) (cR : ContinuousOn R (Icc a b))
    (hdr : ∀ x ∈ Ioo a b, HasDerivAt r (n x) x)
    (hdR : ∀ x ∈ Ioo a b, HasDerivAt R (nt x) x)
    (hnt : ∀ x ∈ Icc a b, nt x < 0)
    (hRange : ∀ x ∈ Icc a b, R x ∈ Ioc 0 R₀)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hratio : ∀ x ∈ Icc a b, k < n x / nt x) :
    StrictAntiOn (fun x => r x - ell (R x)) (Icc a b) := by
  have hRa : StrictAntiOn R (Icc a b) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc a b) cR
      (fun x hx => (hdR x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt)
    exact fun x hx => hnt x (interior_subset hx)
  have hGa : StrictAntiOn (fun x => r x - k * R x) (Icc a b) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (f' := fun x => n x - k * nt x)
      (convex_Icc a b) (cr.sub (cR.const_mul k)) ?_ ?_
    · intro x hx
      have hx' : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
      exact ((hdr x hx').sub ((hdR x hx').const_mul k)).hasDerivWithinAt
    · intro x hx
      exact sub_neg.mpr ((lt_div_iff_of_neg (hnt x (interior_subset hx))).mp
        (hratio x (interior_subset hx)))
  intro x hx y hy hxy
  have hg := hGa hx hy hxy
  have hr := hRa hx hy hxy
  have hL := (lipschitzOnWith_iff_dist_le_mul.mp hLip) (R x) (hRange x hx) (R y) (hRange y hy)
  rw [Real.coe_toNNReal _ hk, Real.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.mpr hr)] at hL
  have hL' := (le_abs_self (ell (R x) - ell (R y))).trans hL
  change r y - ell (R y) < r x - ell (R x)
  change r y - k * R y < r x - k * R x at hg
  linarith only [hg, hL']

/-- [internal]
The original incoming characteristics satisfy the geometric comparison.
The source derivative and continuity hypotheses are discharged directly
from the frozen equations. The consumer supplies the optical ratio bound
and the positive terminal-radius range on late rows. -/
theorem incoming_past_invariance_of_optical_bounds {ui e u₀ R₀ k : ℝ} {S : Fields}
    (h : OriginalData ui e S) (ell : ℝ → ℝ) (hu₀ : u₀ ∈ Ioo ui 0) (hk : 0 ≤ k)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hRange : ∀ u ∈ Ico u₀ 0, S.r u 0 ∈ Ioc 0 R₀)
    (hratio : ∀ p ∈ adaptiveExterior S ui u₀ ell, k < S.nu p.1 p.2 / S.nu p.1 0) :
    ∀ p ∈ adaptiveExterior S ui u₀ ell,
      (∀ s ∈ Icc u₀ p.1, (s, p.2) ∈ adaptiveExterior S ui u₀ ell) ∧
      StrictAntiOn (fun s => S.r s p.2 - ell (S.r s 0)) (Icc u₀ p.1) := by
  intro p hp
  have hs : inSeg u₀ p.1 p.2 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hp.2.1).2
      ⟨hu₀.1.le, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2⟩
  have hs0 : inSeg u₀ p.1 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hp.2.1).2
      ⟨hu₀.1.le, hp.1.2.1, hp.1.2.1.le, le_rfl⟩
  have cr := Calculus.continuousOn_in_section h.solution.cont_r hs
  have cR := Calculus.continuousOn_in_section h.solution.cont_r hs0
  have cn := Calculus.continuousOn_in_section h.solution.cont_nu hs
  have cnt := Calculus.continuousOn_in_section h.solution.cont_nu hs0
  have hd (x : ℝ) (hx : x ∈ Ioo u₀ p.1) :
      HasDerivAt (fun u => S.r u p.2) (S.nu x p.2) x := by
    apply Local.hasDerivAt_of_integralForm_interior hx (cn.mono Ioo_subset_Icc_self)
    intro c d hc hcd hd
    exact (h.solution.eq_in c d p.2 hcd (hd.trans_le hp.1.2.2.1)
      (fun _ hy => hs (inSeg_subset_inSeg hc.le hd.le hy))).1
  have hd0 (x : ℝ) (hx : x ∈ Ioo u₀ p.1) :
      HasDerivAt (fun u => S.r u 0) (S.nu x 0) x := by
    apply Local.hasDerivAt_of_integralForm_interior hx (cnt.mono Ioo_subset_Icc_self)
    intro c d hc hcd hd
    exact (h.solution.eq_in c d 0 hcd (hd.trans hp.1.2.1)
      (fun _ hy => hs0 (inSeg_subset_inSeg hc.le hd.le hy))).1
  have hkeep := incoming_past_invariant_of_characteristic hp.2.1 hk cr cR cn cnt hd hd0
    (fun x hx => h.solution.nu_neg (x, 0) (hs0 ⟨hx.1, hx.2, rfl⟩))
    (fun x hx => hRange x ⟨hx.1, hx.2.trans_lt hp.1.2.1⟩) hLip
    (fun x hx hext => hratio (x, p.2) ⟨hs ⟨hx.1, hx.2, rfl⟩, hx.1, hext⟩) hp.2.2
  refine ⟨?_, strict_incoming_separation_of_characteristic hk cr cR hd hd0
    (fun x hx => h.solution.nu_neg (x, 0) (hs0 ⟨hx.1, hx.2, rfl⟩))
    (fun x hx => hRange x ⟨hx.1, hx.2.trans_lt hp.1.2.1⟩) hLip ?_⟩
  · intro s hs'
    exact ⟨hs ⟨hs'.1, hs'.2, rfl⟩, hs'.1, hkeep s hs'⟩
  · exact fun x hx => hratio (x, p.2) ⟨hs ⟨hx.1, hx.2, rfl⟩, hx.1, hkeep x hx⟩

/-- [internal]
Conditional terminal consumer for `c:exterior#incoming-past-invariance`.
The small prescribed slope and the uniform incoming optical limit give
the strict ratio comparison, including at the frontier. The cutoff may
depend on the fixed terminal inputs; no core gap is assumed. -/
theorem incoming_past_invariance_of_terminal {ui e C k : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      (∀ s ∈ Icc u₀ p.1, (s, p.2) ∈ adaptiveExterior S ui u₀ ell) ∧
      StrictAntiOn (fun s => S.r s p.2 - ell (S.r s 0)) (Icc u₀ p.1) := by
  obtain ⟨un, hun, hnu⟩ := uniform_nu_ratio_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi (1 / 2) (by norm_num)
  have he : ∀ᶠ u in 𝓝[<] (0 : ℝ), u ∈ Ioo ui 0 ∧ S.r u 0 < R₀ := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg, hcollapse.eventually (Iio_mem_nhds hR)]
      with u hu hr
    exact ⟨hu, hr⟩
  obtain ⟨d, hd, hdb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  let ur := max d ui / 2
  have hur : ur ∈ Ioo ui 0 := by
    have hm0 := max_lt hd h.ui_neg
    dsimp [ur]
    constructor <;> linarith [le_max_right d ui]
  let u₀ := max un ur
  have hu₀ : u₀ ∈ Ioo ui 0 := ⟨lt_max_of_lt_left hun.1, max_lt hun.2 hur.2⟩
  refine ⟨u₀, hu₀, incoming_past_invariance_of_optical_bounds h ell hu₀ hk.1.le hLip ?_ ?_⟩
  · intro u hu
    have hu' : u ∈ Ioo d 0 := by
      refine ⟨?_, hu.2⟩
      have hb : ur ≤ u := (le_max_right un ur).trans hu.1
      dsimp [ur] at hb
      have hm0 := max_lt hd h.ui_neg
      linarith [le_max_left d ui]
    exact ⟨h.solution.r_pos (u, 0) ⟨hu₀.1.le.trans hu.1, hu.2, hu.2.le, le_rfl⟩ hu.2,
      (hdb hu').2.le⟩
  · intro p hp
    have hn := hnu p ⟨hp.1, (le_max_left un ur).trans hp.2.1, hp.2.2⟩
    have hlow := (abs_lt.mp hn).1
    linarith [hk.2]

end EmcsfAcExtension.Global.Exterior
