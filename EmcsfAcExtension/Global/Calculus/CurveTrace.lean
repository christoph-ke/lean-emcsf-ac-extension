module

public import EmcsfAcExtension.Global.Calculus.DensityRepresentative
import EmcsfAcExtension.Infra.Density.CurveChain
import EmcsfAcExtension.Infra.AC.Intervals

/-! # AC traces on proper timelike characteristic charts

The outgoing derivative is the fixed initial-density representative. Its
label-null set pulls back under a bi-Lipschitz label. The incoming partial is
continuous by the normalized transport equation. No arbitrary product-a.e.
derivative is evaluated on a curve (`charged_SF_new_version.tex:L1410–L1416`).
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped NNReal

namespace EmcsfAcExtension.Global.Calculus

/-- [internal] Continuous characteristic sources give within derivatives at
the closed-section endpoints as well as interior derivatives. The premise is
the anchored characteristic equation, not a differentiability assumption. -/
theorem hasDerivWithinAt_of_characteristic_forms
    {f g : ℝ → ℂ} {a b u : ℝ} (_hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b))
    (hform : ∀ x ∈ Icc a b, IntegralForm f g a x) (hu : u ∈ Icc a b) :
    HasDerivWithinAt f (g u) (Icc a b) u := by
  let : Fact (u ∈ Icc a b) := ⟨hu⟩
  have hp := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc a b) (t := Icc a b)
    (hform u hu).1 ⟨Icc a b, self_mem_nhdsWithin, hg.aestronglyMeasurable measurableSet_Icc⟩
    (hg u hu)
  exact (hp.const_add (f a)).congr_of_mem (fun x hx => (hform x hx).eq_add_integral) hu

/-- [internal] The ordinary incoming normalized source is jointly continuous
on every positive-radius part of a frozen solution. -/
theorem continuousOn_normalized_incoming_source
    {e : ℝ} {S : Fields} {D K : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hK : K ⊆ D ∩ {p | p.1 < p.2}) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (-S.nu p.1 p.2 / ((1 - S.mu p.1 p.2) * S.r p.1 p.2) : ℝ) *
        (S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) *
          (S.a p.1 p.2 - S.phi p.1 p.2) +
        I * e * (-S.nu p.1 p.2 / ((1 - S.mu p.1 p.2) * S.r p.1 p.2) : ℝ) *
          S.Q p.1 p.2 * S.phi p.1 p.2 - I * e * S.A p.1 p.2 * S.a p.1 p.2) K := by
  have cr := hS.cont_r.mono (fun p hp => (hK hp).1)
  have cn := hS.cont_nu.mono (fun p hp => (hK hp).1)
  have cm := hS.cont_m.mono (fun p hp => (hK hp).1)
  have cQ := hS.cont_Q.mono (fun p hp => (hK hp).1)
  have cA := hS.cont_A.mono (fun p hp => (hK hp).1)
  have cp := hS.cont_phi.mono (fun p hp => (hK hp).1)
  have ca := (continuousOn_a hS).mono (fun p hp => (hK hp).1)
  have hr (p : ℝ × ℝ) (hp : p ∈ K) := (hS.r_pos p (hK hp).1 (hK hp).2).ne'
  have hg (p : ℝ × ℝ) (hp : p ∈ K) := (hS.one_sub_mu_pos p (hK hp).1).ne'
  have cmu : ContinuousOn (Function.uncurry S.mu) K :=
    (continuousOn_const.mul cm).div cr hr
  have cP := cn.neg.div ((continuousOn_const.sub cmu).mul cr)
    (fun p hp => mul_ne_zero (hg p hp) (hr p hp))
  have cB := cmu.sub ((cQ.pow 2).div (cr.pow 2) (fun p hp => pow_ne_zero _ (hr p hp)))
  have cPC := Complex.continuous_ofReal.comp_continuousOn cP
  have cBC := Complex.continuous_ofReal.comp_continuousOn cB
  fun_prop

/-- [internal] The timelike AC chain rule on a proper rectangular chart.
The initial incoming row `a₀` is fixed before choosing the curve segment, so
adjacent charts may use the same prescribed density. All four Lipschitz
constants are explicit and local to the proper parameter interval. -/
theorem timelike_ac_chain_rule_on_rectangle
    {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    {U V : ℝ → ℝ} {s t a₀ : ℝ} {KU KV LU LV : ℝ≥0} (hst : s < t)
    (hU : LipschitzOnWith KU U (uIcc s t)) (hV : LipschitzOnWith KV V (uIcc s t))
    (hUm : MonotoneOn U (uIcc s t)) (hVm : MonotoneOn V (uIcc s t))
    (hUa : AntilipschitzWith LU ((uIcc s t).domRestrict U))
    (hVa : AntilipschitzWith LV ((uIcc s t).domRestrict V)) (ha₀ : a₀ ≤ U s)
    (hrect : Icc a₀ (U t) ×ˢ Icc (V s) (V t) ⊆ D ∩ {p | p.1 < p.2}) :
    let G : ℝ → ℝ → ℂ := fun u v =>
      (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) * (S.a u v - S.phi u v) +
        I * e * (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) * S.Q u v * S.phi u v -
        I * e * S.A u v * S.a u v
    AbsolutelyContinuousOnInterval (fun x => S.a (U x) (V x)) s t ∧
      ∀ᵐ x ∂volume.restrict (uIcc s t), HasDerivAt (fun y => S.a (U y) (V y))
        (deriv U x • G (U x) (V x) +
          deriv V x • densityRepresentative e S a₀ (U x) (V x)) x := by
  let G : ℝ → ℝ → ℂ := fun u v =>
    (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) * (S.a u v - S.phi u v) +
      I * e * (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) * S.Q u v * S.phi u v -
      I * e * S.A u v * S.a u v
  have hUS := hUm.strictMonoOn_of_injOn (by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hUa.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy))
  have hVS := hVm.strictMonoOn_of_injOn (by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hVa.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy))
  have hUt := hUS left_mem_uIcc right_mem_uIcc hst
  have hVt := hVS left_mem_uIcc right_mem_uIcc hst
  have haUt := ha₀.trans_lt hUt
  obtain ⟨P, R, hP, hR, heq, hprim⟩ := exists_density_factors hS haUt hVt hrect
  have hsub : uIcc (U s) (U t) ×ˢ uIcc (V s) (V t) ⊆
      Icc a₀ (U t) ×ˢ Icc (V s) (V t) := by
    simp only [uIcc_of_le hUt.le, uIcc_of_le hVt.le]
    exact prod_mono (Icc_subset_Icc ha₀ le_rfl) Subset.rfl
  have hG := (continuousOn_normalized_incoming_source hS hrect).mono hsub
  have hinit := (hS.ac_out a₀ (V s) (V t) hVt.le (by
    rintro ⟨u, v⟩ ⟨rfl, hv⟩
    exact (hrect ⟨⟨le_rfl, haUt.le⟩, hv⟩).1)).2.2.2.2
  have hin : ∀ u ∈ uIcc (U s) (U t), ∀ v ∈ uIcc (V s) (V t),
      HasDerivWithinAt (fun x => S.a x v) (G u v) (uIcc (U s) (U t)) u := by
    intro u hu v hv
    rw [uIcc_of_le hUt.le] at hu ⊢
    rw [uIcc_of_le hVt.le] at hv
    apply hasDerivWithinAt_of_characteristic_forms hUt.le
      (hG.comp (continuous_id.prodMk continuous_const).continuousOn (by
        intro x hx
        simpa only [uIcc_of_le hUt.le, uIcc_of_le hVt.le] using ⟨hx, hv⟩)) ?_ hu
    intro x hx
    have hbv : x < v := hx.2.trans_lt
      ((hrect (show (U t, V s) ∈ Icc a₀ (U t) ×ˢ Icc (V s) (V t) from
        ⟨⟨haUt.le, le_rfl⟩, ⟨le_rfl, hVt.le⟩⟩)).2.trans_le hv.1)
    have hform := constant_label_connector_calculus hS hx.1 hbv (by
      rintro ⟨y, z⟩ ⟨hy, hyx, rfl⟩
      exact (hrect ⟨⟨ha₀.trans hy, hyx.trans hx.2⟩, hv⟩).1)
    simpa only [normalized_incoming_source_eq, G] using! hform
  have hrep : ∀ u ∈ uIcc (U s) (U t), ∀ v ∈ uIcc (V s) (V t),
      S.a u v = S.a u (V s) + ∫ z in V s..v, Density.fixedDensity P R (deriv (S.a a₀)) u z := by
    intro u hu v hv
    have hp := hsub (show (u, v) ∈ uIcc (U s) (U t) ×ˢ uIcc (V s) (V t) from ⟨hu, hv⟩)
    exact hprim u hp.1 v hp.2
  have hc := Density.trace_ac_chain_rule_of_fixedDensity (G := G) hst hU hV hUm hVm hUa hVa
    (hP.mono hsub) (hR.mono hsub) hG hinit.intervalIntegrable_deriv_complex hin hrep
  refine ⟨hc.1, ?_⟩
  filter_upwards [hc.2, ae_restrict_mem measurableSet_uIcc] with x hx hxm
  have hum : U x ∈ uIcc (U s) (U t) := hUm.image_uIcc_subset ⟨x, hxm, rfl⟩
  have hvm : V x ∈ uIcc (V s) (V t) := hVm.image_uIcc_subset ⟨x, hxm, rfl⟩
  have hm := hsub (show (U x, V x) ∈ uIcc (U s) (U t) ×ˢ uIcc (V s) (V t) from ⟨hum, hvm⟩)
  rw [heq _ hm.1 _ hm.2]
  exact hx

private theorem glue_characteristic_chain_rule {f g : ℝ → ℂ} {q : ℕ → ℝ}
    (hq : Monotone q) (N : ℕ)
    (h : ∀ i < N, AbsolutelyContinuousOnInterval f (q i) (q (i + 1)) ∧
      ∀ᵐ x ∂volume.restrict (Icc (q i) (q (i + 1))), HasDerivAt f (g x) x) :
    AbsolutelyContinuousOnInterval f (q 0) (q N) ∧
      ∀ᵐ x ∂volume.restrict (Icc (q 0) (q N)), HasDerivAt f (g x) x := by
  induction N with
  | zero => exact ⟨.refl _ _, by simp⟩
  | succ N ih =>
    have hp := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn := h N (Nat.lt_succ_self N)
    refine ⟨hp.1.trans_complex hn.1 (hq (Nat.zero_le _)) (hq (Nat.le_succ _)), ?_⟩
    rw [← Icc_union_Icc_eq_Icc (hq (Nat.zero_le N)) (hq (Nat.le_succ N)),
      ae_restrict_union_iff]
    exact ⟨hp.2, hn.2⟩

/-- [node sec:charged-equations#timelike-ac-chain-rule]
The AC chain rule on an entire proper monotone timelike segment in the
original development. The initial incoming row is `U s` on every chart.
Compactness gives a positive coordinate separation; a finite mesh supplies
proper characteristic rectangles, and AC gluing retains the same density.
The explicit Lipschitz constants are local to this segment and are never
required uniformly at the missing endpoint. -/
theorem timelike_ac_chain_rule
    {ui e : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    {U V : ℝ → ℝ} {s t : ℝ} {KU KV LU LV : ℝ≥0} (hst : s < t)
    (hU : LipschitzOnWith KU U (uIcc s t)) (hV : LipschitzOnWith KV V (uIcc s t))
    (hUm : MonotoneOn U (uIcc s t)) (hVm : MonotoneOn V (uIcc s t))
    (hUa : AntilipschitzWith LU ((uIcc s t).domRestrict U))
    (hVa : AntilipschitzWith LV ((uIcc s t).domRestrict V))
    (hmem : ∀ x ∈ uIcc s t, (U x, V x) ∈ origDomain ui)
    (hproper : ∀ x ∈ uIcc s t, U x < V x) :
    let G : ℝ → ℝ → ℂ := fun u v =>
      (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) * (S.a u v - S.phi u v) +
        I * e * (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) * S.Q u v * S.phi u v -
        I * e * S.A u v * S.a u v
    AbsolutelyContinuousOnInterval (fun x => S.a (U x) (V x)) s t ∧
      ∀ᵐ x ∂volume.restrict (uIcc s t), HasDerivAt (fun y => S.a (U y) (V y))
        (deriv U x • G (U x) (V x) +
          deriv V x • densityRepresentative e S (U s) (U x) (V x)) x := by
  let G : ℝ → ℝ → ℂ := fun u v =>
    (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) * (S.a u v - S.phi u v) +
      I * e * (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) * S.Q u v * S.phi u v -
      I * e * S.A u v * S.a u v
  have cgap : ContinuousOn (fun x => V x - U x) (Icc s t) := by
    simpa only [uIcc_of_le hst.le] using! hV.continuousOn.sub hU.continuousOn
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hst.le) cgap
  let gap : ℝ := V x₀ - U x₀
  have hgap : 0 < gap := sub_pos.mpr (hproper x₀ (by rwa [uIcc_of_le hst.le]))
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 ((KU : ℝ) * (t - s) / gap))
  have hNp : 0 < (N : ℝ) := (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).trans hN
  have hNne : (N : ℝ) ≠ 0 := hNp.ne'
  have hstep : (KU : ℝ) * ((t - s) / N) < gap := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hNp).2
    have hh := (div_lt_iff₀ hgap).1 ((le_max_right _ _).trans_lt hN)
    simpa only [mul_comm] using hh
  let q : ℕ → ℝ := fun i => s + (i : ℝ) * ((t - s) / N)
  have hq0 : q 0 = s := by simp [q]
  have hqN : q N = t := by dsimp only [q]; field_simp [hNne]; ring
  have hqS : StrictMono q := by
    intro i j hij
    have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    exact add_lt_add_right (mul_lt_mul_of_pos_right hijR
      (div_pos (sub_pos.mpr hst) hNp)) s
  have hq := hqS.monotone
  have hqm (i : ℕ) (hi : i ≤ N) : q i ∈ uIcc s t := by
    rw [uIcc_of_le hst.le]
    exact ⟨by simpa only [hq0] using hq (Nat.zero_le i), by simpa only [hqN] using hq hi⟩
  have hlocal (i : ℕ) (hi : i < N) :
      AbsolutelyContinuousOnInterval (fun x => S.a (U x) (V x)) (q i) (q (i + 1)) ∧
        ∀ᵐ x ∂volume.restrict (Icc (q i) (q (i + 1))),
          HasDerivAt (fun y => S.a (U y) (V y))
            (deriv U x • G (U x) (V x) +
              deriv V x • densityRepresentative e S (U s) (U x) (V x)) x := by
    have him := hqm i hi.le
    have hjm := hqm (i + 1) hi
    have hsub := uIcc_subset_uIcc him hjm
    have hUi : AntilipschitzWith LU ((uIcc (q i) (q (i + 1))).domRestrict U) := by
      intro x y
      exact hUa ⟨x, hsub x.property⟩ ⟨y, hsub y.property⟩
    have hVi : AntilipschitzWith LV ((uIcc (q i) (q (i + 1))).domRestrict V) := by
      intro x y
      exact hVa ⟨x, hsub x.property⟩ ⟨y, hsub y.property⟩
    have hdx : q (i + 1) - q i = (t - s) / N := by dsimp only [q]; push_cast; ring
    have hdu := hU.dist_le_mul _ hjm _ him
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hUm him hjm (hq (Nat.le_succ i)))),
      Real.dist_eq, abs_of_pos (sub_pos.mpr (hqS (Nat.lt_succ_self i))), hdx] at hdu
    have hsmall : U (q (i + 1)) < V (q i) := by
      have hg : gap ≤ V (q i) - U (q i) :=
        hmin (by simpa only [uIcc_of_le hst.le] using him)
      linarith
    have hrect : Icc (U s) (U (q (i + 1))) ×ˢ Icc (V (q i)) (V (q (i + 1))) ⊆
        origDomain ui ∩ {p | p.1 < p.2} := by
      rintro ⟨u, v⟩ ⟨hu, hv⟩
      have huv := hu.2.trans_lt (hsmall.trans_le hv.1)
      have hv0 := hv.2.trans (hmem _ hjm).2.2.2
      exact ⟨⟨(hmem s left_mem_uIcc).1.trans hu.1, huv.trans_le hv0, huv.le, hv0⟩, huv⟩
    have hc := timelike_ac_chain_rule_on_rectangle hS (hqS (Nat.lt_succ_self i))
      (hU.mono hsub) (hV.mono hsub) (hUm.mono hsub) (hVm.mono hsub) hUi hVi
      (hUm left_mem_uIcc him (by simpa only [hq0] using hq (Nat.zero_le i))) hrect
    simpa only [uIcc_of_le (hq (Nat.le_succ i))] using! hc
  have hglue := glue_characteristic_chain_rule hq N hlocal
  simpa only [hq0, hqN, uIcc_of_le hst.le] using! hglue

end EmcsfAcExtension.Global.Calculus
