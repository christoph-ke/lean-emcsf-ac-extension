module

public import EmcsfAcExtension.Global.Exterior.FrontierLabel
public import EmcsfAcExtension.Global.Exterior.DerivativeSource
public import EmcsfAcExtension.Global.Calculus.DensityRepresentative
import EmcsfAcExtension.Infra.Density.CurveChain
import EmcsfAcExtension.Infra.AC.Intervals

/-! # The normalized scalar on proper exterior boundaries

The selected internal project record argument proves AC using the improved initial-density
label. Derivative identification uses the common good-label set and the
continuous incoming partial, as in internal project record (C7). No arbitrary product-a.e.
representative is evaluated on a curve. All constants here are local to a
proper rectangle, with no terminal uniformity assertion.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [node c:exterior#label-change-chain-rule-bridge]
On a proper positive-radius rectangular chart the normalized scalar trace
is AC by the improved label `v + ∫ |deriv (S.a a)|`. The canonical inverse
is 1-Lipschitz by `improved_label_properties`; the scalar is Lipschitz in
that label by the joint estimate used here. The four constants controlling
the boundary labels are explicit local inputs, never terminal assumptions.
Derivative identification uses the fixed-density representative at the
actual boundary. There are no new field hypotheses. -/
theorem label_change_chain_rule_bridge {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b : ℝ} {V : ℝ → ℝ} {K L : ℝ≥0}
    (hab : a < b) (hV : LipschitzOnWith K V (uIcc a b))
    (hm : MonotoneOn V (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict V))
    (hrect : Icc a b ×ˢ Icc (V a) (V b) ⊆ D ∩ {p | p.1 < p.2}) :
    let G : ℝ → ℝ → ℂ := fun u v =>
      (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) * (S.a u v - S.phi u v) +
        I * e * (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
          S.Q u v * S.phi u v - I * e * S.A u v * S.a u v
    (∃ M ≥ 0, ∃ C ≥ 0, ∀ u ∈ Icc a b, ∀ w ∈ Icc a b,
      ∀ v ∈ Icc (V a) (V b), ∀ z ∈ Icc (V a) (V b),
        dist (S.a u v) (S.a w z) ≤ M * dist u w + C *
          |(z + ∫ s in V a..z, ‖deriv (S.a a) s‖) -
            (v + ∫ s in V a..v, ‖deriv (S.a a) s‖)|) ∧
    AbsolutelyContinuousOnInterval (fun u => S.a u (V u)) a b ∧
      ∀ᵐ u ∂volume.restrict (uIcc a b), HasDerivAt (fun x => S.a x (V x))
        (G u (V u) + deriv V u • densityRepresentative e S a u (V u)) u := by
  let G : ℝ → ℝ → ℂ := fun u v =>
    (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) * (S.a u v - S.phi u v) +
      I * e * (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        S.Q u v * S.phi u v - I * e * S.A u v * S.a u v
  have hstrict : StrictMonoOn V (uIcc a b) := hm.strictMonoOn_of_injOn (by
    intro u hu v hv he
    exact congrArg Subtype.val (ha.injective (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) he))
  have hVV := hstrict left_mem_uIcc right_mem_uIcc hab
  have hbc : b < V a := (hrect (show (b, V a) ∈ Icc a b ×ˢ Icc (V a) (V b) from
    ⟨⟨hab.le, le_rfl⟩, ⟨le_rfl, hVV.le⟩⟩)).2
  have hG : ContinuousOn G.uncurry (Icc a b ×ˢ Icc (V a) (V b)) :=
    Calculus.continuousOn_normalized_incoming_source hS hrect
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hG.norm
  let B : ℝ≥0 := Real.toNNReal (max M 1)
  have hB : (B : ℝ) = max M 1 := Real.coe_toNNReal _ (le_trans zero_le_one (le_max_right _ _))
  have hin (v : ℝ) (hv : v ∈ Icc (V a) (V b)) :
      LipschitzOnWith B (fun u => S.a u v) (Icc a b) := by
    apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun u => G u v)
    · intro u hu
      apply Calculus.hasDerivWithinAt_of_characteristic_forms hab.le
        (hG.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, hv⟩))
        ?_ hu
      intro x hx
      have hs : inSeg a x v ⊆ D := by
        rintro ⟨y, z⟩ ⟨hy, hyx, rfl⟩
        exact (hrect ⟨⟨hy, hyx.trans hx.2⟩, hv⟩).1
      have hf := Calculus.constant_label_connector_calculus hS hx.1
        (hx.2.trans_lt (hbc.trans_le hv.1)) hs
      simpa only [Calculus.normalized_incoming_source_eq, G] using! hf
    · intro u hu
      apply NNReal.coe_le_coe.mp
      rw [coe_nnnorm, hB]
      exact (hM (mem_image_of_mem _ (show (u, v) ∈ Icc a b ×ˢ Icc (V a) (V b) from
        ⟨hu, hv⟩))).trans (le_max_left _ _)
  obtain ⟨P, R, hP, hR, heq, hprim⟩ := Calculus.exists_density_factors hS hab hVV hrect
  obtain ⟨C, hC, hbound⟩ := Density.exists_fixedDensity_bound hP hR
  have hinit := (hS.ac_out a (V a) (V b) hVV.le (by
    rintro ⟨u, v⟩ ⟨rfl, hv⟩
    exact (hrect ⟨⟨le_rfl, hab.le⟩, hv⟩).1)).2.2.2.2
  have hW (u : ℝ) (hu : u ∈ Icc a b) : IntervalIntegrable
      (Density.fixedDensity P R (deriv (S.a a)) u) volume (V a) (V b) :=
    Density.intervalIntegrable_fixedDensity hVV.le hu hP hR hinit.intervalIntegrable_deriv_complex
  have hout := outgoing_dist_le_improved_label_of_primitive hVV.le hC.le
    hinit.intervalIntegrable_deriv_complex hW (fun u hu v hv => by
      simpa only [add_comm] using hbound (deriv (S.a a)) u hu v hv) hprim
  have hac : AbsolutelyContinuousOnInterval (fun u => S.a u (V u)) a b := by
    apply trace_ac_of_improved_label_modulus hab.le B.coe_nonneg hC.le hV hm
      hinit.intervalIntegrable_deriv_complex
    intro u hu w hw
    have hu' : u ∈ uIcc a b := by rwa [uIcc_of_le hab.le]
    have hw' : w ∈ uIcc a b := by rwa [uIcc_of_le hab.le]
    have hVu : V u ∈ Icc (V a) (V b) := by
      simpa only [uIcc_of_le hVV.le] using hm.image_uIcc_subset ⟨u, hu', rfl⟩
    have hVw : V w ∈ Icc (V a) (V b) := by
      simpa only [uIcc_of_le hVV.le] using hm.image_uIcc_subset ⟨w, hw', rfl⟩
    have hh := add_le_add (hout u hu _ hVu _ hVw)
      ((hin (V w) hVw).dist_le_mul u hu w hw)
    exact (dist_triangle _ (S.a u (V w)) _).trans
      (by simpa only [add_comm] using hh)
  have hc := Calculus.timelike_ac_chain_rule_on_rectangle hS hab
    (LipschitzWith.id.lipschitzOnWith : LipschitzOnWith 1 id (uIcc a b)) hV
    (monotone_id.monotoneOn _) hm (AntilipschitzWith.id.domRestrict (uIcc a b)) ha
    le_rfl hrect
  refine ⟨⟨B, B.coe_nonneg, C, hC.le, ?_⟩, hac, ?_⟩
  · intro u hu w hw v hv z hz
    have ho := hout u hu v hv z hz
    rw [Real.dist_eq, abs_sub_comm] at ho
    have hh := add_le_add ho ((hin z hz).dist_le_mul u hu w hw)
    exact (dist_triangle _ (S.a u z) _).trans (by simpa only [add_comm] using hh)
  · filter_upwards [hc.2] with u hu
    simpa only [id_eq, (hasDerivAt_id u).deriv, one_smul] using! hu

/-- [node c:exterior#chain-rule-from-label-change]
The selected internal project record route wraps the joint Lipschitz estimate in the improved
fixed-density label and transports the boundary chain rule to the original
parameter. All local field estimates are proved in the bridge, and no
representation-only route is a conjunct. No constants occur in the rule.
-/
theorem chain_rule_from_label_change {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b : ℝ} {V : ℝ → ℝ} {K L : ℝ≥0}
    (hab : a < b) (hV : LipschitzOnWith K V (uIcc a b))
    (hm : MonotoneOn V (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict V))
    (hrect : Icc a b ×ˢ Icc (V a) (V b) ⊆ D ∩ {p | p.1 < p.2}) :
    let G : ℝ → ℝ → ℂ := fun u v =>
      (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) * (S.a u v - S.phi u v) +
        I * e * (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
          S.Q u v * S.phi u v - I * e * S.A u v * S.a u v
    AbsolutelyContinuousOnInterval (fun u => S.a u (V u)) a b ∧
      ∀ᵐ u ∂volume.restrict (uIcc a b), HasDerivAt (fun x => S.a x (V x))
        (G u (V u) + deriv V u • densityRepresentative e S a u (V u)) u := by
  exact (label_change_chain_rule_bridge hS hab hV hm ha hrect).2

private theorem ac_glue_mesh {f : ℝ → ℂ} {q : ℕ → ℝ} (hq : Monotone q) (N : ℕ)
    (h : ∀ i < N, AbsolutelyContinuousOnInterval f (q i) (q (i + 1))) :
    AbsolutelyContinuousOnInterval f (q 0) (q N) := by
  induction N with
  | zero => exact .refl _ _
  | succ N ih =>
    exact (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))).trans_complex
      (h N (Nat.lt_succ_self N)) (hq (Nat.zero_le _)) (hq (Nat.le_succ _))

/-- [node c:exterior#boundary-ac-chain-rule]
The selected improved-label chain rule on an entire proper increasing
bi-Lipschitz boundary segment in the original development. A finite mesh
places every subarc in a proper rectangle, where the internal project record label argument
proves AC. Concatenation proves AC on the whole segment. The common-density
calculus identifies its derivative with the representative anchored at the
single initial row `a`. The displayed label constants are local to the
proper segment; no uniform terminal Lipschitz bound is required. -/
theorem boundary_ac_chain_rule {ui e : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) {a b : ℝ} {V : ℝ → ℝ} {K L : ℝ≥0}
    (hab : a < b) (hV : LipschitzOnWith K V (uIcc a b))
    (hm : MonotoneOn V (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict V))
    (hmem : ∀ x ∈ uIcc a b, (x, V x) ∈ origDomain ui)
    (hproper : ∀ x ∈ uIcc a b, x < V x) :
    let G : ℝ → ℝ → ℂ := fun u v =>
      (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) * (S.a u v - S.phi u v) +
        I * e * (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
          S.Q u v * S.phi u v - I * e * S.A u v * S.a u v
    AbsolutelyContinuousOnInterval (fun u => S.a u (V u)) a b ∧
      ∀ᵐ u ∂volume.restrict (uIcc a b), HasDerivAt (fun x => S.a x (V x))
        (G u (V u) + deriv V u • densityRepresentative e S a u (V u)) u := by
  have cgap : ContinuousOn (fun x => V x - x) (Icc a b) := by
    simpa only [uIcc_of_le hab.le, Pi.sub_apply, id_eq] using!
      hV.continuousOn.sub continuousOn_id
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) cgap
  let gap := V x₀ - x₀
  have hgap : 0 < gap := sub_pos.mpr (hproper x₀ (by rwa [uIcc_of_le hab.le]))
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 ((b - a) / gap))
  have hNp : 0 < (N : ℝ) := (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).trans hN
  have hNne : (N : ℝ) ≠ 0 := hNp.ne'
  have hstep : (b - a) / N < gap := by
    apply (div_lt_iff₀ hNp).2
    have hh := (div_lt_iff₀ hgap).1 ((le_max_right _ _).trans_lt hN)
    simpa only [mul_comm] using hh
  let q : ℕ → ℝ := fun i => a + (i : ℝ) * ((b - a) / N)
  have hq0 : q 0 = a := by simp [q]
  have hqN : q N = b := by dsimp only [q]; field_simp [hNne]; ring
  have hqS : StrictMono q := by
    intro i j hij
    have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    exact add_lt_add_right (mul_lt_mul_of_pos_right hijR
      (div_pos (sub_pos.mpr hab) hNp)) a
  have hq := hqS.monotone
  have hqm (i : ℕ) (hi : i ≤ N) : q i ∈ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact ⟨by simpa only [hq0] using hq (Nat.zero_le i), by simpa only [hqN] using hq hi⟩
  have hlocal (i : ℕ) (hi : i < N) :
      AbsolutelyContinuousOnInterval (fun x => S.a x (V x)) (q i) (q (i + 1)) := by
    have him := hqm i hi.le
    have hjm := hqm (i + 1) hi
    have hsub := uIcc_subset_uIcc him hjm
    have hVi : AntilipschitzWith L ((uIcc (q i) (q (i + 1))).domRestrict V) := by
      intro x y
      exact ha ⟨x, hsub x.property⟩ ⟨y, hsub y.property⟩
    have hdx : q (i + 1) - q i = (b - a) / N := by dsimp only [q]; push_cast; ring
    have hsmall : q (i + 1) < V (q i) := by
      have hg : gap ≤ V (q i) - q i := hmin (by simpa only [uIcc_of_le hab.le] using him)
      linarith only [hg, hdx, hstep]
    have hrect : Icc (q i) (q (i + 1)) ×ˢ Icc (V (q i)) (V (q (i + 1))) ⊆
        origDomain ui ∩ {p | p.1 < p.2} := by
      rintro ⟨u, v⟩ ⟨hu, hv⟩
      have huv := hu.2.trans_lt (hsmall.trans_le hv.1)
      have hv0 := hv.2.trans (hmem _ hjm).2.2.2
      exact ⟨⟨(hmem _ him).1.trans hu.1, huv.trans_le hv0, huv.le, hv0⟩, huv⟩
    exact (chain_rule_from_label_change hS (hqS (Nat.lt_succ_self i))
      (hV.mono hsub) (hm.mono hsub) hVi hrect).1
  have hac : AbsolutelyContinuousOnInterval (fun u => S.a u (V u)) a b := by
    simpa only [hq0, hqN] using ac_glue_mesh hq N hlocal
  have hc := Calculus.timelike_ac_chain_rule hS hab
    (LipschitzWith.id.lipschitzOnWith : LipschitzOnWith 1 id (uIcc a b)) hV
    (monotone_id.monotoneOn _) hm (AntilipschitzWith.id.domRestrict (uIcc a b)) ha hmem hproper
  refine ⟨hac, ?_⟩
  filter_upwards [hc.2] with u hu
  simpa only [id_eq, (hasDerivAt_id u).deriv, one_smul] using! hu

end EmcsfAcExtension.Global.Exterior
