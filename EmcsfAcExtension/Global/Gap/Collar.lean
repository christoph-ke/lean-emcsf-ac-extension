/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Gap.Crossing
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # The fractional-radius moving collar

The inner label is selected by the actual area radius of a frozen-class
solution. Existence and continuity use the complete outgoing rows and positive
expansion; no regularity of an independently chosen curve is assumed.
Source: charged_SF_new_version.tex:L1668–1682.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Annulus

/-- [internal] Every strict fractional radius has a unique incoming label on
the complete outgoing row. -/
theorem fractional_radius_point {e u₀ b d : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) {u v₂ : ℝ}
    (hu : u₀ ≤ u) (huv : u < v₂) (hb : v₂ ≤ b) (hd : 0 < d ∧ d < 1) :
    ∃! w, w ∈ Ioo u v₂ ∧ S.r u w = (1 - d) * S.r u v₂ := by
  have hs : outSeg u u v₂ ⊆ triangle u₀ b :=
    (outSeg_subset_triangle_iff huv.le).2 ⟨hu, le_rfl, hb⟩
  have hc := Calculus.continuousOn_out_section hS.cont_r hs
  have hz := (hS.axis u ⟨hu, le_rfl, huv.le.trans hb⟩).1
  have hR := hS.r_pos (u, v₂) ⟨hu, huv.le, hb⟩ huv
  have htarget : 0 < (1 - d) * S.r u v₂ := mul_pos (sub_pos.mpr hd.2) hR
  have htarget' : (1 - d) * S.r u v₂ < S.r u v₂ := by
    nlinarith only [mul_pos hd.1 hR]
  obtain ⟨w, hw, heq⟩ := intermediate_value_Icc huv.le hc
    ⟨by simpa only [hz] using htarget.le, htarget'.le⟩
  have huw : u < w := by
    refine lt_of_le_of_ne hw.1 ?_
    rintro rfl
    rw [hz] at heq
    linarith only [heq, htarget]
  have hwv : w < v₂ := by
    refine lt_of_le_of_ne hw.2 ?_
    intro he
    rw [he] at heq
    linarith only [heq, htarget']
  refine ⟨w, ⟨⟨huw, hwv⟩, heq⟩, ?_⟩
  intro z hz'
  have hmono : StrictMonoOn (S.r u) (Icc u v₂) := by
    intro x hx y hy hxy
    exact radius_out_lt hS hx.1 hxy
      ((outSeg_subset_triangle_iff hxy.le).2 ⟨hu, hx.1, hy.2.trans hb⟩)
  exact hmono.injOn ⟨hz'.1.1.le, hz'.1.2.le⟩ hw (hz'.2.trans heq.symm)

/-- [internal] Equal radii on one complete outgoing row have equal labels. -/
theorem radius_out_injOn {e u₀ b : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) {u v₂ : ℝ}
    (hu : u₀ ≤ u) (_huv : u < v₂) (hb : v₂ ≤ b) :
    InjOn (S.r u) (Icc u v₂) := by
  have hmono : StrictMonoOn (S.r u) (Icc u v₂) := by
    intro x hx y hy hxy
    exact radius_out_lt hS hx.1 hxy
      ((outSeg_subset_triangle_iff hxy.le).2 ⟨hu, hx.1, hy.2.trans hb⟩)
  exact hmono.injOn

/-- [internal] The fractional-radius label varies continuously on any proper
closed incoming interval. No gap or charge bound is needed for this result. -/
theorem moving_collar_continuousOn {e u₀ b d : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) {a τ v₂ : ℝ}
    (ha : u₀ ≤ a) (_haτ : a ≤ τ) (hτv : τ < v₂) (hb : v₂ ≤ b)
    (_hd : 0 < d ∧ d < 1) {V : ℝ → ℝ}
    (hV : ∀ u ∈ Icc a τ, V u ∈ Ioo u v₂ ∧ S.r u (V u) = (1 - d) * S.r u v₂) :
    ContinuousOn V (Icc a τ) := by
  have hspec (u : Icc a τ) := hV u u.property
  let f : Icc a τ → Icc a v₂ := fun u =>
    ⟨V u,
      ⟨u.property.1.trans (hspec u).1.1.le, (hspec u).1.2.le⟩⟩
  let T : Set ((Icc a τ) × (Icc a v₂)) := {p | (p.1 : ℝ) ≤ (p.2 : ℝ)}
  have cu : Continuous (fun p : (Icc a τ) × (Icc a v₂) => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have cv : Continuous (fun p : (Icc a τ) × (Icc a v₂) => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hT : IsClosed T := isClosed_le cu cv
  have cr : ContinuousOn (fun p : (Icc a τ) × (Icc a v₂) =>
      S.r p.1 p.2) T :=
    hS.cont_r.comp (cu.prodMk cv).continuousOn
      (fun p hp => ⟨ha.trans p.1.property.1, hp, p.2.property.2.trans hb⟩)
  have ctarget : Continuous (fun p : (Icc a τ) × (Icc a v₂) => S.r p.1 v₂) :=
    hS.cont_r.comp_continuous (cu.prodMk continuous_const)
      (fun p => ⟨ha.trans p.1.property.1, (p.1.property.2.trans_lt hτv).le, hb⟩)
  have cg : ContinuousOn (fun p : (Icc a τ) × (Icc a v₂) =>
      S.r p.1 p.2 - (1 - d) * S.r p.1 v₂) T :=
    cr.sub (continuousOn_const.mul ctarget.continuousOn)
  have hgraph : f.graph = T ∩
      (fun p : (Icc a τ) × (Icc a v₂) =>
        S.r p.1 p.2 - (1 - d) * S.r p.1 v₂) ⁻¹' {0} := by
    ext p
    change (f p.1 = p.2) ↔
      (p.1 : ℝ) ≤ (p.2 : ℝ) ∧ S.r p.1 p.2 - (1 - d) * S.r p.1 v₂ = 0
    constructor
    · intro hp
      have he := congrArg Subtype.val hp
      change V p.1 = (p.2 : ℝ) at he
      rw [← he]
      exact ⟨(hspec p.1).1.1.le, sub_eq_zero.mpr (hspec p.1).2⟩
    · intro hp
      apply Subtype.ext
      apply radius_out_injOn hS (ha.trans p.1.property.1)
        (p.1.property.2.trans_lt hτv) hb
        ⟨(hspec p.1).1.1.le, (hspec p.1).1.2.le⟩ ⟨hp.1, p.2.property.2⟩
      exact (hspec p.1).2.trans (sub_eq_zero.mp hp.2).symm
  have hf : Continuous f := continuous_of_isClosed_graph (by
    rw [hgraph]
    exact cg.preimage_isClosed_of_isClosed hT isClosed_singleton)
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp hf

/-- [internal] A complete triangle supplies a continuous moving inner label
with exactly the prescribed fractional radius. The witness is local to the
conclusion; no globally chosen radial inverse is introduced. -/
theorem moving_collar_exists {e u₀ b d : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) {a τ v₂ : ℝ}
    (ha : u₀ ≤ a) (haτ : a ≤ τ) (hτv : τ < v₂) (hb : v₂ ≤ b)
    (hd : 0 < d ∧ d < 1) :
    ∃ V : ℝ → ℝ,
      (∀ u ∈ Icc a τ, V u ∈ Ioo u v₂ ∧ S.r u (V u) = (1 - d) * S.r u v₂) ∧
      ContinuousOn V (Icc a τ) := by
  classical
  have hex (u : ℝ) : ∃ w, u ∈ Icc a τ →
      w ∈ Ioo u v₂ ∧ S.r u w = (1 - d) * S.r u v₂ := by
    by_cases hu : u ∈ Icc a τ
    · obtain ⟨w, hw, _⟩ := fractional_radius_point hS (ha.trans hu.1)
        (hu.2.trans_lt hτv) hb hd
      exact ⟨w, fun _ => hw⟩
    · exact ⟨u, fun h => False.elim (hu h)⟩
  choose V hV using hex
  exact ⟨V, hV, moving_collar_continuousOn hS ha haτ hτv hb hd hV⟩

end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Annulus

open Filter
open scoped Topology

private theorem implicit_graph_hasDerivAt {f : ℝ × ℝ → ℝ} {V : ℝ → ℝ} {x A B : ℝ}
    (hf : HasStrictFDerivAt f
      ((ContinuousLinearMap.toSpanSingleton ℝ A).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ B)) (x, V x))
    (hB : B ≠ 0) (hV : ContinuousAt V x)
    (heq : ∀ᶠ t in 𝓝 x, f (t, V t) = f (x, V x)) :
    HasDerivAt V (-A / B) x := by
  let P : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.toSpanSingleton ℝ A).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ B)
  let R : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ B
  let Ri : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ B⁻¹
  have hR : P ∘L ContinuousLinearMap.inr ℝ ℝ ℝ = R := by
    ext
    simp [P, R]
  have hL : P ∘L ContinuousLinearMap.inl ℝ ℝ ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ A := by
    ext
    simp [P]
  have hRi : R ∘L Ri = ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [R, Ri, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, hB]
  have hiR : Ri ∘L R = ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp [R, Ri, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, hB]
  have hInv : R.inverse = Ri := ContinuousLinearMap.inverse_eq hRi hiR
  have hInvert : (P ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hR]
    exact ContinuousLinearMap.IsInvertible.of_inverse hRi hiR
  let ψ := hf.implicitFunctionOfProdDomain hInvert
  have hiff := hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInvert
  have ht : Tendsto (fun t => (t, V t)) (𝓝 x) (𝓝 (x, V x)) :=
    (continuousAt_id.prodMk hV).tendsto
  have hsame : V =ᶠ[𝓝 x] ψ := by
    filter_upwards [ht.eventually hiff, heq] with t ht he
    exact (ht.mp he).symm
  have hd := hf.hasStrictFDerivAt_implicitFunctionOfProdDomain hInvert
  have hlin : (-(P ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).inverse ∘L
      (P ∘L ContinuousLinearMap.inl ℝ ℝ ℝ)) =
      ContinuousLinearMap.toSpanSingleton ℝ (-A / B) := by
    rw [hR, hL, hInv]
    ext
    simp [Ri, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  change HasStrictFDerivAt ψ _ x at hd
  rw [hlin] at hd
  have hd' : HasDerivAt ψ (-A / B) x := by
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using hd.hasFDerivAt.hasDerivAt
  exact hd'.congr_of_eventuallyEq hsame

/-- [internal]
The derivative of an actual continuous fractional-radius collar is forced by
its radius identity. Continuity and differentiability of the prescribed radius
partials are derived from the frozen equations; no curve derivative is assumed. -/
theorem moving_collar_hasDerivAt {e u₀ b d : ℝ} {S : Fields} {V : ℝ → ℝ}
    (hS : IsSolution e S (triangle u₀ b)) {a τ v₂ u : ℝ}
    (ha : u₀ ≤ a) (hb : v₂ ≤ b)
    (hV : ∀ t ∈ Icc a τ, V t ∈ Ioo t v₂ ∧ S.r t (V t) = (1 - d) * S.r t v₂)
    (hc : ContinuousOn V (Icc a τ)) (hu : u ∈ Ioo a τ) :
    HasDerivAt V (((1 - d) * S.nu u v₂ - S.nu u (V u)) / S.lam u (V u)) u := by
  have hsp := hV u ⟨hu.1.le, hu.2.le⟩
  let U := {p : ℝ × ℝ | u₀ < p.1 ∧ p.1 < p.2 ∧ p.2 < v₂}
  have ho : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_snd).inter (isOpen_lt continuous_snd continuous_const))
  have hp : (u, V u) ∈ U := ⟨ha.trans_lt hu.1, hsp.1⟩
  have hsub : U ⊆ triangle u₀ b :=
    fun _ hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le.trans hb⟩
  let f (p : ℝ × ℝ) := S.r p.1 p.2 - (1 - d) * S.r p.1 v₂
  let A := S.nu u (V u) - (1 - d) * S.nu u v₂
  let L : ℝ → (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toSpanSingleton ℝ
  have cL : Continuous L := ContinuousLinearMap.toSpanSingletonCLE.continuous
  have cν := hS.cont_nu.mono hsub
  have ctop : ContinuousOn (fun p : ℝ × ℝ => S.nu p.1 v₂) U :=
    hS.cont_nu.comp (continuous_fst.prodMk continuous_const).continuousOn
      (fun p hp => ⟨hp.1.le, hp.2.1.le.trans hp.2.2.le, hb⟩)
  have hf : HasStrictFDerivAt f
      ((L A).coprod (L (S.lam u (V u)))) (u, V u) := by
    apply hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (u, V u))
      (f := fun x y => S.r x y - (1 - d) * S.r x v₂)
      (f₁ := fun x y => L (S.nu x y - (1 - d) * S.nu x v₂))
      (f₂ := fun x y => L (S.lam x y))
    · filter_upwards [ho.eventually_mem hp] with q hq
      have hs : inSeg u₀ q.2 q.2 ⊆ triangle u₀ b := by
        rintro ⟨x, y⟩ ⟨hx, hxy, rfl⟩
        exact ⟨hx, hxy, hq.2.2.le.trans hb⟩
      have ht : inSeg u₀ v₂ v₂ ⊆ triangle u₀ b := by
        rintro ⟨x, y⟩ ⟨hx, hxy, rfl⟩
        exact ⟨hx, hxy, hb⟩
      exact ((radius_in_hasDerivAt hS le_rfl hs ⟨hq.1, hq.2.1⟩).sub
        ((radius_in_hasDerivAt hS le_rfl ht ⟨hq.1, hq.2.1.trans hq.2.2⟩).const_mul
          (1 - d))).hasFDerivAt
    · filter_upwards [ho.eventually_mem hp] with q hq
      have hs : outSeg q.1 q.1 b ⊆ triangle u₀ b := by
        rintro ⟨x, y⟩ ⟨rfl, hxy, hy⟩
        exact ⟨hq.1.le, hxy, hy⟩
      exact ((Local.IsSolution.hasDerivAt_radius_out hS hs
        ⟨hq.2.1, hq.2.2.trans_le hb⟩).sub_const ((1 - d) * S.r q.1 v₂)).hasFDerivAt
    · exact (cL.comp_continuousOn (cν.sub (continuousOn_const.mul ctop))).continuousAt
        (ho.mem_nhds hp)
    · exact (cL.comp_continuousOn (hS.cont_lam.mono hsub)).continuousAt (ho.mem_nhds hp)
  have hd := implicit_graph_hasDerivAt hf
    (hS.lam_pos (u, V u) (hsub hp)).ne'
    (hc.continuousAt (Icc_mem_nhds hu.1 hu.2)) (by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with t ht
      dsimp [f]
      rw [(hV t ⟨ht.1.le, ht.2.le⟩).2, hsp.2]
      ring)
  convert hd using 1
  dsimp [A]
  ring

/-- [internal]
The actual continuous partial incoming flux on a nonincreasing differentiable
positive-radius graph is controlled by its initial ordinary mass. -/
theorem moving_inner_budget_of_derivative {e u₀ b d : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b))
    (hmu : ∀ p ∈ triangle u₀ b, 0 ≤ S.mu p.1 p.2)
    {a τ v₂ : ℝ} (ha : u₀ ≤ a) (haτ : a ≤ τ) (_hτv : τ < v₂) (hb : v₂ ≤ b)
    {V V' : ℝ → ℝ} (hVc : ContinuousOn V (Icc a τ))
    (hV : ∀ u ∈ Icc a τ, V u ∈ Ioo u v₂ ∧ S.r u (V u) = (1 - d) * S.r u v₂)
    (hVder : ∀ u ∈ Ioo a τ, HasDerivAt V (V' u) u)
    (hVsign : ∀ u ∈ Ioo a τ, V' u ≤ 0) :
    IntervalIntegrable (fun u => -S.mU u (V u)) volume a τ ∧
      ∀ t ∈ Icc a τ, (∫ u in a..t, -S.mU u (V u)) ≤ (1 - d) * S.r a v₂ / 2 := by
  have hmap : MapsTo (fun u => (u, V u)) (Icc a τ)
      (triangle u₀ b ∩ {p | p.1 < p.2}) := by
    intro u hu
    exact ⟨⟨ha.trans hu.1, (hV u hu).1.1.le, (hV u hu).1.2.le.trans hb⟩, (hV u hu).1.1⟩
  have cgraph : ContinuousOn (fun u => (u, V u)) (Icc a τ) := continuousOn_id.prodMk hVc
  have cM : ContinuousOn (fun u => S.m u (V u)) (Icc a τ) :=
    hS.cont_m.comp cgraph (fun u hu => (hmap hu).1)
  have cF : ContinuousOn (fun u => -S.mU u (V u)) (Icc a τ) :=
    ((Gap.continuousOn_mass_sources hS).1.comp cgraph hmap).neg
  have hFi := cF.intervalIntegrable_of_Icc (μ := volume) haτ
  let P (u : ℝ) := S.m u (V u) + ∫ x in a..u, -S.mU x (V x)
  have cP : ContinuousOn P (Icc a τ) := cM.add (by
    simpa only [uIcc_of_le haτ] using
      (hFi.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc).continuousOn)
  have dP (u : ℝ) (hu : u ∈ Ioo a τ) :
      HasDerivAt P (S.mV u (V u) * V' u) u := by
    have hu' : u ∈ Icc a τ := ⟨hu.1.le, hu.2.le⟩
    have hm := Gap.mass_curve_hasDerivAt hS (ha.trans_lt hu.1)
      (hV u hu').1.1 ((hV u hu').1.2.trans_le hb) (hVder u hu)
    have huab : u ∈ uIcc a τ := by simpa only [uIcc_of_le haτ] using hu'
    have hprim := intervalIntegral.integral_hasDerivAt_right
      (hFi.mono_set (uIcc_subset_uIcc left_mem_uIcc huab))
      ((cF.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo u hu)
      (cF.continuousAt (Icc_mem_nhds hu.1 hu.2))
    convert hm.add hprim using 1; ring
  have hanti : AntitoneOn P (Icc a τ) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun u => S.mV u (V u) * V' u)
      (convex_Icc a τ) cP
    · intro u hu
      rw [interior_Icc] at hu
      exact (dP u hu).hasDerivWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hp := (hmap (show u ∈ Icc a τ from ⟨hu.1.le, hu.2.le⟩)).1
      exact mul_nonpos_of_nonneg_of_nonpos (Gap.mass_monotonicity hS hp).2 (hVsign u hu)
  refine ⟨hFi, ?_⟩
  intro t ht
  have h := hanti ⟨le_rfl, haτ⟩ ht ht.1
  dsimp [P] at h
  rw [intervalIntegral.integral_same, add_zero] at h
  have hpt := (hmap ht).1
  have hpa := (hmap (show a ∈ Icc a τ from ⟨le_rfl, haτ⟩)).1
  have hrt := hS.r_pos (t, V t) hpt (hV t ht).1.1
  have hra := hS.r_pos (a, V a) hpa (hV a ⟨le_rfl, haτ⟩).1.1
  have hmt : 0 ≤ S.m t (V t) := by
    have hh := (le_div_iff₀ hrt).mp (hmu (t, V t) hpt)
    linarith only [hh]
  have hma : S.m a (V a) < S.r a (V a) / 2 := by
    have hh := (div_lt_iff₀ hra).mp (sub_pos.mp (hS.one_sub_mu_pos (a, V a) hpa))
    linarith only [hh]
  rw [(hV a ⟨le_rfl, haτ⟩).2] at hma
  linarith only [h, hmt, hma]

/-- [internal] The optical endpoint comparison gives the sign of the actual
fractional-radius collar velocity. -/
theorem moving_collar_velocity_nonpos_of_optical_bound
    {e u₀ b d : ℝ} {S : Fields} {V : ℝ → ℝ}
    (hS : IsSolution e S (triangle u₀ b)) {a τ v₂ u : ℝ}
    (ha : u₀ ≤ a) (hb : v₂ ≤ b)
    (hV : ∀ t ∈ Icc a τ, V t ∈ Ioo t v₂ ∧ S.r t (V t) = (1 - d) * S.r t v₂)
    (hopt : ∀ t ∈ Icc a τ, -S.nu t (V t) ≤ (1 - d) * (-S.nu t v₂))
    (hu : u ∈ Icc a τ) :
    ((1 - d) * S.nu u v₂ - S.nu u (V u)) / S.lam u (V u) ≤ 0 := by
  have hp : (u, V u) ∈ triangle u₀ b :=
    ⟨ha.trans hu.1, (hV u hu).1.1.le, (hV u hu).1.2.le.trans hb⟩
  apply div_nonpos_of_nonpos_of_nonneg _ (hS.lam_pos (u, V u) hp).le
  linarith only [hopt u hu]

/-- [internal] The exact moving inner mass
budget once the optical endpoint comparison has been supplied. All curve
derivatives and flux integrability are proved from the frozen solution class.
The coefficient `(1-d)/2` is uniform in all solution and triangle data. -/
theorem moving_inner_budget_of_optical_bound {e u₀ b d : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b))
    (hmu : ∀ p ∈ triangle u₀ b, 0 ≤ S.mu p.1 p.2)
    {a τ v₂ : ℝ} (ha : u₀ ≤ a) (haτ : a ≤ τ) (hτv : τ < v₂) (hb : v₂ ≤ b)
    (hd : 0 < d ∧ d < 1) {V : ℝ → ℝ}
    (hV : ∀ u ∈ Icc a τ, V u ∈ Ioo u v₂ ∧ S.r u (V u) = (1 - d) * S.r u v₂)
    (hopt : ∀ u ∈ Icc a τ, -S.nu u (V u) ≤ (1 - d) * (-S.nu u v₂)) :
    IntervalIntegrable (fun u => -S.mU u (V u)) volume a τ ∧
      ∀ t ∈ Icc a τ, (∫ u in a..t, -S.mU u (V u)) ≤ (1 - d) * S.r a v₂ / 2 := by
  have hc := moving_collar_continuousOn hS ha haτ hτv hb hd hV
  apply moving_inner_budget_of_derivative hS hmu ha haτ hτv hb hc hV
    (fun u hu => moving_collar_hasDerivAt hS ha hb hV hc hu)
  intro u hu
  exact moving_collar_velocity_nonpos_of_optical_bound hS ha hb hV hopt
    ⟨hu.1.le, hu.2.le⟩

end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Annulus

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [internal] Collar expansion makes `(-ν)/r` nondecreasing, so its
inner endpoint obeys the exact optical contraction bound. -/
theorem collar_optical_ratio_of_expansion (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hexp : ∀ v ∈ Icc a b,
      1 ≤ (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) :
    (-S.nu u a) ≤ (S.r u a / S.r u b) * (-S.nu u b) := by
  have hp (v : ℝ) (hv : v ∈ Icc a b) : (u,v) ∈ D := hs ⟨rfl,hv⟩
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have hr v (hv : v ∈ Icc a b) := hS.r_pos (u,v) (hp v hv) (hua.trans_le hv.1)
  have hd v (hv : v ∈ Ioo a b) : HasDerivAt (fun t => -S.nu u t / S.r u t)
      (S.lam u v * (-S.nu u v) / S.r u v ^ 2 *
        (((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) - 1)) v := by
    have dr : HasDerivAt (S.r u) (S.lam u v) v := by
      apply Local.hasDerivAt_of_integralForm_interior hv (cl.mono Ioo_subset_Icc_self)
      intro c d hc hcd hd
      exact (hS.eq_out u c d (hua.trans hc) hcd (by
        rintro ⟨s,t⟩ ⟨rfl,hmem⟩
        exact hs ⟨rfl,hc.le.trans hmem.1,hmem.2.trans hd.le⟩)).1
    have hv' := Ioo_subset_Icc_self hv
    have hn := (hS.nu_neg (u,v) (hp v hv')).ne
    have hg := (hS.one_sub_mu_pos (u,v) (hp v hv')).ne'
    have hh := (Gap.nu_out_hasDerivAt hS hua hs hv).neg.div dr (hr v hv').ne'
    convert hh using 1; dsimp only [Pi.neg_apply,Pi.div_apply,Fields.rUV];
      field_simp [(hr v hv').ne',hg]; ring
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc a b)
    (cn.neg.div cr (fun v hv => (hr v hv).ne'))
    (fun v hv => (hd v
        (by simpa only [interior_Icc] using hv)).differentiableAt.differentiableWithinAt)
    (fun v hv => by
      have hv' : v ∈ Ioo a b := by simpa only [interior_Icc] using hv
      change 0 ≤ deriv (fun t => -S.nu u t / S.r u t) v
      rw [(hd v hv').deriv]
      have hv'' := Ioo_subset_Icc_self hv'
      exact mul_nonneg (div_nonneg (mul_nonneg
        (hS.lam_pos (u,v) (hp v hv'')).le (neg_nonneg.mpr (hS.nu_neg (u,v) (hp v hv'')).le))
        (sq_nonneg _)) (sub_nonneg.mpr (hexp v hv'')))
  have ha : a ∈ Icc a b := ⟨le_rfl,hab⟩
  have hb : b ∈ Icc a b := ⟨hab,le_rfl⟩
  have hh := hm ha hb hab
  change (-S.nu u a) / S.r u a ≤ (-S.nu u b) / S.r u b at hh
  calc
    _ ≤ ((-S.nu u b) / S.r u b) * S.r u a := (div_le_iff₀ (hr a ha)).mp hh
    _ = _ := by ring


end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Gap


private theorem log_seven_lt_two : Real.log 7 < 2 := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr (by linarith only [h])
/-- [internal]
The numerical collar gap is strictly less than `7/16` for every fractional
width in `(0,1/8]`. The bound is independent of all solution data. -/
theorem collar_rational_bound {s : ℝ} (hs : 0 < s) (hsd : s ≤ 1 / 8) :
    (1 / 256 + 2 / 1024 + s + (1 + 2 / 1024) * s * Real.log ((1 - s) / s)) /
      (1 - s) < (7 / 16 : ℝ) := by
  have h1s : 0 < 1 - s := by linarith only [hsd]
  have hy : 0 < (1 - s) / s := div_pos h1s hs
  have ht := Real.log_le_sub_one_of_pos (div_pos hy (show (0 : ℝ) < 7 by norm_num))
  rw [Real.log_div hy.ne' (show (7 : ℝ) ≠ 0 by norm_num)] at ht
  have hlog : Real.log ((1 - s) / s) < 1 + ((1 - s) / s) / 7 := by
    linarith only [ht, log_seven_lt_two]
  have hprod := (mul_lt_mul_of_pos_left hlog hs)
  have hid : s * (1 + ((1 - s) / s) / 7) = (1 + 6 * s) / 7 := by
    field_simp [hs.ne']
    ring
  rw [hid] at hprod
  apply (div_lt_iff₀ h1s).mpr
  have hc := mul_lt_mul_of_pos_left hprod (show (0 : ℝ) < 1 + 2 / 1024 by norm_num)
  linarith only [hc, hsd]


/-- [node cg:collar-gap]
The exact inner-collar gap bound, uniformly over the coupling, solution,
bootstrap gap, triangle, and every fractional width in `(0,1/8]`. -/
theorem collar_gap {e δ u₀ b s : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ p ∈ triangle u₀ b, 0 ≤ S.mu p.1 p.2)
    (hgap : ∀ p ∈ triangle u₀ b, δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ p ∈ triangle u₀ b, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64)
    {u v₁ v₂ : ℝ} (hu : u₀ ≤ u) (huv : u < v₁) (hv : v₁ < v₂) (hb : v₂ ≤ b)
    (hs : 0 < s ∧ s ≤ 1 / 8)
    (hinit : S.r u v₁ = (1 - s) * S.r u v₂)
    (hout : 1 - S.mu u v₂ ≤ 1 / 256) :
    1 - S.mu u v₁ ≤
      (1 / 256 + 2 / 1024 + s + (1 + 2 / 1024) * s * Real.log ((1 - s) / s)) /
        (1 - s) ∧
    (1 / 256 + 2 / 1024 + s + (1 + 2 / 1024) * s * Real.log ((1 - s) / s)) /
        (1 - s) < (7 / 16 : ℝ) := by
  have ha := Annulus.annular_bound hS hδ hmu hgap hsmall hu huv hv hb
    ⟨hs.1, by linarith only [hs.2]⟩ hinit
  have hR := hS.r_pos (u,v₂) ⟨hu,(huv.trans hv).le,hb⟩ (huv.trans hv)
  have h1s : 0 < 1 - s := by linarith only [hs.2]
  have heq : 1 - S.mu u v₁ =
      ((1 - S.mu u v₂) - s + 2 * (S.m u v₂ - S.m u v₁) / S.r u v₂) / (1-s) := by
    dsimp [Fields.mu]
    rw [hinit]
    field_simp [hR.ne', h1s.ne']
    ring
  refine ⟨?_,collar_rational_bound hs.1 hs.2⟩
  rw [heq]
  apply div_le_div_of_nonneg_right _ h1s.le
  linarith only [ha,hout]
/-- [node cg:collar-expansion]
The charged radial expansion is strictly larger than one on the closed
one-eighth collar of a sphere whose gap is at most `1/256`. Both lower bounds
are literal, uniform numerical constants. -/
theorem collar_expansion {e δ u₀ b : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ p ∈ triangle u₀ b, 0 ≤ S.mu p.1 p.2)
    (hgap : ∀ p ∈ triangle u₀ b, δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ p ∈ triangle u₀ b, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64)
    {u v₁ v₂ : ℝ} (hu : u₀ ≤ u) (huv : u < v₁) (hv : v₁ < v₂) (hb : v₂ ≤ b)
    (hinit : S.r u v₁ = (1 - (1 / 8 : ℝ)) * S.r u v₂)
    (hout : 1 - S.mu u v₂ ≤ 1 / 256) :
    ∀ v ∈ Icc v₁ v₂,
      (1 - (1 / 1024 : ℝ)) * (9 / 7) ≤
        (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v) ∧
      1 < (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v) := by
  intro v hvmem
  have hp : (u,v) ∈ triangle u₀ b := ⟨hu,huv.le.trans hvmem.1,hvmem.2.trans hb⟩
  have hge : 0 < 1 - S.mu u v := hS.one_sub_mu_pos (u,v) hp
  have hR := hS.r_pos (u,v₂) ⟨hu,(huv.trans hv).le,hb⟩ (huv.trans hv)
  have hgsmall : 1 - S.mu u v < (7 / 16 : ℝ) := by
    rcases eq_or_lt_of_le hvmem.2 with he | he
    · subst v
      linarith only [hout]
    · let s := (S.r u v₂ - S.r u v) / S.r u v₂
      have hRlt := Annulus.radius_out_lt hS (huv.le.trans hvmem.1) he (by
        rintro ⟨x,y⟩ ⟨rfl,hvy,hyv⟩
        exact ⟨hu,(huv.le.trans hvmem.1).trans hvy,hyv.trans hb⟩)
      have hRle := radius_out_le hS huv.le hvmem.1 (by
        rintro ⟨x,y⟩ ⟨rfl,hvy,hyv⟩
        exact ⟨hu,huv.le.trans hvy,hyv.trans (hvmem.2.trans hb)⟩)
      have hspos : 0 < s := div_pos (sub_pos.mpr hRlt) hR
      have hsle : s ≤ 1 / 8 := by
        apply (div_le_iff₀ hR).mpr
        rw [hinit] at hRle
        linarith only [hRle]
      have hfrac : S.r u v = (1-s)*S.r u v₂ := by
        dsimp [s]
        field_simp [hR.ne']
        ring
      have hcg := collar_gap hS hδ hmu hgap hsmall hu
        (huv.trans_le hvmem.1) he hb ⟨hspos,hsle⟩ hfrac hout
      exact hcg.1.trans_lt hcg.2
  have hseg : outSeg u u v ⊆ triangle u₀ b := by
    rintro ⟨x,y⟩ ⟨rfl,huy,hyv⟩
    exact ⟨hu,huy,hyv.trans (hvmem.2.trans hb)⟩
  have hrel := relative_charge hS (huv.trans_le hvmem.1) hseg hδ (hmu (u,v) hp)
    (fun w hw => hgap (u,w) (hseg ⟨rfl,hw⟩))
    (fun w hw => hsmall (u,w) (hseg ⟨rfl,hw⟩))
  have hlow : (1 - (1 / 1024 : ℝ)) * (9 / 7) ≤
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v) := by
    apply (le_div_iff₀ hge).mpr
    linarith only [hrel.1.trans hrel.2, hgsmall]
  exact ⟨hlow, lt_of_lt_of_le (by norm_num) hlow⟩

end EmcsfAcExtension.Global.Gap
