module

public import EmcsfAcExtension.Local.Defs.Limit
import EmcsfAcExtension.Local.Limit.ExistenceEquations
import EmcsfAcExtension.Local.Limit.ExistenceAC

/-! # Endpoint AC of the primary scalar limit

The shrinking variation condition supplies finite variation in a neighborhood
of each axis endpoint. Integral equations give the classical scalar derivative
everywhere else on a section; endpoint AC recovery then closes both families.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Recover the scalar's AC on both full characteristic families from its
actual shrinking-axis variation and the constructed off-axis equations.
No derivative bound at the axis and no new numerical constant is required. -/
theorem StrongLimit.scalar_ac_of_axis_variation {e T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hT : 0 < T) (hc1 : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hlim : StrongLimit e T Sn S)
    (hr : ∀ p ∈ triangle 0 T, p.1 < p.2 → 0 < S.r p.1 p.2)
    (hl : ∀ p ∈ triangle 0 T, 0 < S.lam p.1 p.2)
    (hn : ∀ p ∈ triangle 0 T, S.nu p.1 p.2 < 0)
    (hg : ∀ p ∈ triangle 0 T, 0 < 1 - S.mu p.1 p.2)
    (haxis : ∀ t, (t, t) ∈ triangle 0 T → ∃ δ : ℝ, 0 < δ ∧
      (∀ u a b, outSeg u a b ⊆ triangle 0 T ∩ triangle (t - δ) (t + δ) →
        eVariationOn (S.phi u) (Icc a b) ≤ 1) ∧
      (∀ a b v, inSeg a b v ⊆ triangle 0 T ∩ triangle (t - δ) (t + δ) →
        eVariationOn (fun u => S.phi u v) (Icc a b) ≤ 1)) :
    (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.phi u) u T) ∧
    (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.phi u v) 0 v) := by
  obtain ⟨hout, hin⟩ := hlim.integral_equations_of_c1 hT hc1 hr hl hn hg
  have cp := hlim.unif_phi.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_phi.continuousOn).frequently
  have cr := hlim.unif_r.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_r.continuousOn).frequently
  have ct := hlim.unif_theta.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_theta.continuousOn).frequently
  have cx := hlim.unif_xi.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_xi.continuousOn).frequently
  have cA := hlim.unif_A.continuousOn (Eventually.of_forall fun n => (hc1
      n).c1_A.continuousOn).frequently
  constructor
  · intro u hu
    rcases hu.2.eq_or_lt with heq | hlt
    · subst T
      exact AbsolutelyContinuousOnInterval.rfl
    have hmaps : MapsTo (fun x : ℝ => (u, x)) (Icc u T) (triangle 0 T) :=
      fun x hx => ⟨hu.1, hx.1, hx.2⟩
    apply ac_of_left_bv_of_interior_equations hlt
      (cp.comp (continuous_const.prodMk continuous_id).continuousOn hmaps)
    · have hmaps' : MapsTo (fun x : ℝ => (u, x)) (Ioc u T) (triangle 0 T) :=
        fun x hx => ⟨hu.1, hx.1.le, hx.2⟩
      exact (ct.comp (continuous_const.prodMk continuous_id).continuousOn hmaps').div
        (Complex.continuous_ofReal.comp_continuousOn
          (cr.comp (continuous_const.prodMk continuous_id).continuousOn hmaps'))
        (fun x hx => Complex.ofReal_ne_zero.mpr (hr (u, x) (hmaps' hx) hx.1).ne')
    · intro a b hua hab hbT
      exact (hout u a b hua hab (fun p hp => by
        rcases p with ⟨x, y⟩
        rcases hp with ⟨rfl, hya, hyb⟩
        exact ⟨hu.1, hua.le.trans hya, hyb.trans hbT⟩)).2.2.2.2.2.1
    · obtain ⟨δ, hδ, hv, _⟩ := haxis u ⟨hu.1, le_rfl, hu.2⟩
      let c := min T (u + δ / 2)
      have huc : u < c := lt_min hlt (by linarith only [hδ])
      have hcT : c ≤ T := min_le_left _ _
      have hcc : c ≤ u + δ := (min_le_right _ _).trans (by linarith only [hδ])
      refine ⟨c, ⟨huc, hcT⟩, ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) ?_⟩
      apply hv u u c
      rintro ⟨x, y⟩ ⟨rfl, hxy, hyc⟩
      exact ⟨⟨hu.1, hxy, hyc.trans hcT⟩,
        ⟨by linarith only [hδ], hxy, hyc.trans hcc⟩⟩
  · intro v hv
    rcases hv.1.eq_or_lt with heq | hlt
    · subst v
      exact AbsolutelyContinuousOnInterval.rfl
    have hmaps : MapsTo (fun x : ℝ => (x, v)) (Icc 0 v) (triangle 0 T) :=
      fun x hx => ⟨hx.1, hx.2, hv.2⟩
    apply ac_of_right_bv_of_interior_equations hlt
      (cp.comp (continuous_id.prodMk continuous_const).continuousOn hmaps)
    · have hmaps' : MapsTo (fun x : ℝ => (x, v)) (Ico 0 v) (triangle 0 T) :=
        fun x hx => ⟨hx.1, hx.2.le, hv.2⟩
      have cc := (continuous_id.prodMk (continuous_const (y := v))).continuousOn (s := Ico 0 v)
      have cphi := cp.comp cc hmaps'
      have cpot := Complex.continuous_ofReal.comp_continuousOn (cA.comp cc hmaps')
      have cdiv := (cx.comp cc hmaps').div
        (Complex.continuous_ofReal.comp_continuousOn (cr.comp cc hmaps'))
        (fun x hx => Complex.ofReal_ne_zero.mpr (hr (x, v) (hmaps' hx) hx.2).ne')
      exact cdiv.sub (((continuousOn_const (c := I * (e : ℂ))).mul cpot).mul cphi)
    · intro a b h0a hab hbv
      exact (hin a b v hab hbv (fun p hp => by
        rcases p with ⟨x, y⟩
        rcases hp with ⟨hxa, hxb, rfl⟩
        exact ⟨h0a.trans hxa, hxb.trans hbv.le, hv.2⟩)).2.2.2.2.1
    · obtain ⟨δ, hδ, _, hi⟩ := haxis v ⟨hv.1, le_rfl, hv.2⟩
      let c := max 0 (v - δ / 2)
      have h0c : 0 ≤ c := le_max_left _ _
      have hcv : c < v := max_lt hlt (by linarith only [hδ])
      have hcc : v - δ ≤ c := (by linarith only [hδ] : v - δ ≤ v - δ / 2).trans (le_max_right _ _)
      refine ⟨c, ⟨h0c, hcv⟩, ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) ?_⟩
      apply hi c v v
      rintro ⟨x, y⟩ ⟨hcx, hxv, rfl⟩
      exact ⟨⟨h0c.trans hcx, hxv, hv.2⟩,
        ⟨hcc.trans hcx, hxv, by linarith only [hδ]⟩⟩

end EmcsfAcExtension.Local
