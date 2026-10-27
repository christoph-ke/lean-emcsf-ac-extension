module

public import EmcsfAcExtension.Local.Defs.Limit
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform radial limits at the regular axis

The topological part of `charged_SF_new_version.tex:L6459–6459`. Uniform convergence and
the numerical expansion lower bounds give continuous normalized limit fields.
Compactness upgrades their matching axis values to a uniform radial limit.
There is no asserted power law or quantitative modulus for the AC datum.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace EmcsfAcExtension.Local

private theorem uniform_axis_continuity {E : Type*} [PseudoMetricSpace E]
    {T : ℝ} {f : ℝ × ℝ → E} (hf : ContinuousOn f (triangle 0 T)) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ u v, (u, v) ∈ triangle 0 T → v - u < δ →
      dist (f (u, v)) (f (u, u)) < ε ∧ dist (f (u, v)) (f (v, v)) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_triangle 0 T).uniformContinuousOn_of_continuous hf) ε hε
  refine ⟨δ, hδ, fun u v hp huv => ?_⟩
  have hle : u ≤ v := hp.2.1
  have hd₁ : dist (u, v) (u, u) < δ := by
    simpa only [Prod.dist_eq, dist_self, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hle), max_eq_right (sub_nonneg.mpr hle)] using huv
  have hd₂ : dist (u, v) (v, v) < δ := by
    simpa only [Prod.dist_eq, dist_self, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hle), neg_sub, max_eq_left (sub_nonneg.mpr hle)] using huv
  exact ⟨hbound (u, v) hp (u, u) ⟨hp.1, le_rfl, hle.trans hp.2.2⟩ hd₁,
    hbound (u, v) hp (v, v) ⟨hp.1.trans hle, le_rfl, hp.2.2⟩ hd₂⟩

/-- [node restart-sec-independent-null-construction#uniform-axis-radial-limit]
The normalized scalar fields and the radial scalar meet the common axis value
uniformly as `v-u` tends to zero; both normalized defects vanish uniformly.
The positive expansion lower bound `c` is fixed before the sequence. The conclusion
is qualitative on the fixed triangle and introduces no rate or new constant. -/
theorem Null.uniform_axis_radial_limit_of_strongLimit {e T c : ℝ}
    {Sn : ℕ → Fields} {S : Fields} (hc : 0 < c)
    (hS : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hbox : ∀ n p, p ∈ triangle 0 T → c ≤ (Sn n).lam p.1 p.2 ∧ c ≤ -(Sn n).nu p.1 p.2)
    (hlim : StrongLimit e T Sn S) :
    (∀ t ∈ Icc 0 T, S.a t t = S.phi t t ∧ S.b t t = S.phi t t) ∧
      ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ u v, (u, v) ∈ triangle 0 T → v - u < δ →
        ‖S.a u v - S.phi u u‖ < ε ∧ ‖S.b u v - S.phi v v‖ < ε ∧
          ‖S.phi u v - S.phi u u‖ < ε ∧
            ‖S.theta u v / S.lam u v‖ < ε ∧ ‖S.xi u v / S.nu u v‖ < ε := by
  have hlam p (hp : p ∈ triangle 0 T) : c ≤ S.lam p.1 p.2 :=
    ge_of_tendsto (hlim.unif_lam.tendsto_at hp) (Eventually.of_forall fun n => (hbox n p hp).1)
  have hnu p (hp : p ∈ triangle 0 T) : c ≤ -S.nu p.1 p.2 :=
    ge_of_tendsto (hlim.unif_nu.tendsto_at hp).neg
      (Eventually.of_forall fun n => (hbox n p hp).2)
  have htheta t (ht : t ∈ Icc 0 T) : S.theta t t = 0 := by
    have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
    have hz n : (Sn n).theta t t = 0 := by
      have hh := (hS n).axis t hp |>.2.2.2.2.1
      have hn : ((Sn n).lam t t : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr ((hS n).lam_pos _ hp).ne'
      simpa only [Fields.a, add_eq_left, div_eq_zero_iff, or_iff_left hn] using hh
    exact tendsto_nhds_unique (hlim.unif_theta.tendsto_at hp)
      (by simpa only [Function.uncurry_apply_pair, hz] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  have hxi t (ht : t ∈ Icc 0 T) : S.xi t t = 0 := by
    have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
    have hz n : (Sn n).xi t t = 0 := by
      have hh := (hS n).axis t hp |>.2.2.2.2.2
      have hn : ((Sn n).nu t t : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr ((hS n).nu_neg _ hp).ne
      simpa only [Fields.b, add_eq_left, div_eq_zero_iff, or_iff_left hn] using hh
    exact tendsto_nhds_unique (hlim.unif_xi.tendsto_at hp)
      (by simpa only [Function.uncurry_apply_pair, hz] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  have hphi := hlim.unif_phi.continuousOn
    (Eventually.of_forall fun n => (hS n).c1_phi.continuousOn).frequently
  have hl := hlim.unif_lam.continuousOn
    (Eventually.of_forall fun n => (hS n).c1_lam.continuousOn).frequently
  have hn := hlim.unif_nu.continuousOn
    (Eventually.of_forall fun n => (hS n).c1_nu.continuousOn).frequently
  have ht := hlim.unif_theta.continuousOn
    (Eventually.of_forall fun n => (hS n).c1_theta.continuousOn).frequently
  have hx := hlim.unif_xi.continuousOn
    (Eventually.of_forall fun n => (hS n).c1_xi.continuousOn).frequently
  have hratio : ContinuousOn (fun p : ℝ × ℝ => S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ))
      (triangle 0 T) := ht.div (Complex.continuous_ofReal.comp_continuousOn hl)
    (fun p hp => Complex.ofReal_ne_zero.mpr (hc.trans_le (hlam p hp)).ne')
  have hratio' : ContinuousOn (fun p : ℝ × ℝ => S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ))
      (triangle 0 T) := hx.div (Complex.continuous_ofReal.comp_continuousOn hn)
    (fun p hp => Complex.ofReal_ne_zero.mpr (neg_pos.mp (hc.trans_le (hnu p hp))).ne)
  have ha : ContinuousOn (Function.uncurry S.a) (triangle 0 T) := hphi.add hratio
  have hb : ContinuousOn (Function.uncurry S.b) (triangle 0 T) := hphi.add hratio'
  have haxis t (ht : t ∈ Icc 0 T) : S.a t t = S.phi t t ∧ S.b t t = S.phi t t := by
    simp [Fields.a, Fields.b, htheta t ht, hxi t ht]
  refine ⟨haxis, fun ε hε => ?_⟩
  obtain ⟨da, hda, hba⟩ := uniform_axis_continuity ha ε hε
  obtain ⟨db, hdb, hbb⟩ := uniform_axis_continuity hb ε hε
  obtain ⟨dp, hdp, hbp⟩ := uniform_axis_continuity hphi ε hε
  obtain ⟨dt, hdt, hbt⟩ := uniform_axis_continuity hratio ε hε
  obtain ⟨dx, hdx, hbx⟩ := uniform_axis_continuity hratio' ε hε
  refine ⟨min da (min db (min dp (min dt dx))),
    lt_min hda (lt_min hdb (lt_min hdp (lt_min hdt hdx))), fun u v hp hgap => ?_⟩
  rcases lt_min_iff.mp hgap with ⟨hga, hgap⟩
  rcases lt_min_iff.mp hgap with ⟨hgb, hgap⟩
  rcases lt_min_iff.mp hgap with ⟨hgp, hgap⟩
  rcases lt_min_iff.mp hgap with ⟨hgt, hgx⟩
  have hu : u ∈ Icc 0 T := ⟨hp.1, hp.2.1.trans hp.2.2⟩
  have hv : v ∈ Icc 0 T := ⟨hp.1.trans hp.2.1, hp.2.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.uncurry_apply_pair, (haxis u hu).1, dist_eq_norm] using
      (hba u v hp hga).1
  · simpa only [Function.uncurry_apply_pair, (haxis v hv).2, dist_eq_norm] using
      (hbb u v hp hgb).2
  · simpa only [Function.uncurry_apply_pair, dist_eq_norm] using (hbp u v hp hgp).1
  · simpa only [htheta u hu, zero_div, dist_zero_right] using (hbt u v hp hgt).1
  · simpa only [hxi v hv, zero_div, dist_zero_right] using (hbx u v hp hgx).2

end EmcsfAcExtension.Local
