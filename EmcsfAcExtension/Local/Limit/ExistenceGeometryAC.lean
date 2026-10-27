module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.Fields.Omega2
import EmcsfAcExtension.Local.Limit.ExistenceAC
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Infra.AC.Quotient

/-! # All geometric characteristic AC clauses

Pure expansion AC is supplied by the classical derivative comparison. The
cross expansions and mass ratio have continuous interior equation densities;
their passed finite variation and axis continuity recover endpoint AC.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem omega_ac {lam nu mu : ℝ → ℝ} {a b : ℝ}
    (hl : AbsolutelyContinuousOnInterval lam a b)
    (hn : AbsolutelyContinuousOnInterval nu a b)
    (hm : AbsolutelyContinuousOnInterval mu a b)
    (hg : ∀ x ∈ uIcc a b, 1 / 4 ≤ 1 - mu x) :
    AbsolutelyContinuousOnInterval (fun x => -4 * nu x * lam x / (1 - mu x)) a b := by
  have hconst (z : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => z) a b :=
    (LipschitzWith.const z).lipschitzOnWith.absolutelyContinuousOnInterval
  exact (((hconst (-4)).mul_normed_ring hn).mul_normed_ring hl).div_of_le_norm
    ((hconst 1).sub hm) (by norm_num : (0 : ℝ) < 1 / 4)
    (fun x hx => (hg x hx).trans (le_abs_self _))

/-- Derive both four-field geometric AC records in the frozen existence
bounds. The positive denominator margin is the explicit fixed quarter from
the constructed comparison box. The finite variation bound `B` may depend
on the fixed datum and triangle; no new uniform estimate is claimed here. -/
theorem IsSolution.geometry_ac_of_bounds {e T : ℝ} {S : Fields} {B : ℝ≥0∞}
    (hS : IsSolution e S (triangle 0 T))
    (hmu : ContinuousOn (Function.uncurry S.mu) (triangle 0 T))
    (hg : ∀ p ∈ triangle 0 T, 1 / 4 ≤ 1 - S.mu p.1 p.2)
    (hla : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.lam u) u T)
    (hna : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.nu u v) 0 v)
    (hB : B ≠ ⊤)
    (hvo : ∀ u ∈ Icc 0 T, eVariationOn (S.nu u) (Icc u T) ≤ B ∧
      eVariationOn (S.mu u) (Icc u T) ≤ B)
    (hvi : ∀ v ∈ Icc 0 T, eVariationOn (fun u => S.lam u v) (Icc 0 v) ≤ B ∧
      eVariationOn (fun u => S.mu u v) (Icc 0 v) ≤ B) :
    (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.lam u) u T ∧
      AbsolutelyContinuousOnInterval (S.nu u) u T ∧ AbsolutelyContinuousOnInterval (S.mu u) u T ∧
      AbsolutelyContinuousOnInterval (S.Omega2 u) u T) ∧
    (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.lam u v) 0 v ∧
      AbsolutelyContinuousOnInterval (fun u => S.nu u v) 0 v ∧
      AbsolutelyContinuousOnInterval (fun u => S.mu u v) 0 v ∧
      AbsolutelyContinuousOnInterval (fun u => S.Omega2 u v) 0 v) := by
  let D := triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}
  have nr p (hp : p ∈ D) := (hS.r_pos p hp.1 hp.2).ne'
  have ng p (hp : p ∈ D) := (hS.one_sub_mu_pos p hp.1).ne'
  have csource : ContinuousOn (Function.uncurry S.rUV) D := by
    simpa only [Fields.rUV, Function.uncurry_def] using!
      (((hS.cont_nu.mono inter_subset_left).mul (hS.cont_lam.mono inter_subset_left)).div
        (hS.cont_r.mono inter_subset_left) nr).mul
        (((hmu.mono inter_subset_left).sub
          (((hS.cont_Q.mono inter_subset_left).pow 2).div ((hS.cont_r.mono inter_subset_left).pow 2)
            (fun p hp => pow_ne_zero 2 (nr p hp)))).div
          (continuousOn_const.sub (hmu.mono inter_subset_left)) ng)
  constructor
  · intro u hu
    have hm : MapsTo (fun x => (u, x)) (Icc u T) (triangle 0 T) := fun x hx => ⟨hu.1, hx.1, hx.2⟩
    have hseg : outSeg u u T ⊆ triangle 0 T := by
      rintro ⟨x, y⟩ ⟨rfl, huy, hyT⟩
      exact ⟨hu.1, huy, hyT⟩
    have hnu : AbsolutelyContinuousOnInterval (S.nu u) u T := by
      apply ac_of_continuous_bv_of_differentiableOn hu.2
        (hS.cont_nu.comp (continuous_const.prodMk continuous_id).continuousOn hm)
        (ne_top_of_le_ne_top hB (hvo u hu).1)
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      apply HasDerivAt.differentiableAt (f' := S.rUV u x)
      apply hasDerivAt_of_integralForm_interior hx
        (csource.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun y hy => ⟨⟨hu.1, hy.1.le, hy.2.le⟩, hy.1⟩))
      intro a b hua hab hbT
      exact (hS.eq_out u a b hua hab (by
        rintro ⟨x, y⟩ ⟨rfl, hay, hyb⟩
        exact ⟨hu.1, hua.le.trans hay, hyb.trans hbT.le⟩)).2.1
    have hmuac : AbsolutelyContinuousOnInterval (S.mu u) u T := by
      apply ac_of_continuous_bv_of_differentiableOn hu.2
        (hmu.comp (continuous_const.prodMk continuous_id).continuousOn hm)
        (ne_top_of_le_ne_top hB (hvo u hu).2)
      intro x hx
      have hdm := IsSolution.hasDerivAt_mass_out hS hseg hx
      have hdr := IsSolution.hasDerivAt_radius_out hS hseg hx
      exact ((hdm.const_mul 2).div hdr (hS.r_pos (u, x) (hm ⟨hx.1.le, hx.2.le⟩)
          hx.1).ne').differentiableAt.differentiableWithinAt
    refine ⟨hla u hu, hnu, hmuac, ?_⟩
    exact omega_ac (hla u hu) hnu hmuac (fun x hx =>
      hg (u, x) (hm (by simpa only [uIcc_of_le hu.2] using hx)))
  · intro v hv
    have hm : MapsTo (fun x => (x, v)) (Icc 0 v) (triangle 0 T) := fun x hx => ⟨hx.1, hx.2, hv.2⟩
    have hseg : inSeg 0 v v ⊆ triangle 0 T := by
      rintro ⟨x, y⟩ ⟨h0x, hxv, rfl⟩
      exact ⟨h0x, hxv, hv.2⟩
    have hlam : AbsolutelyContinuousOnInterval (fun u => S.lam u v) 0 v := by
      apply ac_of_continuous_bv_of_differentiableOn hv.1
        (hS.cont_lam.comp (continuous_id.prodMk continuous_const).continuousOn hm)
        (ne_top_of_le_ne_top hB (hvi v hv).1)
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      apply HasDerivAt.differentiableAt (f' := S.rUV x v)
      apply hasDerivAt_of_integralForm_interior hx
        (csource.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun y hy => ⟨⟨hy.1.le, hy.2.le, hv.2⟩, hy.2⟩))
      intro a b h0a hab hbv
      exact (hS.eq_in a b v hab hbv (by
        rintro ⟨x, y⟩ ⟨hax, hxb, rfl⟩
        exact ⟨h0a.le.trans hax, hxb.trans hbv.le, hv.2⟩)).2.1
    have hmuac : AbsolutelyContinuousOnInterval (fun u => S.mu u v) 0 v := by
      apply ac_of_continuous_bv_of_differentiableOn hv.1
        (hmu.comp (continuous_id.prodMk continuous_const).continuousOn hm)
        (ne_top_of_le_ne_top hB (hvi v hv).2)
      intro x hx
      have hdm := IsSolution.hasDerivAt_mass_in hS hseg hx
      have hdr : HasDerivAt (fun u => S.r u v) (S.nu x v) x := by
        apply hasDerivAt_of_integralForm_interior hx
          ((hS.cont_nu.comp (continuous_id.prodMk continuous_const).continuousOn hm).mono
              Ioo_subset_Icc_self)
        intro a b h0a hab hbv
        exact (hS.eq_in a b v hab hbv (by
          rintro ⟨x, y⟩ ⟨hax, hxb, rfl⟩
          exact ⟨h0a.le.trans hax, hxb.trans hbv.le, hv.2⟩)).1
      exact ((hdm.const_mul 2).div hdr (hS.r_pos (x, v) (hm ⟨hx.1.le, hx.2.le⟩)
          hx.2).ne').differentiableAt.differentiableWithinAt
    refine ⟨hlam, hna v hv, hmuac, ?_⟩
    exact omega_ac hlam (hna v hv) hmuac (fun x hx =>
      hg (x, v) (hm (by simpa only [uIcc_of_le hv.1] using hx)))

end EmcsfAcExtension.Local
