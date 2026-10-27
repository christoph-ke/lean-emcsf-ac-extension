module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff
import EmcsfAcExtension.Infra.AC.Variation

/-! # Restricting the a priori setting to smaller complete triangles

The global variation and canonical background remain upper controls on
each smaller complete triangle. Canonical partial derivatives agree on
the restriction, so the growing-apex envelopes refer to one fixed field.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

/-- The prescribed datum has finite variation in a classical a priori
setting. The assertion uses its equality with the normalized initial
trace and introduces no uniform derivative bound. -/
theorem AprioriSetting.datum_variation_ne_top {e T ε M : ℝ}
    {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e T ε M S h) :
    eVariationOn h (Icc 0 T) ≠ ⊤ := by
  have ca : ContDiffOn ℝ 1 (S.a 0) (Icc 0 T) :=
    hset.c1.c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have ch : ContDiffOn ℝ 1 h (Icc 0 T) :=
    ca.congr (fun v hv => (hset.data.1 v hv).2.symm)
  have hac : AbsolutelyContinuousOnInterval h 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hset.pos.le] using ch
  exact hac.boundedVariationOn_Icc hset.pos.le

/-- Restricting to a positive complete subtriangle preserves the same
variation and background upper controls. No constant depending on the
smaller apex or on higher data norms is introduced. -/
theorem AprioriSetting.restrict_apex {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    AprioriSetting e s ε M S h := by
  have hsub := triangle_subset_triangle hsT
  refine ⟨hs, hset.c1.mono hsub (uniqueDiffOn_triangle hs),
    isRestartData_mono hset.data hsT, ?_, hset.M_eq, hset.box.mono hsub⟩
  exact (ENNReal.toReal_mono hset.datum_variation_ne_top
    (eVariationOn.mono h (Icc_subset_Icc le_rfl hsT))).trans hset.eps

/-- The outgoing renormalized density on a positive subtriangle is the
restriction of the original canonical density. This is an exact identity,
independent of all size and derivative parameters. -/
theorem jC1_restrict_apex {e T s : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hs : 0 < s) (hsT : s ≤ T)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    jC1 (triangle 0 s) S u v = jC1 (triangle 0 T) S u v := by
  unfold jC1
  rw [pdV_mono hS.c1_a (triangle_subset_triangle hsT) (uniqueDiffOn_triangle hs) hp]

/-- The incoming renormalized density on a positive subtriangle is the
restriction of the original canonical density. The connection is unchanged;
no gauge or size assumption is required. -/
theorem kC1_restrict_apex {e T s : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hs : 0 < s) (hsT : s ≤ T)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    kC1 e (triangle 0 s) S u v = kC1 e (triangle 0 T) S u v := by
  unfold kC1
  rw [pdU_mono hS.c1_b (triangle_subset_triangle hsT) (uniqueDiffOn_triangle hs) hp]

/-- Both envelope integrals computed with canonical derivatives on a
positive subtriangle equal those of the fixed ambient densities. The
identities retain the smaller apex as the incoming envelope endpoint. -/
theorem envelope_integrals_restrict_apex {e T s : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hs : 0 < s) (hsT : s ≤ T) :
    (∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v) =
        (∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 T) S) v) ∧
      (∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u) =
        (∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 T) S) u) := by
  constructor
  · apply setLIntegral_congr_fun measurableSet_Icc
    intro v hv
    apply iSup_congr
    intro u
    apply iSup_congr
    intro hu
    rw [jC1_restrict_apex hS hs hsT ⟨hu.1, hu.2, hv.2⟩]
  · apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    apply iSup_congr
    intro v
    apply iSup_congr
    intro hv
    rw [kC1_restrict_apex hS hs hsT ⟨hu.1, hv.1, hv.2⟩]

end EmcsfAcExtension.Local
