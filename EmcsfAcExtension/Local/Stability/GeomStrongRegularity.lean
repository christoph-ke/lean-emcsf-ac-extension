module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.FluxDifferenceRegularity
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Regularity of geometric renormalizations and their transport source

The quadratic corrections extend continuously through the axis. The
totalized common source is measurable on every section, before its
integrability is obtained from the ordered area estimates.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- The outgoing geometric renormalization is continuous on the full
classical triangle. There is no bound on higher derivatives or constant.
-/
theorem stab_geomL_continuous_c1 {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    ContinuousOn (Function.uncurry (geomL (triangle 0 T) S)) (triangle 0 T) := by
  have cp := continuousOn_partial_v hset.c1.c1_lam (uniqueDiffOn_triangle hset.pos)
  simpa only [geomL, Function.uncurry_def] using!
    (cp.div hset.c1.c1_lam.continuousOn (fun p hp => (hset.c1.lam_pos p hp).ne')).add
      (stab_out_quadratic_flux_continuous hset)

/-- The incoming geometric renormalization is continuous through the
regular diagonal, without a derivative-supremum bound or constant.
-/
theorem stab_geomN_continuous_c1 {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    ContinuousOn (Function.uncurry (geomN (triangle 0 T) S)) (triangle 0 T) := by
  have cp := continuousOn_partial_u hset.c1.c1_nu (uniqueDiffOn_triangle hset.pos)
  have hc := (cp.div hset.c1.c1_nu.continuousOn
    (fun p hp => (hset.c1.nu_neg p hp).ne)).sub (stab_in_quadratic_flux_continuous hset)
  apply hc.congr
  intro p hp
  dsimp only [Function.uncurry_def, geomN, Pi.sub_apply, Pi.div_apply, pdU]
  rw [neg_div]
  ring

/-- The totalized geometric source is a.e. measurable on any continuous
section in the classical triangle. No finite-integral hypothesis or
estimate constant is introduced.
-/
theorem stab_geomSource_aemeasurable_on_c1
    {e T ε M A a b : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {p : ℝ → ℝ × ℝ}
    (cp : ContinuousOn p (Icc a b)) (hp : MapsTo p (Icc a b) (triangle 0 T)) :
    AEMeasurable (fun t => geomSource S (p t).1 (p t).2) (volume.restrict (Icc a b)) := by
  have ar : AEMeasurable (fun t => S.r (p t).1 (p t).2) (volume.restrict (Icc a b)) :=
    (hset.c1.c1_r.continuousOn.comp cp hp).aemeasurable measurableSet_Icc
  have al : AEMeasurable (fun t => S.lam (p t).1 (p t).2) (volume.restrict (Icc a b)) :=
    (hset.c1.c1_lam.continuousOn.comp cp hp).aemeasurable measurableSet_Icc
  have an : AEMeasurable (fun t => S.nu (p t).1 (p t).2) (volume.restrict (Icc a b)) :=
    (hset.c1.c1_nu.continuousOn.comp cp hp).aemeasurable measurableSet_Icc
  have am : AEMeasurable (fun t => S.m (p t).1 (p t).2) (volume.restrict (Icc a b)) :=
    (hset.c1.c1_m.continuousOn.comp cp hp).aemeasurable measurableSet_Icc
  have aq : AEMeasurable (fun t => S.Q (p t).1 (p t).2) (volume.restrict (Icc a b)) :=
    (hset.c1.c1_Q.continuousOn.comp cp hp).aemeasurable measurableSet_Icc
  have ax : AEMeasurable (fun t => S.theta (p t).1 (p t).2) (volume.restrict (Icc a b)) :=
    (hset.c1.c1_theta.continuousOn.comp cp hp).aemeasurable measurableSet_Icc
  have ay : AEMeasurable (fun t => S.xi (p t).1 (p t).2) (volume.restrict (Icc a b)) :=
    (hset.c1.c1_xi.continuousOn.comp cp hp).aemeasurable measurableSet_Icc
  dsimp only [geomSource, curv, Fields.mu]
  fun_prop

end EmcsfAcExtension.Local
