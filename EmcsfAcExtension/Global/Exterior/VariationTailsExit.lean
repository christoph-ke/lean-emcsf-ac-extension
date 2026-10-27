module

public import EmcsfAcExtension.Global.Exterior.VariationTailsHistory

/-! # The moving-interval modulus formula with its exit cost

This is the labelwise proof of M3 in approved internal project record,
`charged_SF_new_version.tex:L1364–L1380`, L1413–L1416. Every incoming history is
stopped at the actual measurable exit time. Both terms on the left
are retained, before any estimate of the coefficient or source.
-/

public section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The exact incoming modulus estimate on a moving outgoing interval.
The exit-map assumptions are purely geometric and include surviving
labels. Integrability of the history, exit and boundary density is proved
from the original solution's prescribed representative. The coefficient
of every term is one, uniformly in all data and proper segments. -/
theorem moving_interval_modulus_of_exit_map
    {ui e a b : ℝ} {S : Fields} {t τ : ℝ → ℝ} {K L : ℝ≥0}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (ht : LipschitzOnWith K t (uIcc a b)) (hm : MonotoneOn t (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict t))
    (hmem : ∀ u ∈ Icc a b, (u, t u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < t u)
    (hτ : Measurable τ)
    (hτmem : ∀ v ∈ Icc (t a) 0, (τ v, v) ∈ variationSweptDomain a b t)
    (hτinv : ∀ u ∈ uIcc a b, τ (t u) = u)
    (hexit : ∀ u ∈ Icc a b, ∀ v ∈ Icc (t a) 0, u ≤ τ v ↔ t u ≤ v) :
    (eVariationOn (S.a b) (Icc (t b) 0)).toReal +
        (∫ u in a..b, deriv t u * ‖densityRepresentative e S a u (t u)‖) ≤
      (eVariationOn (S.a a) (Icc (t a) 0)).toReal +
        ∫ u in a..b, ∫ v in t u..0, densityModulusHistory e S a (u, v) := by
  have htc : ContinuousOn t (Icc a b) := by
    simpa only [uIcc_of_le hab] using ht.continuousOn
  have hmc : MonotoneOn t (Icc a b) := by
    simpa only [uIcc_of_le hab] using hm
  have haa : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hta : t a ≤ 0 := (hmem a haa).2.2.2
  have htb : t b ≤ 0 := (hmem b hbb).2.2.2
  have htab : t a ≤ t b := hmc haa hbb hab
  have hK := (isClosed_variationSweptDomain hab htc).measurableSet
  have hH := integrableOn_densityModulusHistory hS hab htc hmc hmem hproper
  have hhist := integrable_stopped_histories hK
    (fun v hv => (hτmem v hv).1.2) (fun u hu => hmc haa hu hu.1) hexit hH
  have hswap := integral_integral_swap_stopped_histories hτ hK
    (fun v hv => (hτmem v hv).1.2) (fun u hu => hmc haa hu hu.1) hexit hH
  have hI := intervalIntegrable_swept_density_exit hS hab hta htc hmc hmem hproper hτ hτmem
  have hinit := swept_initial_density_intervalIntegrable hS hab hmem
  have hIset := (intervalIntegrable_iff_integrableOn_Icc_of_le hta).1 hI.norm
  have hinitset := (intervalIntegrable_iff_integrableOn_Icc_of_le hta).1 hinit.norm
  have hineq : ∀ v ∈ Icc (t a) 0,
      ‖densityRepresentative e S a (τ v) v‖ ≤ ‖deriv (S.a a) v‖ +
        ∫ u in Icc a (τ v), densityModulusHistory e S a (u, v) := by
    intro v hv
    have hp := hτmem v hv
    have hn := density_norm_le_initial_add_history hS (hmem a haa).1 hp.1.1
      ((hproper _ hp.1).trans_le hp.2.1) hp.2.2
    rwa [intervalIntegral.integral_of_le hp.1.1, ← integral_Icc_eq_integral_Ioc] at hn
  have hi := integral_mono_ae hIset (hinitset.add hhist)
    ((ae_restrict_mem measurableSet_Icc).mono fun v hv => hineq v hv)
  dsimp only [Pi.add_apply] at hi hhist
  rw [integral_add hinitset hhist, hswap] at hi
  have hconvert (f : ℝ → ℝ) {c : ℝ} (hc : c ≤ 0) :
      (∫ v in Icc c 0, f v) = ∫ v in c..0, f v := by
    rw [intervalIntegral.integral_of_le hc, integral_Icc_eq_integral_Ioc]
  rw [hconvert _ hta, hconvert _ hta] at hi
  have hrowconvert : (∫ u in Icc a b, ∫ v in Icc (t u) 0,
      densityModulusHistory e S a (u, v)) =
      ∫ u in a..b, ∫ v in t u..0, densityModulusHistory e S a (u, v) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact hconvert _ (hmem u hu).2.2.2
  rw [hrowconvert] at hi
  have hinitial : (eVariationOn (S.a a) (Icc (t a) 0)).toReal =
      ∫ v in t a..0, ‖deriv (S.a a) v‖ := by
    rw [swept_row_variation_eq_density_integral hS hab hmem hproper haa]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hta] at hv
    have hp : (a, v) ∈ origDomain ui :=
      ⟨(hmem a haa).1, (hmem a haa).2.1,
        (hproper a haa).le.trans hv.1, hv.2⟩
    exact congrArg norm (densityRepresentative_initial_of_mem (e := e) hS hp)
  have htbmem : t b ∈ uIcc (t a) 0 := by
    rw [uIcc_of_le hta]
    exact ⟨htab, htb⟩
  have hI₁ := hI.norm.mono_set (uIcc_subset_uIcc left_mem_uIcc htbmem)
  have hI₂ := hI.norm.mono_set (uIcc_subset_uIcc htbmem right_mem_uIcc)
  have hboundary := swept_density_boundary_norm_eq_exit hS hab ht hm ha
    (by simpa only [uIcc_of_le hab] using hmem)
    (by simpa only [uIcc_of_le hab] using hproper) hτ
    (fun v hv => hτmem v ⟨hv.1, hv.2.trans htb⟩) hτinv
  have hsurv : (∫ v in t b..0, ‖densityRepresentative e S a (τ v) v‖) =
      ∫ v in t b..0, ‖densityRepresentative e S a b v‖ := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le htb] at hv
    have hva : v ∈ Icc (t a) 0 := ⟨htab.trans hv.1, hv.2⟩
    have hτb : τ v = b := le_antisymm (hτmem v hva).1.2
      ((hexit b hbb v hva).2 hv.1)
    dsimp only
    rw [hτb]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂
  rw [← hsplit, hsurv, ← hboundary.2,
    ← swept_row_variation_eq_density_integral hS hab hmem hproper hbb,
    ← hinitial] at hi
  linarith only [hi]

end EmcsfAcExtension.Global.Exterior
