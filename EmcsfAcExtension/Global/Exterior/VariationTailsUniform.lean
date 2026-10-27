module

public import EmcsfAcExtension.Global.Exterior.VariationTailsBounds
import EmcsfAcExtension.Infra.AC.Variation

/-! # Uniform variation and moving-boundary exit bounds

The complete time integrals determine the variation constant before any
later row or boundary segment is selected. The exit bound applies to every
proper increasing boundary inside the adaptive exterior, and therefore to
every admissible radius cylinder. Source: `charged_SF_new_version.tex:L1337–L1380`,
L1413–L1416; approved internal project record (M4)–(M5).
-/

public section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The actual outgoing variation obeys the uniform Grönwall bound from its
genuine density-history majorant. The right side depends only on the
entry variation and the complete integrals of `k,q`, uniformly in every
later row. Proper continuity is derived from the prescribed L¹ density. -/
theorem outgoing_variation_bound_of_history
    {ui e c : ℝ} {S : Fields} {t k q : ℝ → ℝ}
    (h : OriginalData ui e S) (hc : c ∈ Ioo ui 0)
    (hroot : ∀ u ∈ Ico c 0, u < t u ∧ t u < 0)
    (hm : MonotoneOn t (Ico c 0))
    (hsegments : ∀ a b, c ≤ a → a ≤ b → b < 0 →
      ∃ K L : ℝ≥0, LipschitzOnWith K t (uIcc a b) ∧
        AntilipschitzWith L ((uIcc a b).domRestrict t))
    (hk : IntervalIntegrable k volume c 0) (hq : IntervalIntegrable q volume c 0)
    (hk₀ : ∀ u ∈ Ico c 0, 0 ≤ k u) (hq₀ : ∀ u ∈ Ico c 0, 0 ≤ q u)
    (hrow : ∀ a u, ui ≤ a → a ≤ u → u ∈ Ico c 0 →
      (∫ v in t u..0, densityModulusHistory e S a (u, v)) ≤
        k u * (eVariationOn (S.a u) (Icc (t u) 0)).toReal + q u) :
    ∀ u ∈ Ico c 0, (eVariationOn (S.a u) (Icc (t u) 0)).toReal ≤
      ((eVariationOn (S.a c) (Icc (t c) 0)).toReal + ∫ s in c..0, q s) *
        Real.exp (∫ s in c..0, k s) := by
  have hmem (b : ℝ) (hb : b ∈ Ico c 0) (u : ℝ) (hu : u ∈ Icc c b) :
      (u, t u) ∈ origDomain ui :=
    ⟨hc.1.le.trans hu.1, hu.2.trans_lt hb.2,
      (hroot u ⟨hu.1, hu.2.trans_lt hb.2⟩).1.le,
      (hroot u ⟨hu.1, hu.2.trans_lt hb.2⟩).2.le⟩
  have hproper (b : ℝ) (hb : b ∈ Ico c 0) (u : ℝ) (hu : u ∈ Icc c b) :
      u < t u := (hroot u ⟨hu.1, hu.2.trans_lt hb.2⟩).1
  have hmono (b : ℝ) (hb : b ∈ Ico c 0) : MonotoneOn t (Icc c b) :=
    hm.mono (fun u hu => ⟨hu.1, hu.2.trans_lt hb.2⟩)
  have hcont (b : ℝ) (hb : b ∈ Ico c 0) :
      ContinuousOn (fun u => (eVariationOn (S.a u) (Icc (t u) 0)).toReal) (Icc c b) := by
    obtain ⟨K, L, ht, ha⟩ := hsegments c b le_rfl hb.1 hb.2
    apply continuousOn_outgoing_variation h.solution hb.1
      (by simpa only [uIcc_of_le hb.1] using ht.continuousOn)
      (hmono b hb) (hmem b hb) (hproper b hb)
  apply uniform_bound_of_moving_modulus hc.2 ENNReal.toReal_nonneg hcont hk hq hk₀ hq₀
  intro u hu
  obtain ⟨K, L, ht, ha⟩ := hsegments c u le_rfl hu.1 hu.2
  have hsub : uIcc c u ⊆ uIcc c 0 := by
    rw [uIcc_of_le hu.1, uIcc_of_le hc.2.le]
    exact Icc_subset_Icc le_rfl hu.2.le
  have hm' : MonotoneOn t (uIcc c u) := by
    simpa only [uIcc_of_le hu.1] using hmono u hu
  have he := moving_interval_modulus_inequality_of_history_bound h.solution hu.1
    ht hm' ha (hmem u hu) (hproper u hu) (hk.mono_set hsub) (hq.mono_set hsub)
    (fun s hs => hrow c s hc.1.le hs.1 ⟨hs.1, hs.2.trans_lt hu.2⟩)
  have hn := boundary_density_exit_nonneg (e := e) (S := S) hu.1 (hmono u hu)
  linarith only [he, hn]

/-- [internal]
The M5 bound for any proper bi-Lipschitz increasing boundary remaining
above the adaptive frontier. Its right side is fixed independently of the
boundary, its cylinder radius, and its final time. The actual outgoing
variation bound is the only previously established estimate consumed. -/
theorem boundary_exit_bound_of_history
    {ui e c a b KV : ℝ} {S : Fields} {t k q γ : ℝ → ℝ} {K L : ℝ≥0}
    (h : OriginalData ui e S) (hc : c ∈ Ioo ui 0)
    (hroot : ∀ u ∈ Ico c 0, u < t u ∧ t u ≤ 0)
    (ha : c ≤ a) (hab : a ≤ b) (hb : b < 0)
    (hγ : LipschitzOnWith K γ (uIcc a b)) (hγm : MonotoneOn γ (uIcc a b))
    (hγa : AntilipschitzWith L ((uIcc a b).domRestrict γ))
    (hinside : ∀ u ∈ Icc a b, t u ≤ γ u ∧ γ u ≤ 0)
    (hk : IntervalIntegrable k volume c 0) (hq : IntervalIntegrable q volume c 0)
    (hk₀ : ∀ u ∈ Ico c 0, 0 ≤ k u) (hq₀ : ∀ u ∈ Ico c 0, 0 ≤ q u)
    (hKV : 0 ≤ KV)
    (hvar : ∀ u ∈ Ico c 0, (eVariationOn (S.a u) (Icc (t u) 0)).toReal ≤ KV)
    (hrow : ∀ a u, ui ≤ a → a ≤ u → u ∈ Ico c 0 →
      (∫ v in t u..0, densityModulusHistory e S a (u, v)) ≤
        k u * (eVariationOn (S.a u) (Icc (t u) 0)).toReal + q u) :
    (∫ u in a..b, deriv γ u * ‖densityRepresentative e S a u (γ u)‖) ≤
      (eVariationOn (S.a a) (Icc (t a) 0)).toReal +
        ∫ u in a..0, (k u * KV + q u) := by
  have hlate (u : ℝ) (hu : u ∈ Icc a b) : u ∈ Ico c 0 :=
    ⟨ha.trans hu.1, hu.2.trans_lt hb⟩
  have hmem (u : ℝ) (hu : u ∈ Icc a b) : (u, γ u) ∈ origDomain ui :=
    ⟨hc.1.le.trans (hlate u hu).1, (hlate u hu).2,
      ((hroot u (hlate u hu)).1.le.trans (hinside u hu).1), (hinside u hu).2⟩
  have hproper (u : ℝ) (hu : u ∈ Icc a b) : u < γ u :=
    (hroot u (hlate u hu)).1.trans_le (hinside u hu).1
  have hraw := moving_interval_modulus h.solution hab hγ hγm hγa hmem hproper
  have hVa : (eVariationOn (S.a a) (Icc (γ a) 0)).toReal ≤
      (eVariationOn (S.a a) (Icc (t a) 0)).toReal := by
    have haa : a ∈ Icc a b := ⟨le_rfl, hab⟩
    have hs : outSeg a (t a) 0 ⊆ origDomain ui :=
      (outSeg_subset_origDomain_iff (hroot a (hlate a haa)).2).2
        ⟨hc.1.le.trans ha, hab.trans_lt hb, (hroot a (hlate a haa)).1.le, le_rfl⟩
    have hac := (h.solution.ac_out a (t a) 0 (hroot a (hlate a haa)).2 hs).2.2.2.2
    exact ENNReal.toReal_mono (hac.boundedVariationOn_Icc (hroot a (hlate a haa)).2)
      (eVariationOn.mono (S.a a) (Icc_subset_Icc (hinside a haa).1 le_rfl))
  have hsuba : uIcc a 0 ⊆ uIcc c 0 := by
    rw [uIcc_of_le (hab.trans_lt hb).le, uIcc_of_le hc.2.le]
    exact Icc_subset_Icc ha le_rfl
  have hi := ((hk.mul_const KV).add hq).mono_set hsuba
  have hhist : (∫ u in a..b, ∫ v in γ u..0, densityModulusHistory e S a (u, v)) ≤
      ∫ u in a..b, (k u * KV + q u) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    apply integral_mono_of_nonneg
      ((ae_restrict_mem measurableSet_Ioc).mono fun u hu =>
        intervalIntegral.integral_nonneg (hinside u ⟨hu.1.le, hu.2⟩).2
          (fun v _ => densityModulusHistory_nonneg e S a (u, v)))
      (hi.mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le (hab.trans_lt hb).le]
        exact Icc_subset_Icc le_rfl hb.le)).1
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu' : u ∈ Icc a b := ⟨hu.1.le, hu.2⟩
    have hr := hroot u (hlate u hu')
    have hinc := intervalIntegral.integral_mono_interval (hinside u hu').1
      (hinside u hu').2 le_rfl
      (Eventually.of_forall fun v => densityModulusHistory_nonneg e S a (u, v))
      (densityModulusHistory_intervalIntegrable_on_row h.solution
        (hc.1.le.trans ha) hu'.1 hr.1 hr.2)
    exact hinc.trans ((hrow a u (hc.1.le.trans ha) hu'.1 (hlate u hu')).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hvar u (hlate u hu'))
        (hk₀ u (hlate u hu'))) le_rfl))
  have hlast := intervalIntegral.integral_mono_interval le_rfl hab hb.le
    (by
      rw [restrict_Ioc_eq_restrict_Icc, ← restrict_Ico_eq_restrict_Icc]
      filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
      exact add_nonneg (mul_nonneg (hk₀ u ⟨ha.trans hu.1, hu.2⟩) hKV)
        (hq₀ u ⟨ha.trans hu.1, hu.2⟩)) hi
  have hVb : 0 ≤ (eVariationOn (S.a b) (Icc (γ b) 0)).toReal := ENNReal.toReal_nonneg
  linarith only [hraw, hVa, hhist, hlast, hVb]

end EmcsfAcExtension.Global.Exterior
