module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Stability.PotentialIncomingIdentity
import EmcsfAcExtension.Local.Stability.PotentialRegularity
import EmcsfAcExtension.Local.Stability.PotentialParametric
import EmcsfAcExtension.Local.Calculus.Normalized

/-! # Full characteristic primitives for the classical potential

The outgoing zero-axis gauge fixes the primitive. A continuous
representative of the incoming constraint density then identifies
the actual incoming partial on every complete section.
-/

public section

open Set MeasureTheory Filter

namespace EmcsfAcExtension.Local

/-- The classical axis-gauge potential is its exact outgoing constraint
primitive, including both endpoints. The coefficient is one; no
smallness, derivative bound or estimate constant is needed. -/
theorem stab_potential_outgoing_primitive_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    S.A u v = ∫ w in u..v, S.AV u w := by
  have hm : MapsTo (fun w : ℝ => (u, w)) (Icc u v) (triangle 0 T) :=
    fun w hw => ⟨hu, hw.1, hw.2.trans hvT⟩
  have cp : ContinuousOn (fun w : ℝ => (u, w)) (Icc u v) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have cA := hset.c1.c1_A.continuousOn.comp cp hm
  have cAV := (stab_potential_constraint_continuous_c1 hset).comp cp hm
  have hd w (hw : w ∈ Ioo u v) : HasDerivAt (S.A u) (S.AV u w) w := by
    have hh := hasDerivWithinAt_v_aux hset.c1.c1_A hu hw.1.le (hw.2.le.trans hvT)
    rw [(hset.c1.eq_v (u, w) ⟨hu, hw.1.le, hw.2.le.trans hvT⟩ hw.1).2.2.2.2.1] at hh
    exact hh.hasDerivAt (Icc_mem_nhds hw.1 (hw.2.trans_le hvT))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv cA hd
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cAV)
  change (∫ w in u..v, S.AV u w) = S.A u v - S.A u u at hi
  rw [hset.data.2 u ⟨hu, huv.trans hvT⟩, sub_zero] at hi
  exact hi.symm

/-- A prescribed incoming derivative of the classical potential density
agrees with the A11p expression off the axis. This is uniqueness of a
within-interval derivative, with no extra regularity or constant. -/
theorem stab_potential_incoming_density_eq_of_derivative_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {u v z : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T)
    (hd : HasDerivWithinAt (fun t => S.AV t v) z (Icc 0 v) u) :
    z = S.AV u v * geomN (triangle 0 T) S u v -
      2 * S.nu u v / S.r u v * S.AV u v +
      2 * e * S.nu u v ^ 2 * S.lam u v / ((1 - S.mu u v) * S.r u v) *
        (starRingEnd ℂ (S.phi u v) * (S.xi u v / (S.nu u v : ℂ))).im := by
  have hUnique := uniqueDiffOn_Icc (hu.trans_lt huv) u ⟨hu, huv.le⟩
  exact (hd.derivWithin hUnique).symm.trans
    ((Stab.potential_constraint_incoming_derivative_c1 hset.c1 hu huv hvT).derivWithin hUnique)

/-- [internal]
The potential's incoming ordinary partial is the outgoing integral of
one continuous incoming constraint representative, a.e. on every full
section. This is the classical primitive identity required for the
potential strong-limit record; the full general-AC export belongs to
internal project record. No quantitative derivative bound or estimate constant is assumed.
-/
theorem stab_potential_incoming_primitive_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    ∃ H : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry H) (triangle 0 T) ∧
      (∀ u v, 0 ≤ u → u < v → v ≤ T →
        H u v = S.AV u v * geomN (triangle 0 T) S u v -
          2 * S.nu u v / S.r u v * S.AV u v +
          2 * e * S.nu u v ^ 2 * S.lam u v / ((1 - S.mu u v) * S.r u v) *
            (starRingEnd ℂ (S.phi u v) * (S.xi u v / (S.nu u v : ℂ))).im) ∧
      ∀ v ∈ Icc 0 T,
        AbsolutelyContinuousOnInterval (fun u => S.A u v) 0 v ∧
        ∀ᵐ u ∂volume.restrict (Icc 0 v),
          pdU (triangle 0 T) S.A u v = ∫ w in u..v, H u w := by
  obtain ⟨H, cH, hdH⟩ := stab_exists_continuous_potential_incoming_source_c1 hset
  refine ⟨H, cH, fun u v hu huv hvT =>
    stab_potential_incoming_density_eq_of_derivative_c1 hset hu huv hvT (hdH u v hu huv hvT), ?_⟩
  intro v hv
  obtain ⟨hAC, hDeriv⟩ := stab_incoming_derivative_of_triangle_primitive
    (stab_potential_constraint_continuous_c1 hset) cH (by
      intro t ht
      dsimp only [Fields.AV]
      rw [(hset.c1.axis t ⟨ht.1, le_rfl, ht.2⟩).1]
      simp)
    hdH (fun u v hp => stab_potential_outgoing_primitive_c1 hset hp.1 hp.2.1 hp.2.2) hv
  refine ⟨hAC, ?_⟩
  have hne₀ : ∀ᵐ u : ℝ, u ≠ 0 := by simp [ae_iff]
  have hneV : ∀ᵐ u : ℝ, u ≠ v := by simp [ae_iff]
  filter_upwards [hDeriv, ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae hne₀, ae_restrict_of_ae hneV] with u hdu hu hu0 huv
  have hleft : 0 < u := lt_of_le_of_ne hu.1 hu0.symm
  have hright : u < v := lt_of_le_of_ne hu.2 huv
  have hd := (hasDerivWithinAt_u_aux hset.c1.c1_A hu.1 hu.2 hv.2).hasDerivAt
    (Icc_mem_nhds hleft hright)
  exact hd.unique hdu

end EmcsfAcExtension.Local
