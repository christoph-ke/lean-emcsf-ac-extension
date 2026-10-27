module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Defs.Envelope
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Infra.Mixed.TriangleCauchy

/-! # Realizing envelopes for the actual strong-limit derivatives

The inheritance step of internal project record, `#limit-renormalized-envelope-bound`.
`StrongLimit` supplies errors against the actual frozen `jOut` and `kIn`.
Fatou realizes measurable envelopes without losing the sum of their two masses.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem liminf_add_le {a b : ℕ → ℝ≥0∞} :
    liminf a atTop + liminf b atTop ≤ liminf (a + b) atTop := by
  rw [liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat,
    liminf_eq_iSup_iInf_of_nat]
  apply ENNReal.iSup_add_iSup_le
  intro i j
  apply le_iSup_of_le (max i j)
  apply le_iInf₂
  intro k hk
  exact add_le_add (iInf₂_le_of_le k ((le_max_left i j).trans hk) le_rfl)
    (iInf₂_le_of_le k ((le_max_right i j).trans hk) le_rfl)

/-- [internal]
Realize envelopes for the actual frozen derivatives of a strong limit and retain
the approximants' combined mass bound with coefficient one. The supplied constant
`C` precedes coupling, time, data size and approximants; its scope is exactly the
scope of the eventual smooth bound. No new constant or smallness threshold is chosen.
The nonnegative extended envelopes have finite integrals, hence finite real L¹
representatives. Domination is a.e. on each individual natural section. -/
theorem Null.limit_renormalized_envelope_bound_of_strongLimit
    {C e T ε : ℝ} {εn : ℕ → ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hT : 0 < T) (hS : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hlim : StrongLimit e T Sn S) (hε : Tendsto εn atTop (𝓝 ε))
    (hbound : ∀ᶠ n in atTop,
      (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) (Sn n)) v) +
        (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) (Sn n)) u) ≤
          ENNReal.ofReal (C * εn n)) :
    ∃ J K : ℝ → ℝ≥0∞, Measurable J ∧ Measurable K ∧
      (∫⁻ v in Icc 0 T, J v) < ⊤ ∧ (∫⁻ u in Icc 0 T, K u) < ⊤ ∧
      (∀ u ∈ Icc 0 T, ∀ᵐ v ∂volume.restrict (Icc u T), ‖jOut S u v‖ₑ ≤ J v) ∧
      (∀ v ∈ Icc 0 T, ∀ᵐ u ∂volume.restrict (Icc 0 v), ‖kIn e S u v‖ₑ ≤ K u) ∧
      (∫⁻ v in Icc 0 T, J v) + (∫⁻ u in Icc 0 T, K u) ≤ ENNReal.ofReal (C * ε) := by
  classical
  obtain ⟨Dj, hDjm, hDjlim, hDj⟩ := hlim.env_j
  obtain ⟨Dk, hDkm, hDklim, hDk⟩ := hlim.env_k
  let Jn n := (Icc (0 : ℝ) T).indicator (outEnv 0 (jC1 (triangle 0 T) (Sn n)))
  let Kn n := (Icc (0 : ℝ) T).indicator (inEnv T (kC1 e (triangle 0 T) (Sn n)))
  have hJm n : Measurable (Jn n) :=
    measurable_indicator_normEnvelope ((hS n).continuousOn_jC1 hT)
  have hKm n : Measurable (Kn n) :=
    Mixed.measurable_indicator_incoming_envelope hT.le ((hS n).continuousOn_kC1 hT)
  let J v := liminf (fun n => Jn n v + Dj n v) atTop
  let K u := liminf (fun n => Kn n u + Dk n u) atTop
  have hJ : Measurable J := Measurable.liminf (fun n => (hJm n).add (hDjm n))
  have hK : Measurable K := Measurable.liminf (fun n => (hKm n).add (hDkm n))
  have hjdom : ∀ u ∈ Icc 0 T, ∀ᵐ v ∂volume.restrict (Icc u T), ‖jOut S u v‖ₑ ≤ J v := by
    intro u hu
    filter_upwards [ae_all_iff.mpr (fun n => hDj n u hu),
      ae_restrict_mem measurableSet_Icc] with v hv hmem
    apply le_liminf_of_le (by isBoundedDefault)
    apply Eventually.of_forall
    intro n
    have hvT : v ∈ Icc 0 T := ⟨hu.1.trans hmem.1, hmem.2⟩
    have he : Jn n v = outEnv 0 (jC1 (triangle 0 T) (Sn n)) v := indicator_of_mem hvT _
    rw [he]
    have htri : ‖jOut S u v‖ₑ ≤ ‖jC1 (triangle 0 T) (Sn n) u v‖ₑ +
        ‖jC1 (triangle 0 T) (Sn n) u v - jOut S u v‖ₑ := by
      simpa only [sub_sub_cancel] using (enorm_sub_le
        (a := jC1 (triangle 0 T) (Sn n) u v) (b := jC1 (triangle 0 T) (Sn n) u v - jOut S u v))
    exact htri.trans (add_le_add (enorm_le_normEnvelope _ ⟨hu.1, hmem.1⟩) (hv n))
  have hkdom : ∀ v ∈ Icc 0 T, ∀ᵐ u ∂volume.restrict (Icc 0 v), ‖kIn e S u v‖ₑ ≤ K u := by
    intro v hv
    filter_upwards [ae_all_iff.mpr (fun n => hDk n v hv),
      ae_restrict_mem measurableSet_Icc] with u hu hmem
    apply le_liminf_of_le (by isBoundedDefault)
    apply Eventually.of_forall
    intro n
    have huT : u ∈ Icc 0 T := ⟨hmem.1, hmem.2.trans hv.2⟩
    have he : Kn n u = inEnv T (kC1 e (triangle 0 T) (Sn n)) u := indicator_of_mem huT _
    rw [he]
    have henv : ‖kC1 e (triangle 0 T) (Sn n) u v‖ₑ ≤
        inEnv T (kC1 e (triangle 0 T) (Sn n)) u := le_iSup₂_of_le v ⟨hmem.2, hv.2⟩ le_rfl
    have htri : ‖kIn e S u v‖ₑ ≤ ‖kC1 e (triangle 0 T) (Sn n) u v‖ₑ +
        ‖kC1 e (triangle 0 T) (Sn n) u v - kIn e S u v‖ₑ := by
      simpa only [sub_sub_cancel] using (enorm_sub_le
        (a := kC1 e (triangle 0 T) (Sn n) u v) (b := kC1 e (triangle 0 T) (Sn n) u v - kIn e S u v))
    exact htri.trans (add_le_add henv (hu n))
  have hfatj : (∫⁻ v in Icc 0 T, J v) ≤
      liminf (fun n => ∫⁻ v in Icc 0 T, Jn n v + Dj n v) atTop :=
    lintegral_liminf_le' (fun n => ((hJm n).add (hDjm n)).aemeasurable)
  have hfatk : (∫⁻ u in Icc 0 T, K u) ≤
      liminf (fun n => ∫⁻ u in Icc 0 T, Kn n u + Dk n u) atTop :=
    lintegral_liminf_le' (fun n => ((hKm n).add (hDkm n)).aemeasurable)
  have hmass : (∫⁻ v in Icc 0 T, J v) + (∫⁻ u in Icc 0 T, K u) ≤ ENNReal.ofReal (C * ε) := by
    apply (add_le_add hfatj hfatk).trans
    apply liminf_add_le.trans
    change liminf (fun n => (∫⁻ v in Icc 0 T, Jn n v + Dj n v) +
      (∫⁻ u in Icc 0 T, Kn n u + Dk n u)) atTop ≤ ENNReal.ofReal (C * ε)
    have heq : (fun n => (∫⁻ v in Icc 0 T, Jn n v + Dj n v) +
        (∫⁻ u in Icc 0 T, Kn n u + Dk n u)) =
        (fun n => (∫⁻ v in Icc 0 T, Jn n v) + (∫⁻ u in Icc 0 T, Kn n u)) +
          (fun n => (∫⁻ v in Icc 0 T, Dj n v) + (∫⁻ u in Icc 0 T, Dk n u)) := by
      funext n
      rw [lintegral_add_left (hJm n), lintegral_add_left (hKm n)]
      simp only [Pi.add_apply]
      ac_rfl
    rw [heq, ENNReal.liminf_add_of_right_tendsto_zero (by simpa using hDjlim.add hDklim)]
    have hevent : ∀ᶠ n in atTop, (∫⁻ v in Icc 0 T, Jn n v) +
        (∫⁻ u in Icc 0 T, Kn n u) ≤ ENNReal.ofReal (C * εn n) := by
      filter_upwards [hbound] with n hn
      simpa only [Jn, Kn, lintegral_indicator measurableSet_Icc,
        Measure.restrict_restrict measurableSet_Icc,
        inter_self] using hn
    apply (liminf_le_liminf hevent).trans_eq
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hε.const_mul C)).liminf_eq
  exact ⟨J, K, hJ, hK,
    lt_of_le_of_lt ((le_add_right le_rfl).trans hmass) ENNReal.ofReal_lt_top,
    lt_of_le_of_lt ((le_add_left le_rfl).trans hmass) ENNReal.ofReal_lt_top,
    hjdom, hkdom, hmass⟩

end EmcsfAcExtension.Local
