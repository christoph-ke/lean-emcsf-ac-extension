module

public import EmcsfAcExtension.Local.Limit.AcBridgeAdmissibility
public import EmcsfAcExtension.Local.Limit.AcBridgeComparison
public import EmcsfAcExtension.Local.Limit.AcBridgeDataConvergence
import EmcsfAcExtension.Local.Broad.Propagation

/-! # Comparing an arbitrary AC sequence with its constructed data limit

internal project record item 7.2–5. The sequence is assumed only to solve the broad integral
system in its original common box. Smooth provenance is a conclusion of broad
uniqueness. In particular no fixed-vertex assumption is imposed.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Supply the constructed limit and quantitative comparisons for a general
AC sequence. The smallness threshold depends only on the fixed `c,H`; the
positive coefficients have only this fixed-parameter scope, before `T,e`,
the common size and every sequence. This is an interface for the four full
sequence nodes; it asserts no incoming-potential derivative convergence. -/
theorem ac_sequence_comparisons_of_inputs
    (hex : WholeTriangleExistenceStmt) (hstab : StabExtendedStmt)
    (c H : ℝ) (hc : 0 < c) (hH : 0 < H) :
    ∃ s B C : ℝ, 0 < s ∧ 0 < B ∧ 0 < C ∧
      ∀ (T e η M Cb : ℝ) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ)
        (Sn : ℕ → Fields) (Jn : ℕ → ℝ → ℝ),
        0 < T → 0 ≤ η → AbsolutelyContinuousOnInterval h 0 T →
        (∀ n, AbsolutelyContinuousOnInterval (hn n) 0 T) →
        (∀ n, IsSolution e (Sn n) (triangle 0 T)) →
        (∀ n, IsRestartData (Sn n) (hn n) T) →
        (∀ n, StabBox (Sn n) c Cb η M (triangle 0 T)) →
        (∀ n, IntervalIntegrable (Jn n) volume 0 T) →
        (∀ n, ∀ᵐ v ∂volume.restrict (Icc 0 T), ‖jOut (Sn n) 0 v‖ ≤ Jn n v) →
        (∀ n, (∫ v in (0 : ℝ)..T, Jn n v) ≤ H * η) →
        η ^ 2 + sigma e M T ≤ s →
        Tendsto (fun n => dataDist (hn n) h T) atTop (𝓝 0) →
        ∃ S : Fields, IsSolution e S (triangle 0 T) ∧ IsRestartData S h T ∧
          IsConstructedLimit e T h S ∧ ExistenceBounds B e T h S ∧
          datumM h T ≤ 3 * M ∧
          (∀ n, IsConstructedLimit e T (hn n) (Sn n) ∧ ExistenceBounds B e T (hn n) (Sn n) ∧
            datumM (hn n) T ≤ 3 * M) ∧
          (∀ n, StabConclusion C e T (hn n) h (Sn n) S ∧
            supDist T (Sn n).A S.A ≤ ENNReal.ofReal
              (C * |e| * T * (2 * max (datumM (hn n) T) (datumM h T)) * dataDist (hn n) h T) ∧
            supDist T (Sn n).mu S.mu ≤ ENNReal.ofReal (C * dataDist (hn n) h T) ∧
            (∀ p ∈ triangle 0 T, p.1 < p.2 →
              |(Sn n).Q p.1 p.2 - S.Q p.1 p.2| / (Sn n).r p.1 p.2 ^ 2 ≤
                C * |e| * (2 * max (datumM (hn n) T) (datumM h T)) * dataDist (hn n) h T)) := by
  obtain ⟨εa, δa, B, hεa, hδa, hB, hexis⟩ := ac_data_existence_of_inputs hex hstab
  obtain ⟨εp, δp, C, hεp, hδp, hC, hpair⟩ := constructed_extended_comparison_of_inputs hstab
  let ε := min εa εp
  let δ := min δa δp
  obtain ⟨s, hs, hadm⟩ := ac_data_admissible_of_initial_envelope c H ε δ hc hH
    (lt_min hεa hεp) (lt_min hδa hδp)
  refine ⟨s, B, C, hs, hB, hC, ?_⟩
  intro T e η M Cb hn h Sn Jn hT hη hac hacn hSn hdn hbox hJn hjn hmass hsmall hd
  have ha n := hadm T e η M Cb (hn n) (Sn n) (Jn n) hT hη (hacn n)
    (hSn n) (hdn n) (hbox n) (hJn n) (hjn n) (hmass n) hsmall
  obtain ⟨_, hv, hM, hscale⟩ := data_parameters_tendsto_of_dataDist (e := e) hT.le hacn hac hd
  have hεh : datumVar h T ≤ ε := le_of_tendsto hv (Eventually.of_forall fun n => (ha n).1)
  have hδh : chargedScale e h T ≤ δ := le_of_tendsto hscale
    (Eventually.of_forall fun n => (ha n).2.1)
  have hMh : datumM h T ≤ 3 * M := le_of_tendsto hM (Eventually.of_forall fun n => (ha n).2.2)
  obtain ⟨S, hS, hdS, hcS, hbS⟩ := hexis T e h hT hac
    (hεh.trans (min_le_left _ _)) (hδh.trans (min_le_left _ _))
  have hconstruct n : IsConstructedLimit e T (hn n) (Sn n) ∧ ExistenceBounds B e T (hn n) (Sn n) :=
      by
    obtain ⟨S', hS', hd', hc', hb'⟩ := hexis T e (hn n) hT (hacn n)
      ((ha n).1.trans (min_le_left _ _)) ((ha n).2.1.trans (min_le_left _ _))
    have he : (Sn n).EqOn S' (triangle 0 T) := broad_uniqueness hT (hSn n) hS'
      (fun v hv => ⟨(((hdn n).1 v hv).1).trans ((hd'.1 v hv).1).symm,
        (((hdn n).1 v hv).2).trans ((hd'.1 v hv).2).symm⟩)
      (fun t ht => ⟨(hdn n).2 t ht, hd'.2 t ht⟩)
    exact ⟨hc'.congr_of_eqOn he, hb'.congr hT.le he⟩
  refine ⟨S, hS, hdS, hcS, hbS, hMh,
    fun n => ⟨(hconstruct n).1, (hconstruct n).2, (ha n).2.2⟩, ?_⟩
  intro n
  exact hpair T e (hn n) h (Sn n) S hT (hacn n)
    ((ha n).1.trans (min_le_right _ _)) ((ha n).2.1.trans (min_le_right _ _)) hac
    (hεh.trans (min_le_right _ _)) (hδh.trans (min_le_right _ _)) (hconstruct n).1 hcS

end EmcsfAcExtension.Local
