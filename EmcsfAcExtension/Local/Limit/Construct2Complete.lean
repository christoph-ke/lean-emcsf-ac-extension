module

public import EmcsfAcExtension.Local.Limit.Construct2Strong
import EmcsfAcExtension.Local.Limit.ExistenceConstruct
import EmcsfAcExtension.Local.Limit.StabilityPointwise

/-! # The constructed strong approximation and its full comparison Cauchy norm

Both pending inputs are used to select actual classical solutions in a common
setting. No limiting solution, density identification or Cauchy assertion is
an input to this construction.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
Construct the full same-label Cauchy approximation and its actual frozen
strong limit. The universal positive thresholds precede all times, couplings,
data and sequences; comparison constants have no dependence on derivative
suprema. The full-triangle a distance also controls the initial normalized
datum distance, by the returned exact restart data. This proves the full
comparison norm, rather than just its j/k or scalar components. -/
theorem Null.constructed_strong_limit_of_inputs
    (hex : WholeTriangleExistenceStmt) (hstab : StabExtendedStmt) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T → datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        ∃ (hn : ℕ → ℝ → ℂ) (Sn : ℕ → Fields) (S : Fields),
          (∀ n, hn n 0 = h 0) ∧
          Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) ∧
          (∀ n, IsC1Solution e (Sn n) (triangle 0 T) ∧ IsRestartData (Sn n) (hn n) T) ∧
          (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
            jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) + geomDist T (Sn n) (Sn m) +
              supDist T (Sn n).a (Sn m).a + supDist T (Sn n).b (Sn m).b +
              supDist T (Sn n).phi (Sn m).phi < ENNReal.ofReal ρ) ∧
          StrongLimit e T Sn S ∧ IsRestartData S h T ∧ IsConstructedLimit e T h S := by
  obtain ⟨ηc, C, hηc, hC, hcomp⟩ := hstab 1 (by norm_num)
  obtain ⟨ηs, hηs, hstrong⟩ := Null.strong_limit_of_inputs hstab 1 (by norm_num)
  obtain ⟨ε, δ, q, hε, hδ, _, happ⟩ := Null.comparison_approximants_of_inputs hex
    (min ηc ηs) (lt_min hηc hηs)
  refine ⟨ε, δ, hε, hδ, ?_⟩
  intro T e h hT hac hd hscale
  obtain ⟨hn, Sn, _, hv, herr, hevar, _, hs, hsmall⟩ := happ T e h hT hac hd hscale
  obtain ⟨S, hlim, _, _, _, _, _, _⟩ := hstrong T e q (2 * datumM h T) Sn hn h hs hac hv herr
    (hsmall.trans (min_le_right _ _))
  have hC1 n := (hs n).c1
  have hdata n := (hs n).data
  have hgeom := hlim.lower_geometry_of_settings hs
  have hL p (hp : p ∈ triangle 0 T) : S.lam p.1 p.2 ≠ 0 := by
    have hh := (hgeom p hp).1
    linarith only [hh]
  have hrestart := restart_data_of_strongLimit hT hC1 hdata hac hv herr hlim hL
  refine ⟨hn, Sn, S, hv, hevar, fun n => ⟨hC1 n, hdata n⟩, ?_, hlim, hrestart,
    ⟨Sn, hn, hv, hevar, Eventually.of_forall (fun n => ⟨hC1 n, hdata n⟩), hlim⟩⟩
  intro ρ hρ
  obtain ⟨N, hN⟩ := data_dist_cauchy_of_stabSetting hs hac hv herr (ρ / C) (div_pos hρ hC)
  refine ⟨N, fun n hn' m hm' => ?_⟩
  apply (hcomp T e q (2 * datumM h T) (Sn n) (Sn m) (hn n) (hn m)
    (hs n) (hs m) (hsmall.trans (min_le_left _ _))).main.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hρ).2
  exact (lt_div_iff₀' hC).1 (hN n hn' m hm')

end EmcsfAcExtension.Local
