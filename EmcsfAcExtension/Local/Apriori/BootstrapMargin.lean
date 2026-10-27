module

public import EmcsfAcExtension.Local.Defs.Bounds
public import EmcsfAcExtension.Local.Defs.Params

/-! # Passing from a positive bootstrap margin to the datum variation

internal project record, audit note N3, requires the bootstrap to run with a parameter
strictly larger than the datum variation. This module passes the resulting
uniform estimates to the endpoint without trying to initialize a box with
zero width. It is an assembly helper, not a bootstrap-improvement assumption.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem le_endpoint_of_margin {β : Type*} [TopologicalSpace β]
    [Preorder β] [OrderClosedTopology β] {d η : ℝ} {x : β} {f : ℝ → β}
    (hη : 0 < η) (hf : ContinuousAt f d)
    (hbound : ∀ z, d < z → z < d + η → x ≤ f z) : x ≤ f d := by
  apply ge_of_tendsto (hf.tendsto.mono_left
    (show 𝓝[>] d ≤ 𝓝 d from nhdsWithin_le_nhds))
  have hupper : ∀ᶠ z in 𝓝[>] d, z < d + η :=
    (eventually_lt_nhds (lt_add_of_pos_right d hη)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hupper] with z hz hzu
  exact hbound z hz hzu

/-- Uniform smooth bounds for every sufficiently small positive excess over
the datum variation imply the bounds at the datum variation itself.
The same constant `C` is used throughout; it must have been chosen before
the data in the supplying a priori theorem. No estimate is inferred from
a bound whose constant depends on the excess parameter.
-/
theorem smoothBounds_of_margin {C e T η : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hη : 0 < η)
    (hmargin : ∀ ε', datumVar h T < ε' → ε' < datumVar h T + η →
      SmoothBounds C e T ε' (1 + ‖h 0‖ + 10 * ε') S) :
    SmoothBounds C e T (datumVar h T) (datumM h T) S := by
  let d := datumVar h T
  have hbase := hmargin (d + η / 2) (by dsimp only [d]; linarith only [hη])
    (by dsimp only [d]; linarith only [hη])
  refine {
    geom := ?_
    mu_nonneg := hbase.mu_nonneg
    phi_le := ?_
    ratio := ?_
    charge := ?_
    env := ?_
    tvj := hbase.tvj
    tvk := hbase.tvk
    tv_in := ?_
    geomTV_out := ?_
    geomTV_in := ?_
    geomEnv := ?_
    crossTV := hbase.crossTV
    hardyOut := hbase.hardyOut
    hardyIn := hbase.hardyIn
    massFlux := ?_
  }
  · intro p hp
    exact le_endpoint_of_margin (d := datumVar h T) (f := fun z => C * z ^ 2) hη (by fun_prop)
      (fun ε' hlo hhi => (hmargin ε' hlo hhi).geom p hp)
  · intro p hp
    change ‖S.phi p.1 p.2‖ ≤ 1 + ‖h 0‖ + 10 * datumVar h T
    exact le_endpoint_of_margin (d := datumVar h T)
      (f := fun z => 1 + ‖h 0‖ + 10 * z) hη (by fun_prop)
      (fun ε' hlo hhi => (hmargin ε' hlo hhi).phi_le p hp)
  · intro p hp
    exact le_endpoint_of_margin (d := datumVar h T) (f := fun z => C * z) hη (by fun_prop)
      (fun ε' hlo hhi => (hmargin ε' hlo hhi).ratio p hp)
  · intro p hp
    change |S.Q p.1 p.2| ≤
      C * |e| * (1 + ‖h 0‖ + 10 * datumVar h T) * datumVar h T * S.r p.1 p.2 ^ 2
    exact le_endpoint_of_margin (d := datumVar h T)
      (f := fun z => C * |e| * (1 + ‖h 0‖ + 10 * z) * z * S.r p.1 p.2 ^ 2)
      hη (by fun_prop)
      (fun ε' hlo hhi => (hmargin ε' hlo hhi).charge p hp)
  · exact le_endpoint_of_margin (d := datumVar h T)
      (f := fun z => ENNReal.ofReal (C * z)) hη
      (ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop))
      (fun ε' hlo hhi => (hmargin ε' hlo hhi).env)
  · intro v hv
    exact le_endpoint_of_margin (d := datumVar h T)
      (f := fun z => ENNReal.ofReal (C * z)) hη
      (ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop))
      (fun ε' hlo hhi => (hmargin ε' hlo hhi).tv_in v hv)
  · intro u hu
    exact le_endpoint_of_margin (d := datumVar h T)
      (f := fun z => ENNReal.ofReal (C * z ^ 2)) hη
      (ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop))
      (fun ε' hlo hhi => (hmargin ε' hlo hhi).geomTV_out u hu)
  · intro v hv
    exact le_endpoint_of_margin (d := datumVar h T)
      (f := fun z => ENNReal.ofReal (C * z ^ 2)) hη
      (ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop))
      (fun ε' hlo hhi => (hmargin ε' hlo hhi).geomTV_in v hv)
  · exact le_endpoint_of_margin (d := datumVar h T)
      (f := fun z => ENNReal.ofReal (C * z ^ 2)) hη
      (ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop))
      (fun ε' hlo hhi => (hmargin ε' hlo hhi).geomEnv)
  · constructor
    · intro u hu
      exact le_endpoint_of_margin (d := datumVar h T)
        (f := fun z => ENNReal.ofReal (C * z ^ 2)) hη
        (ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop))
        (fun ε' hlo hhi => (hmargin ε' hlo hhi).massFlux.1 u hu)
    · intro v hv
      exact le_endpoint_of_margin (d := datumVar h T)
        (f := fun z => ENNReal.ofReal (C * z ^ 2)) hη
        (ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop))
        (fun ε' hlo hhi => (hmargin ε' hlo hhi).massFlux.2 v hv)

end EmcsfAcExtension.Local
