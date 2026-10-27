module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Params
public import EmcsfAcExtension.Local.Defs.Box
public import EmcsfAcExtension.Local.Defs.Envelope

/-! # Standing a priori and stability settings

Literal internal definitions from internal project record and
`source/charged_SF_new_version.tex`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The standing setting of §4.3 on the complete triangle `𝒟_s`
(charged_SF_new_version.tex:L4494–4506). -/
structure AprioriSetting (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ) : Prop where
  /-- The `pos` clause of `AprioriSetting` in internal project record. -/
  pos : 0 < s
  /-- The `c1` clause of `AprioriSetting` in internal project record. -/
  c1 : IsC1Solution e S (triangle 0 s)
  /-- The `data` clause of `AprioriSetting` in internal project record. -/
  data : IsRestartData S h s
  /-- The `eps` clause of `AprioriSetting` in internal project record. -/
  eps : datumVar h s ≤ ε
  /-- The `M_eq` clause of `AprioriSetting` in internal project record. -/
  M_eq : M = 1 + ‖h 0‖ + 10 * ε
  /-- The `box` clause of `AprioriSetting` in internal project record. -/
  box : BootBox S ε M (triangle 0 s)

/-- The standing setting of §4.4 (charged_SF_new_version.tex:L4955–4996): box with `c₀ = 1/4`, `C₀ =
1`, and
  the envelope
assumption (restart-stab-envelope-assumption, charged_SF_new_version.tex:L4993–4996) with constant
`A`. -/
structure StabSetting (e T ε M A : ℝ) (S : Fields) (h : ℝ → ℂ) : Prop where
  /-- The `pos` clause of `StabSetting` in internal project record. -/
  pos : 0 < T
  /-- The `c1` clause of `StabSetting` in internal project record. -/
  c1 : IsC1Solution e S (triangle 0 T)
  /-- The `data` clause of `StabSetting` in internal project record. -/
  data : IsRestartData S h T
  /-- The `box` clause of `StabSetting` in internal project record. -/
  box : StabBox S (1 / 4) 1 ε M (triangle 0 T)
  /-- The `env` clause of `StabSetting` in internal project record. -/
  env : (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) v) +
      (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) u) ≤ ENNReal.ofReal (A * ε)

end EmcsfAcExtension.Local
