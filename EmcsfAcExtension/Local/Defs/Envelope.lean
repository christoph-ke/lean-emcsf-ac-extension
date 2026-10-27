module

public import EmcsfAcExtension.Local.Defs.Renormalized
public import EmcsfAcExtension.Frozen.Triangle
public import EmcsfAcExtension.Infra.Null.Envelope

/-! # Characteristic envelopes and distances

Literal internal definitions from internal project record and
`source/charged_SF_new_version.tex`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

section Envelope

variable {E : Type*} [NormedAddCommGroup E]

/-- [def-node restart-sec-independent-area#characteristic-envelopes]
[def-node restart-sec-bv-stability-independent#characteristic-envelopes]
Outgoing-label envelope `J(v) = sup_{a ≤ u ≤ v} |f(u,v)|` (charged_SF_new_version.tex:L4615–4620,
  charged_SF_new_version.tex:L4988–4992), in `ℝ≥0∞`
(no junk value: an unbounded section gives `⊤`). -/
noncomputable abbrev outEnv (a : ℝ) (f : ℝ → ℝ → E) (v : ℝ) : ℝ≥0∞ :=
  normEnvelope f a v

/-- Unfold `outEnv` to its literal internal project record formula. -/
theorem outEnv_def (a : ℝ) (f : ℝ → ℝ → E) (v : ℝ) :
    outEnv a f v =
  ⨆ u ∈ Icc a v, ‖f u v‖ₑ := rfl

/-- [def-node restart-sec-independent-area#characteristic-envelopes]
[def-node restart-sec-bv-stability-independent#characteristic-envelopes]
Incoming-label envelope `K(u) = sup_{u ≤ v ≤ b} |f(u,v)|` (charged_SF_new_version.tex:L4615–4620,
  charged_SF_new_version.tex:L4988–4992). -/
noncomputable def inEnv (b : ℝ) (f : ℝ → ℝ → E) (u : ℝ) : ℝ≥0∞ := ⨆ v ∈ Icc u b, ‖f u v‖ₑ

/-- Unfold `inEnv` to its literal internal project record formula. -/
theorem inEnv_def (b : ℝ) (f : ℝ → ℝ → E) (u : ℝ) :
    inEnv b f u =
  ⨆ v ∈ Icc u b, ‖f u v‖ₑ := rfl

/-- [def-node restart-stab-broad-uniqueness#normalized-field-distance]
Uniform distance on the closed triangle `𝒟_T`. -/
noncomputable def supDist (T : ℝ) (f g : ℝ → ℝ → E) : ℝ≥0∞ :=
  ⨆ p ∈ triangle 0 T, ‖f p.1 p.2 - g p.1 p.2‖ₑ

/-- Unfold `supDist` to its literal internal project record formula. -/
theorem supDist_def (T : ℝ) (f g : ℝ → ℝ → E) :
    supDist T f g =
  ⨆ p ∈ triangle 0 T, ‖f p.1 p.2 - g p.1 p.2‖ₑ := rfl

end Envelope

/-- [def-node restart-sec-bv-stability-independent#comparison-distances]
`Δ_j = ∫_0^T sup_{0 ≤ u ≤ v} |δj(u,v)| dv` (charged_SF_new_version.tex:L5266–5266) for two `C¹`
solutions on
  `𝒟_T`. -/
noncomputable def jDist (T : ℝ) (S₁ S₂ : Fields) : ℝ≥0∞ :=
  ∫⁻ v in Icc 0 T, outEnv 0 (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v) v

/-- [def-node restart-sec-bv-stability-independent#comparison-distances]
`Δ_k = ∫_0^T sup_{u ≤ v ≤ T} |δk(u,v)| du` (charged_SF_new_version.tex:L5266–5266). -/
noncomputable def kDist (e T : ℝ) (S₁ S₂ : Fields) : ℝ≥0∞ :=
  ∫⁻ u in Icc 0 T, inEnv T (fun u v => kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v) u

/-- [def-node restart-sec-bv-stability-independent#comparison-distances]
`G = sup (|δλ| + |δν| + |δr|/r₁)` on `𝒟_T` (charged_SF_new_version.tex:L5085–5087); at the axis
Lean's `x/0 =
  0`. -/
noncomputable def geomDist (T : ℝ) (S₁ S₂ : Fields) : ℝ≥0∞ :=
  ⨆ p ∈ triangle 0 T, ENNReal.ofReal (|S₁.lam p.1 p.2 - S₂.lam p.1 p.2| +
    |S₁.nu p.1 p.2 - S₂.nu p.1 p.2| + |S₁.r p.1 p.2 - S₂.r p.1 p.2| / S₁.r p.1 p.2)

end EmcsfAcExtension.Local
