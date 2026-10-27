# Lean formalization of: Extension criterion for the spherically-symmetric Einstein–Maxwell-charged-scalar-field equations with absolutely continuous initial data

Extension Principle Collaboration. Paper: *Extension criterion for the spherically-symmetric Einstein–Maxwell-charged-scalar-field equations with absolutely continuous initial data*, available at `<URL>`.

Licensed under the Apache License, Version 2.0 (`LICENSE`). Citation metadata: `CITATION.cff`.

**Line numbers.** Comments in the Lean sources cite the paper as `charged_SF_new_version.tex:L<line>`, the version of
25 October 2026 (6792 lines, SHA-256 `976a9e726f64140df7090272ec76f9d056aac8b5244afd21b533fa3191c2e8c2`). Its
`thm:charged-main` (L170–209) and `restart-charged-local-BV` (L4400–4458) are exactly the first two formalized
theorems. The third, `charged_main_real_uncharged`, formalizes the claim of the abstract (L34–38) about the real
uncharged Einstein–scalar-field system. The paper calls the scalar coupling `q₀`; the Lean code calls it `e`. The 32
frozen files are byte-identical to their approved form. Thirty-one of them cite the version of 21 October 2026 as
`charged_SF.tex:L<line>` (SHA-256 `4e7263d274ff2d7b60e01a2ed7f66239228006d7d0479373763cdfb79a03b297`); the third
theorem's file cites the abstract of the version of 25 October 2026. The paper's LaTeX sources are not part of this
release. Some comments refer to an "internal project record": the project's internal planning and proof
notes, which are not part of this release; nothing in the build or the checks depends on them.

This library formalizes three results for the massless charged scalar field system
in spherical symmetry: the terminal incoming cone continuation theorem
`EmcsfAcExtension.charged_main` (paper label `thm:charged-main`), the small BV
local theory in the absolutely continuous class
`EmcsfAcExtension.restart_charged_local_BV` (paper label
`restart-charged-local-BV`), including existence, bounds, stability and uniqueness,
and its real uncharged case `EmcsfAcExtension.charged_main_real_uncharged` (the
claim of the paper's abstract): for coupling `e = 0` and a real scalar field, the
continuation of `charged_main` is again real, with vanishing charge and potential.
The terminal result allows arbitrary coupling and data size subject to its
written hypotheses. In the local result, the positive constants ε₀, δ₀ and C
are chosen before T, e and the data, and hence are uniform in those variables.
The formal statements below specify the precise mathematical hypotheses.

The code depends only on Lean and Mathlib (including Mathlib's pinned transitive
dependencies). No other formalization project is a dependency.
The toolchain is `leanprover/lean4:v4.35.0-rc3`; Mathlib is pinned to
`7d6757bc18680044fc0ff6efc8ee20494b408556` in the Lake configuration and manifest.

All three theorem anchors are SEALED under the approved seal rulings. Seal states
are read from the manifest; historical header comments are preserved byte for
byte. Their exact sealed proof bodies are:

```lean
-- EmcsfAcExtension.charged_main
by exact EmcsfAcExtension.Provider.chargedMain ui e hui S hS hgauge hmu hr hdata
-- EmcsfAcExtension.restart_charged_local_BV
by exact EmcsfAcExtension.Provider.restartChargedLocalBV
-- EmcsfAcExtension.charged_main_real_uncharged
by exact EmcsfAcExtension.Provider.chargedMainRealUncharged ui hui S hS hgauge hmu hr hdata hreal hterm
```

With the specified Lean toolchain, Lake, Python 3.11 or later, and the pinned
Mathlib dependencies available, run from the export root:

```sh
lake build
python3 scripts/check_frozen_anchors.py --root . --manifest FROZEN_MANIFEST.json
python3 scripts/frozen_abi.py frozen --check FROZEN_MANIFEST.json
python3 scripts/axiom_scan.py
bash scripts/check_all.sh --no-build
```

`bash scripts/check_all.sh` also runs the build. The Python verification tools
use `.lake/verification` for transient Lean files; `FROZEN_ABI_TMP` and
`AXIOM_SCAN_TMP` can override that location. The checks need no unpublished paper
or private project records. They verify the supplied manifest; they do not
establish approval provenance or equivalence with the paper independently.

For the kernel-reported axioms, create the transient directory with
`mkdir -p .lake/verification`, save the following as
`.lake/verification/CheckAxioms.lean`, and run
`lake env lean -j 4 .lake/verification/CheckAxioms.lean` after building:

```lean
import EmcsfAcExtension.Frozen.ChargedMain
import EmcsfAcExtension.Frozen.RestartChargedLocalBV
import EmcsfAcExtension.Frozen.ChargedMainRealUncharged
#print axioms EmcsfAcExtension.charged_main
#print axioms EmcsfAcExtension.restart_charged_local_BV
#print axioms EmcsfAcExtension.charged_main_real_uncharged
```

All three theorems have exactly the axiom footprint `propext`, `Classical.choice`,
and `Quot.sound`. The project-wide axiom scan passes with zero draft anchors
and rejects every nonstandard axiom.

`FROZEN_MANIFEST.json` binds 32 frozen exports to declaration identities, source
hashes, elaborated ABI hashes and theorem states. Definition files and each
theorem's transitive frozen definition closure are byte-hashed. The theorem
prefix and suffix hashes protect statements and imports; ABI hashes protect the
elaborated types and definitions. A SEALED theorem body must be a short checked
assembly of its registered provider export, within the manifest limits. The
guard accepts that export alone or applied to exactly the anchor's explicit
binder names, in declaration order; no other arguments are permitted.
The checker has no rebaseline command. The manifest is not a signature and is not a
byte hash of every implementation proof. See `CERTIFICATION.md` for scope,
current status and the independence note.

The following declarations are copied verbatim, without their proof bodies,
from the frozen files. They use `namespace EmcsfAcExtension`,
`open MeasureTheory Set Filter Topology Complex` and `open scoped ENNReal`.
The three modules must be imported explicitly; the root module is deliberately
small and does not re-export the theorem anchors.

```lean
theorem charged_main (ui e : ℝ) (hui : ui < 0) (S : Fields)
    (hS : IsSolution e S (origDomain ui))
    (hgauge : ∀ t, ui ≤ t → t < 0 → S.A t t = 0)
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (hr : ∀ v ∈ Icc ui 0, S.r ui v = (v - ui) / 2)
    (hdata : AbsolutelyContinuousOnInterval (S.a ui) ui 0) :
    (BddAbove ((fun u => ∫ s in ui..u, signedExpIntegrand S s 0) '' Ioo ui 0) ↔
      ∫⁻ u in Ico ui 0, ENNReal.ofReal (positiveExpIntegrand S u 0) < ⊤) ∧
    (BddAbove ((fun u => ∫ s in ui..u, signedExpIntegrand S s 0) '' Ioo ui 0) →
      (∃ us vp : ℝ, ∃ S' : Fields, ui < us ∧ us < 0 ∧ 0 < vp ∧
        IsSolution e S' (origDomain ui ∪ triangle us vp) ∧
        (∀ t ∈ Icc us vp, S'.A t t = 0) ∧ S'.EqOn S (origDomain ui)) ∧
      eVariationOn (fun u => S.phi u 0) (Ico ui 0) < ⊤ ∧
      eVariationOn (fun u => S.b u 0) (Ico ui 0) < ⊤ ∧
      eVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) < ⊤ ∧
      (⨆ v ∈ Ioo ui 0, ∫⁻ u in Ico ui v, ENNReal.ofReal (positiveExpIntegrand S u v)) < ⊤)
```

```lean
theorem charged_main_real_uncharged (ui : ℝ) (hui : ui < 0) (S : Fields)
    (hS : IsSolution 0 S (origDomain ui))
    (hgauge : ∀ t, ui ≤ t → t < 0 → S.A t t = 0)
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (hr : ∀ v ∈ Icc ui 0, S.r ui v = (v - ui) / 2)
    (hdata : AbsolutelyContinuousOnInterval (S.a ui) ui 0)
    (hreal : ∀ p ∈ origDomain ui, (S.phi p.1 p.2).im = 0)
    (hterm : BddAbove ((fun u => ∫ s in ui..u, signedExpIntegrand S s 0) '' Ioo ui 0)) :
    ∃ us vp : ℝ, ∃ S' : Fields, ui < us ∧ us < 0 ∧ 0 < vp ∧
      IsSolution 0 S' (origDomain ui ∪ triangle us vp) ∧
      (∀ t ∈ Icc us vp, S'.A t t = 0) ∧ S'.EqOn S (origDomain ui) ∧
      ∀ p ∈ origDomain ui ∪ triangle us vp,
        (S'.phi p.1 p.2).im = 0 ∧ (S'.theta p.1 p.2).im = 0 ∧ (S'.xi p.1 p.2).im = 0 ∧
        S'.Q p.1 p.2 = 0 ∧ S'.A p.1 p.2 = 0
```

```lean
theorem restart_charged_local_BV :
    ∃ ε₀ δ₀ C : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ T e : ℝ, 0 < T →
    -- existence on the closed triangle, bounds, and uniqueness in the broad class
    (∀ h : ℝ → ℂ, AbsolutelyContinuousOnInterval h 0 T →
      datumVar h T ≤ ε₀ → |e| * (T / 2) * (1 + ‖h 0‖ + 10 * datumVar h T) ≤ δ₀ →
      ∃ S : Fields,
        IsSolution e S (triangle 0 T) ∧
        (∀ v ∈ Icc 0 T, S.r 0 v = v / 2 ∧ S.a 0 v = h v) ∧
        (∀ t ∈ Icc 0 T, S.A t t = 0) ∧
        (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.a u) u T) ∧
        (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v) ∧
        AbsolutelyContinuousOnInterval (fun t => S.phi t t) 0 T ∧
        (⨆ u ∈ Icc 0 T, eVariationOn (S.a u) (Icc u T)) +
            (⨆ v ∈ Icc 0 T, covVarIn e S.A S.b 0 v v) ≤
          ENNReal.ofReal (C * datumVar h T) ∧
        (∀ p ∈ triangle 0 T,
          ‖S.phi p.1 p.2‖ ≤ 1 + ‖h 0‖ + 10 * datumVar h T ∧
          ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ + ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤
            C * datumVar h T ∧
          |S.lam p.1 p.2 - 1 / 2| + |S.nu p.1 p.2 + 1 / 2| + S.mu p.1 p.2 ≤
            C * datumVar h T ^ 2 ∧
          |S.Q p.1 p.2| ≤
            C * |e| * (1 + ‖h 0‖ + 10 * datumVar h T) * datumVar h T * S.r p.1 p.2 ^ 2) ∧
        (∀ u ∈ Icc 0 T,
          eVariationOn (S.lam u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (S.nu u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (S.mu u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (S.Omega2 u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2)) ∧
        (∀ v ∈ Icc 0 T,
          eVariationOn (fun u => S.lam u v) (Icc 0 v) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (fun u => S.nu u v) (Icc 0 v) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (fun u => S.mu u v) (Icc 0 v) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (fun u => S.Omega2 u v) (Icc 0 v) ≤
            ENNReal.ofReal (C * datumVar h T ^ 2)) ∧
        (∀ u ∈ Icc 0 T,
          AbsolutelyContinuousOnInterval (S.lam u) u T ∧
          AbsolutelyContinuousOnInterval (S.nu u) u T ∧
          AbsolutelyContinuousOnInterval (S.mu u) u T ∧
          AbsolutelyContinuousOnInterval (S.Omega2 u) u T) ∧
        (∀ v ∈ Icc 0 T,
          AbsolutelyContinuousOnInterval (fun u => S.lam u v) 0 v ∧
          AbsolutelyContinuousOnInterval (fun u => S.nu u v) 0 v ∧
          AbsolutelyContinuousOnInterval (fun u => S.mu u v) 0 v ∧
          AbsolutelyContinuousOnInterval (fun u => S.Omega2 u v) 0 v) ∧
        ContDiffOn ℝ 1 (Function.uncurry S.r) (triangle 0 T) ∧
        (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S.b u v) (Icc 0 v)) ≤
          ENNReal.ofReal (C * datumVar h T) ∧
        (∀ T' ∈ Ioc 0 T, ∀ S' : Fields, IsSolution e S' (triangle 0 T') →
          (∀ v ∈ Icc 0 T', S'.r 0 v = v / 2 ∧ S'.a 0 v = h v) →
          (∀ t ∈ Icc 0 T', S'.A t t = 0) → S'.EqOn S (triangle 0 T'))) ∧
    -- Lipschitz stability in `W^{1,1}` of the datum, fixed gauge
    (∀ (h₁ h₂ : ℝ → ℂ) (S₁ S₂ : Fields),
      AbsolutelyContinuousOnInterval h₁ 0 T → datumVar h₁ T ≤ ε₀ →
      |e| * (T / 2) * (1 + ‖h₁ 0‖ + 10 * datumVar h₁ T) ≤ δ₀ →
      AbsolutelyContinuousOnInterval h₂ 0 T → datumVar h₂ T ≤ ε₀ →
      |e| * (T / 2) * (1 + ‖h₂ 0‖ + 10 * datumVar h₂ T) ≤ δ₀ →
      IsSolution e S₁ (triangle 0 T) → (∀ v ∈ Icc 0 T, S₁.r 0 v = v / 2 ∧ S₁.a 0 v = h₁ v) →
      (∀ t ∈ Icc 0 T, S₁.A t t = 0) →
      IsSolution e S₂ (triangle 0 T) → (∀ v ∈ Icc 0 T, S₂.r 0 v = v / 2 ∧ S₂.a 0 v = h₂ v) →
      (∀ t ∈ Icc 0 T, S₂.A t t = 0) →
      (∃ J K : ℝ → ℝ, IntegrableOn J (Icc 0 T) ∧ IntegrableOn K (Icc 0 T) ∧
        (∀ u ∈ Icc 0 T, ∀ᵐ v ∂(volume.restrict (Icc u T)),
          ‖jOut S₁ u v - jOut S₂ u v‖ ≤ J v) ∧
        (∀ v ∈ Icc 0 T, ∀ᵐ u ∂(volume.restrict (Icc 0 v)),
          ‖kIn e S₁ u v - kIn e S₂ u v‖ ≤ K u) ∧
        ∀ p₁ ∈ triangle 0 T, ∀ p₂ ∈ triangle 0 T, ∀ p₃ ∈ triangle 0 T, ∀ p₄ ∈ triangle 0 T,
          (∫ v in (0 : ℝ)..T, J v) + (∫ u in (0 : ℝ)..T, K u) +
            (|S₁.lam p₁.1 p₁.2 - S₂.lam p₁.1 p₁.2| + |S₁.nu p₁.1 p₁.2 - S₂.nu p₁.1 p₁.2| +
              |S₁.r p₁.1 p₁.2 - S₂.r p₁.1 p₁.2| / S₁.r p₁.1 p₁.2) +
            ‖S₁.a p₂.1 p₂.2 - S₂.a p₂.1 p₂.2‖ + ‖S₁.b p₃.1 p₃.2 - S₂.b p₃.1 p₃.2‖ +
            ‖S₁.phi p₄.1 p₄.2 - S₂.phi p₄.1 p₄.2‖ ≤
          C * (‖h₁ 0 - h₂ 0‖ + datumVar (h₁ - h₂) T)) ∧
      (⨆ u ∈ Icc 0 T, eVariationOn (fun v => S₁.a u v - S₂.a u v) (Icc u T)) +
          (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S₁.b u v - S₂.b u v) (Icc 0 v)) ≤
        ENNReal.ofReal (C * (‖h₁ 0 - h₂ 0‖ + datumVar (h₁ - h₂) T)))
```
