# Certification: Lean formalization of: Extension criterion for the spherically-symmetric Einstein–Maxwell-charged-scalar-field equations with absolutely continuous initial data

Extension Principle Collaboration. Paper: *Extension criterion for the spherically-symmetric Einstein–Maxwell-charged-scalar-field equations with absolutely continuous initial data* (link to be added).

This document describes the checks and their scope. The code is licensed
under the Apache License, Version 2.0 (`LICENSE`).

The formalization covers `EmcsfAcExtension.charged_main` (terminal incoming cone
continuation), `EmcsfAcExtension.restart_charged_local_BV` (small BV local
existence, bounds, stability and uniqueness in the absolutely continuous class)
and `EmcsfAcExtension.charged_main_real_uncharged` (the real uncharged case
claimed in the paper's abstract: for `e = 0` and a real scalar field the
continuation is real, with vanishing charge and potential on the whole extended
domain). Their verbatim Lean statements, including all mathematical hypotheses,
are in `README.md` and the three corresponding `EmcsfAcExtension/Frozen/` modules.
The paper states the third result in its abstract without a separate proof; its
Lean proof uses conjugation symmetry of the uncharged equations and the
uniqueness clause of the local theory for the same restarted solution.
There are no additional undischarged proof-provider assumptions. The local
constants are chosen uniformly before the time scale, coupling and data.

All three theorem anchors are SEALED. Their exact sealed proof bodies are:

```lean
-- EmcsfAcExtension.charged_main
by exact EmcsfAcExtension.Provider.chargedMain ui e hui S hS hgauge hmu hr hdata
-- EmcsfAcExtension.restart_charged_local_BV
by exact EmcsfAcExtension.Provider.restartChargedLocalBV
-- EmcsfAcExtension.charged_main_real_uncharged
by exact EmcsfAcExtension.Provider.chargedMainRealUncharged ui hui S hS hgauge hmu hr hdata hreal hterm
```

Each theorem's axiom footprint is exactly `propext`, `Classical.choice`,
`Quot.sound`. The project-wide axiom scan passes with zero draft anchors
and rejects every nonstandard axiom.

The code depends only on Lean and Mathlib, including the latter's transitive
dependencies. Lean is `leanprover/lean4:v4.35.0-rc3`. Mathlib is pinned to
`7d6757bc18680044fc0ff6efc8ee20494b408556`; `lake-manifest.json` records the
transitive dependency revisions. The export uses a plain Mathlib requirement
and the standard local Lake package directory.

Run `lake build` and `bash scripts/check_all.sh --no-build` from the export root.
The latter runs the frozen-anchor guard, elaborated ABI comparison and the
project-wide axiom scan. The guard checks every supplied baseline in
`FROZEN_MANIFEST.json`: definition-file and definition-closure byte hashes,
theorem prefix and suffix hashes, declaration identities, quarantine rules and
permitted short provider assemblies for SEALED bodies. The guard accepts the
registered export alone or applied to exactly the anchor's explicit binder
names, in declaration order; no other arguments are permitted.
`scripts/frozen_abi.py`
compares elaborated ABI hashes for all 32 exports. The ABI deliberately excludes
theorem proof terms so an approved seal does not change the statement ABI.
`scripts/axiom_scan.py` rejects every nonstandard axiom in this sealed release;
the manifest has zero draft anchors. Use `#print axioms` for each
theorem as shown in `README.md` to inspect its individual footprint.

These checks validate consistency with the supplied frozen baselines and Lean's
kernel; they do not authenticate the manifest's approval metadata or independently
verify the correspondence of the formal readings with the paper. The frozen files are
released byte for byte, so their comments still name three internal planning documents;
in all other files such references read "internal project record". The manifest's
approval fields name "the author". None of these records is needed to run the checks.
Internal planning documents are not included, and neither are the paper's LaTeX sources. Line citations refer to
the version of 25 October 2026 (SHA-256 `976a9e726f64140df7090272ec76f9d056aac8b5244afd21b533fa3191c2e8c2`, with the
coupling `q₀` written `e` in Lean); the 31 frozen files approved before 26 October cite the version of 21 October 2026
(SHA-256 `4e7263d274ff2d7b60e01a2ed7f66239228006d7d0479373763cdfb79a03b297`).

Independence note: the
development policy prohibited reading, importing, copying or adapting another
formalization project's code or planning material. During final verification of
one five-module contribution, an overly broad search accidentally displayed
approximately thirty one-line snippets from other projects' scratch copies. They
showed a standard Mathlib API pattern for almost everywhere differentiability of
absolutely continuous functions. The contribution had already been written, and
the same pattern was already used earlier in this project's own infrastructure.
The worker reported the incident. The author accepted the five modules without
a clean-room re-proof. Search boundaries were then tightened and worker read-log
checks added to the landing gate. Retrospective review also found directory-name
listings without other projects' file contents. This note discloses the incident;
it does not claim an incident-free development history. No other formalization
project is a code dependency.
