/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Infra.Calculus.PartialsC1
public import EmcsfAcExtension.Infra.Calculus.SectionalC1
public import EmcsfAcExtension.Infra.Calculus.MixedWithin
public import EmcsfAcExtension.Infra.Calculus.DiagonalChain
public import EmcsfAcExtension.Infra.Calculus.Glue

/-! # Within-domain calculus on characteristic domains

The positive internal project record API: unique differentiation, continuous sectional partials
and their C¹ converse on closed triangles, mixed derivatives from integral
representations, diagonal calculus and gluing over relative neighborhoods.
The degenerate-domain sanity checks are available separately in `Obstruction`.
-/
