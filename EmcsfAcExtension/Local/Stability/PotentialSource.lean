module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized

/-! # The three-term incoming potential density

This auxiliary expression names the exact A11p cancellation formula.
Its totalized axis value is distinct from the continuous derivative
representative used in the classical parameter-integral argument.
-/

public section

namespace EmcsfAcExtension.Local

/-- The A11p incoming derivative of the outgoing potential constraint,
with its geometric, charge-Hardy and incoming Maxwell-current terms.
This auxiliary formula is totalized at the axis. -/
@[expose] noncomputable def potentialIncomingSource (e : ℝ) (D : Set (ℝ × ℝ))
    (S : Fields) (u v : ℝ) : ℝ :=
  S.AV u v * geomN D S u v - 2 * S.nu u v / S.r u v * S.AV u v +
    2 * e * S.nu u v ^ 2 * S.lam u v / ((1 - S.mu u v) * S.r u v) *
      (starRingEnd ℂ (S.phi u v) * (S.xi u v / (S.nu u v : ℂ))).im

end EmcsfAcExtension.Local
