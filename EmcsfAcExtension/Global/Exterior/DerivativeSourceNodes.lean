module

public import EmcsfAcExtension.Global.Exterior.DerivativeSource
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceTerminal
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceAggregateTerminal

/-! # Canonical names for the exterior equation nodes

Source labels without a parent `#` live directly under `Global`, as
specified in the Root A architecture's node naming table. These aliases
preserve the exact proved types of the exterior implementations.
-/

public section

namespace EmcsfAcExtension.Global

/-- [node eq:charged-exterior-derivative]
Canonical name for the exact incoming AC transport and derivative equation
of the prescribed outgoing density. There are no estimate constants or
terminal assumptions. Source: `charged_SF_new_version.tex:L1260–L1272`. -/
alias charged_exterior_derivative := Exterior.charged_exterior_derivative

/-- [internal]
Canonical terminal consumer of the literal source integral estimate.
The coefficient `4096` is numerical and uniform in all late rows and
outgoing exterior intervals. Source: `charged_SF_new_version.tex:L1298–L1325`. -/
alias charged_exterior_source_bound_of_terminal :=
  Exterior.charged_exterior_source_bound_of_terminal

end EmcsfAcExtension.Global
