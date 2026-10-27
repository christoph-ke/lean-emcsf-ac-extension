module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
public import EmcsfAcExtension.Local.Limit.Inputs
import EmcsfAcExtension.Local.Apriori.SmoothSupContinuation
import EmcsfAcExtension.Local.Construction.WireWhole

/-! # Unconditional whole-triangle C¹ existence

The landed C¹ a priori estimate discharges the last continuation input.
The Picard and system-recovery inputs were discharged in `WireWhole`.
-/

public section

namespace EmcsfAcExtension.Local

/-- The common C¹ continuation bound, supplied by the a priori estimate.
The positive thresholds are universal; the bound may depend on `T,e,h`
and is uniform in every positive constructed apex and every solution. -/
theorem continuation_c1_bound_input : ContinuationC1BoundInput :=
  Null.smooth_c1_bound

/-- [node restart-sec-independent-null-construction#whole-triangle-smooth-existence]
The C¹ whole-triangle existence contract, with every continuation input
discharged. The positive thresholds are universal, before time, coupling
and datum; the solution includes the terminal edge and apex. -/
theorem whole_triangle_existence : WholeTriangleExistenceStmt :=
  whole_triangle_existence_of_c1_bound continuation_c1_bound_input

end EmcsfAcExtension.Local
