module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
public import EmcsfAcExtension.Local.Limit.Inputs
import EmcsfAcExtension.Local.Construction.WireOriginal
import EmcsfAcExtension.Local.Construction.WireShort
import EmcsfAcExtension.Local.Construction.WireRecovery
import EmcsfAcExtension.Local.Construction.Whole

/-! # Whole-triangle existence with the Picard and recovery inputs discharged

The three landed construction producers supply the original ball, the
uniform short-cone solution and C¹ system recovery. The common C¹ a priori
bound is the sole remaining producer premise.
-/

public section

namespace EmcsfAcExtension.Local

/-- [internal]
The C¹ whole-triangle existence contract of internal project record, conditional only on the
pending internal project record C¹ bound. All Picard and recovery inputs are discharged.
Both positive smallness thresholds are universal, before time, coupling
and datum. The conclusion includes the terminal edge and apex. -/
theorem whole_triangle_existence_of_c1_bound (h4 : ContinuationC1BoundInput) :
    WholeTriangleExistenceStmt := by
  exact whole_triangle_solution_of_inputs continuation_original_picard_input
    continuation_short_picard_input continuation_recovery_input h4

end EmcsfAcExtension.Local
