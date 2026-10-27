module

public import EmcsfAcExtension.Global.Closure.ConnectorExclusion
public import EmcsfAcExtension.Global.Closure.ConnectorGeometry
public import EmcsfAcExtension.Global.Closure.ConnectorClock
public import EmcsfAcExtension.Global.Closure.ConnectorEnergy

/-! # Terminal-row exclusion and the constant-label connector

The Root A stage induction can import this module for the terminal-row
exclusion consumers, the actual capped connector construction, its clock
and clipped-variation identities, and its energy recurrence and finite
iteration. The construction of compatible prefixes and the strict-stop
callback on restricted/reappended cutoffs belong to the stage induction.
Source: `charged_SF_new_version.tex:L3905–L3923`, `charged_SF_new_version.tex:L4074–L4106`.
-/

public section
