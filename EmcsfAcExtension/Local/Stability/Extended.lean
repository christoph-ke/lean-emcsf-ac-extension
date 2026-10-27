module

public import EmcsfAcExtension.Local.Stability.W11Algebra
public import EmcsfAcExtension.Local.Stability.W11
public import EmcsfAcExtension.Local.Stability.W11Nonconcentration
public import EmcsfAcExtension.Local.Stability.W11FluxStrong
public import EmcsfAcExtension.Local.Stability.GeomStrongInitial
public import EmcsfAcExtension.Local.Stability.GeomStrong
public import EmcsfAcExtension.Local.Stability.GeomStrongEnvelopeMain
public import EmcsfAcExtension.Local.Stability.GeomStrongPureLimit
public import EmcsfAcExtension.Local.Stability.GeomStrongAC
public import EmcsfAcExtension.Local.Stability.GeomStrongMassOut
public import EmcsfAcExtension.Local.Stability.GeomStrongMassIn
public import EmcsfAcExtension.Local.Stability.GeomStrongCrossLimit
public import EmcsfAcExtension.Local.Stability.GeomStrongMassDerivatives
public import EmcsfAcExtension.Local.Stability.PotentialHardy
public import EmcsfAcExtension.Local.Stability.PotentialTriangle
public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Stability.PotentialStrong
public import EmcsfAcExtension.Local.Stability.ExtendedMain

public import EmcsfAcExtension.Local.Stability.ExtendedLipschitz
public import EmcsfAcExtension.Local.Stability.ExtendedNodes
public import EmcsfAcExtension.Local.Stability.ExtendedLimits
public import EmcsfAcExtension.Local.Stability.ExtendedNonconcentration

/-! # Strong smooth stability and the complete extended record

The scalar, geometric, mass and electromagnetic comparison lemmas,
complete-section strong limits, nonconcentration and every internal project record
extended-record clause are gathered here. The four full general-AC
exports remain downstream in internal project record, exactly as internal project record requires.
The unconditional exports discharge the local helpers with the proved
main Lipschitz theorem and supply the full `stab_extended` record.
-/

public section
