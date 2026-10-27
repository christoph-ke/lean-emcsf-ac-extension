module

public import EmcsfAcExtension.Global.Exterior.OpticsCoefficients
public import EmcsfAcExtension.Global.Exterior.OpticsPast
public import EmcsfAcExtension.Global.Exterior.OpticalTails
public import EmcsfAcExtension.Global.Exterior.OpticalLimits
public import EmcsfAcExtension.Global.Exterior.OpticsFrontier
public import EmcsfAcExtension.Global.Exterior.OpticsSpeed
public import EmcsfAcExtension.Global.Exterior.OpticsInverse
public import EmcsfAcExtension.Global.Exterior.OpticsTerminal

/-! # Adaptive exterior optics and frontier

Public entry point for the optical coefficients, incoming-past invariance,
nonnegative optical tails, uniform limits and actual adaptive-frontier speed.
The split files keep every module below the packet's 600-line bound.
-/
