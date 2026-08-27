module DASHI.Physics.Closure.Everything where

-- Authoritative closure / Clay-facing rollup.
-- New NS/YM closure surfaces should be wired here (or into a narrower
-- subfolder Everything) before being promoted into DASHI.Physics.Everything.

import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface

-- Current Navier--Stokes terminal and critical-path surfaces.
import DASHI.Physics.Closure.NSFinalStateReceipt
import DASHI.Physics.Closure.NSFastestClayPathReceipt
import DASHI.Physics.Closure.NSPaper1ClayTargetReceipt
import DASHI.Physics.Closure.NSGlobalH118BoundReceipt
import DASHI.Physics.Closure.NSW4WeakSolutionReceipt

-- Reusable exact NS kernels consumed by the terminal surfaces.
import DASHI.Physics.Closure.NSPeriodicConcreteNorms
import DASHI.Physics.Closure.NSCrossShellSchurBound
import DASHI.Physics.Closure.NSFactorizedSchurFrameGap
import DASHI.Physics.Closure.NSTriadKNCarrierCoverage
import DASHI.Physics.Closure.NSTriadKNBKMContinuation
import DASHI.Physics.Closure.NSTriadKNLuoScalingExact
import DASHI.Physics.Closure.NSTriadKNResonantNullGain

-- TOE integration: native SSP/369 symmetry action, equivariant two-sheet
-- reduction, residual-bearing 9 -> 6 reopening, and NS 3 x 3 nonary chart.
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

-- Coupled-trajectory/Feynman/Kelvin cross-pollination: finite histories,
-- path fibres, stationary coherence classification, wavelength/source-scale
-- conditioning, context-dependent weighting, TSFV invariant boundary, and
-- source-bounded experimental support.
import DASHI.Physics.Closure.FeynmanKelvinTrajectoryCrossPollinationExact
import DASHI.Physics.Closure.ApertureWakeModeSelectionBridgeExact
import DASHI.Physics.Closure.TSFVBidirectionalCausticBridgeExact
import DASHI.Physics.Closure.TSFVHistoryConditionedChoiceBridgeExact
import DASHI.Physics.Closure.SinglePhotonRecoilRelationalObserverBridgeExact
import DASHI.Physics.Closure.TSFVLocalActionCandidateAuditExact
