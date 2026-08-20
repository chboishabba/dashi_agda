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
