module DASHI.Physics.Closure.NSTriadKNDefectMeasureAdjointComRound40Validation where

-- Round 40 is stacked on the complete Round-39 validation root.  It tests the
-- post-Round-39 highest-alpha hypotheses rather than opening another generic
-- abstraction lane: a single energy-weighted directional defect for HH-good
-- and HH-bad, exact symbolic threshold optimization, shell-dependent threshold
-- diagnostics, PV cancellation before residual scalarization, finite
-- shell-kernel Cauchy with a uniform periodized L1 constant, literal modal
-- skew-adjoint transport coefficients, the resulting one-channel Com collapse,
-- and exact Farkas-certificate sensitivity.

open import DASHI.Physics.Closure.NSTriadKNPeriodicPVOddComF4Round39Validation

open import DASHI.Physics.Closure.NSTriadKNHHUnifiedDirectionalDefectRound40Exact
open import DASHI.Physics.Closure.NSTriadKNHHBadDefectMeasureGainRound40Exact
open import DASHI.Physics.Closure.NSTriadKNHHAnalyticThresholdOptimizerRound40Exact
open import DASHI.Physics.Closure.NSTriadKNHHSquaredThresholdRepresentationRound40Exact
open import DASHI.Physics.Closure.NSTriadKNHHScaleDependentThresholdRound40Exact
open import DASHI.Physics.Closure.NSTriadKNHHGoodPVResidualOrderRound40Exact
open import DASHI.Physics.Closure.NSTriadKNHHGoodFiniteKernelCauchyRound40Exact
open import DASHI.Physics.Closure.NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact
open import DASHI.Physics.Closure.NSTriadKNPhysicalTransportCoefficientSkewRound40Exact
open import DASHI.Physics.Closure.NSTriadKNComAdjointCollapseRound40Exact
open import DASHI.Physics.Closure.NSTriadKNNineOwnerDualSensitivityRound40Exact
