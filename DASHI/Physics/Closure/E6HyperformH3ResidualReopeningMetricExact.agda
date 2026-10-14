module DASHI.Physics.Closure.E6HyperformH3ResidualReopeningMetricExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformH3PhaseMetricLiftExact as PhaseLift
import DASHI.Physics.Closure.E6HyperformH3SameObjectEmbeddingExact as H3

------------------------------------------------------------------------
-- H3 RESIDUAL / REOPENING INTERPRETATION OF THE PHASE METRIC TERM
--
-- On the selected local H3 chart the intrinsic quadratic source is
--
--   q(x,y,z) = (x+z)^2 + y^2,
--
-- with radical r=(1,0,-1). Hence q(v+t r)=q(v): the source is blind to one
-- ternary direction and factors through a 9-state quotient.
--
-- The additional linear coordinate
--
--   ell(x,y,z)=x-z
--
-- satisfies ell(r)=2 != 0. Therefore every v has the unique split
--
--   t = 2 ell(v),
--   k = v - t r,
--   ell(k)=0,
--   v = k + t r.
--
-- The executable producer checks this on all 27 points. Thus the same phase
-- coordinate whose square resolves the local metric radical is also exactly a
-- residual/reopening coordinate for the information discarded by the coarse
-- quadratic observer. This is a local same-object theorem shape; it does not
-- identify the residual with the separate 3-H3-patch fibre or E8/zeta phase.
------------------------------------------------------------------------

localCarrierCount : Nat
localCarrierCount = 27

phaseKernelCount : Nat
phaseKernelCount = 9

phaseValueCount : Nat
phaseValueCount = 3

radicalCoordinate : String
radicalCoordinate = "r=(1,0,2) mod 3"

phaseCoordinate : String
phaseCoordinate = "ell=(1,0,2); ell(v)=x-z mod 3"

splitFormula : String
splitFormula = "t=2*ell(v); k=v-t*r; ell(k)=0; v=k+t*r"

record H3ResidualReopeningLocalReceipt : Set where
  constructor h3-residual-reopening-local-receipt
  field
    sameSelectedH3CarrierUsed : Bool
    quadraticSourceConstantAlongRadical : Bool
    coarseQuadraticObserverLosesRadicalCoordinate : Bool
    phaseKernelHasNineStates : Bool
    phaseHasThreeValues : Bool
    phaseNonzeroOnRadical : Bool
    splitFormulaCheckedAll27States : Bool
    reopeningRoundtripCheckedAll27States : Bool
    kernelTimesPhaseHas27States : Bool
    phaseIsExactResidualForSelectedSplit : Bool
    phaseSquareIsSameRadicalResolvingMetricTerm : Bool
    localResidualInterpretationPaid : Bool
    globalLeastSufficientObserverPaid : Bool
    threeH3PatchFibreIdentityPaid : Bool
    e8ZetaPhaseIdentityPaid : Bool
    physicalThirdSpatialDirectionPaid : Bool
    boundary : String
open H3ResidualReopeningLocalReceipt public

canonicalH3ResidualReopeningLocalReceipt : H3ResidualReopeningLocalReceipt
canonicalH3ResidualReopeningLocalReceipt =
  h3-residual-reopening-local-receipt
    true true true true true true true true true true true true
    false false false false
    "The local H3 quadratic observer forgets exactly one ternary radical coordinate. The covector ell=x-z reopens that coordinate on every one of the 27 local states and the same ell^T ell term makes the local metric nondegenerate. This pays a local residual/reopening interpretation of the added metric datum. It does not yet prove global least-sufficient-observer status, identity with the separate three-patch A2^3 fibre, identity with the E8/zeta phase, or a physical continuum spatial direction."

phaseMetricReceipt : PhaseLift.H3PhaseMetricLiftLocalReceipt
phaseMetricReceipt = PhaseLift.canonicalH3PhaseMetricLiftLocalReceipt

data LocalReopeningCreatesGlobalPhysicalDirection : Set where

localReopeningDoesNotCreatePhysicalDirection :
  LocalReopeningCreatesGlobalPhysicalDirection → {A : Set} → A
localReopeningDoesNotCreatePhysicalDirection ()
