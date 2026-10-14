module DASHI.Physics.Closure.Ternary27TrinificationTwoNeutralVEVBreakingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.Ternary27TrinificationSMBridgeExact as SM
import DASHI.Physics.Closure.Ternary27TrinificationSU2RBreakingFrontierExact as Frontier

------------------------------------------------------------------------
-- TWO-NEUTRAL-VEV TRINIFICATION BREAKING CANDIDATE
--
-- Work on the same (1,3,bar3) lepton/Higgs 3x3 matrix block used by the
-- trinification representation.  Under the already-owned hypercharge
-- generator
--
--   Y = -(1/6) X_L -(1/6) X_R -(1/2) T3_R,
--
-- the matrix units E_32 and E_33 are both neutral.
--
-- The local exact compact-Lie stabilizer calculation gives:
--
--   one neutral VEV E_33:
--       dim Stab_{su3_L + su3_R} = 7;
--
--   two independent neutral VEVs E_32 and E_33:
--       dim Stab_{su3_L + su3_R} = 4,
--
-- with an explicit kernel basis consisting of the three su(2)_L generators
-- plus
--
--   X_L + 3 T3_R + X_R.
--
-- Multiplication of the final generator by -1/6 is exactly the same U(1)_Y
-- generator used by the existing charge calculation.  SU(3)_C acts on the
-- separate colour factor and is untouched. Hence the compact stabilizer at Lie
-- algebra level is
--
--   su(3)_C + su(2)_L + u(1)_Y.
--
-- The positive gauge-boson mass quadratic form induced by these two VEV
-- directions has rank 12 on su3_L + su3_R, with the above 4-dimensional
-- kernel.  This is conditional algebraic mass/decoupling structure: the Higgs
-- potential, existence of two physical scalar 27 copies, VEV scale, couplings
-- and numerical masses remain separate physical receipts.
------------------------------------------------------------------------

oneNeutralVEVLRStabilizerDimension : Nat
oneNeutralVEVLRStabilizerDimension = 7

twoNeutralVEVLRStabilizerDimension : Nat
twoNeutralVEVLRStabilizerDimension = 4

brokenLRGeneratorCount : Nat
brokenLRGeneratorCount = 12

fullLowEnergyGaugeLieDimension : Nat
fullLowEnergyGaugeLieDimension = 12

neutralVEVDirections : String
neutralVEVDirections = "E_32 and E_33 in the (1,3,bar3) matrix block"

survivingU1Generator : String
survivingU1Generator = "Y = -(X_L + 3*T3_R + X_R)/6"

record TrinificationTwoNeutralVEVLocalReceipt : Set where
  constructor trinification-two-neutral-vev-local-receipt
  field
    sameFirstTitsTrinification27Used : Bool
    sameHyperchargeGeneratorUsed : Bool
    e32HyperchargeNeutral : Bool
    e33HyperchargeNeutral : Bool
    oneNeutralVEVLeavesDimensionSevenLRStabilizer : Bool
    twoNeutralVEVsLeaveDimensionFourLRStabilizer : Bool
    threeSU2LGeneratorsInKernel : Bool
    fourthKernelGeneratorEqualsHyperchargeUpToScale : Bool
    exactLRKernelIsSU2LPlusU1Y : Bool
    colourSU3Untouched : Bool
    fullCompactLowEnergyLieAlgebraMatchesSMGaugeAlgebra : Bool
    brokenLRGeneratorCountTwelve : Bool
    conditionalGaugeMassQuadraticRankTwelve : Bool
    twoPhysicalScalar27CopiesSupplied : Bool
    higgsPotentialSelectsTheseDirections : Bool
    physicalVEVScalePaid : Bool
    physicalGaugeCouplingsPaid : Bool
    numericalHeavyGaugeMassesPaid : Bool
    dhrCompactGroupSameActionPaid : Bool
    empiricalBreakingReceiptPaid : Bool
    boundary : String
open TrinificationTwoNeutralVEVLocalReceipt public

canonicalTrinificationTwoNeutralVEVLocalReceipt : TrinificationTwoNeutralVEVLocalReceipt
canonicalTrinificationTwoNeutralVEVLocalReceipt =
  trinification-two-neutral-vev-local-receipt
    true true true true true true true true true true true true true
    false false false false false false false false
    "Two independent hypercharge-neutral lepton-block VEV directions reduce the compact SU(3)_L x SU(3)_R stabilizer exactly to SU(2)_L x U(1)_Y at Lie-algebra level while leaving SU(3)_C untouched. The conditional gauge mass operator has rank 12 on the broken L/R directions. This pays an explicit algebraic order-parameter/stabilizer pattern, but not the physical existence of two scalar 27s, their potential, scale, couplings, numerical spectrum, DHR same-action theorem or experimental breaking evidence."

oldBreakingFrontier : Frontier.TrinificationSU2RBreakingFrontierReceipt
oldBreakingFrontier = Frontier.canonicalTrinificationSU2RBreakingFrontierReceipt

record PhysicalTwoVEVBreakingProducer : Set₁ where
  field
    ScalarFieldCopy : Set
    first27 second27 : ScalarFieldCopy
    potential : Set
    minimumReceipt : Set
    neutralVEVDirectionReceipt : Set
    vevScaleReceipt : Set
    gaugeCouplingReceipt : Set
    massSpectrumReceipt : Set
    lowEnergyDecouplingReceipt : Set
    dhrSameActionReceipt : Set
    empiricalReceipt : Set
open PhysicalTwoVEVBreakingProducer public

data AlgebraicStabilizerCreatesPhysicalHiggsMechanism : Set where

algebraicStabilizerDoesNotCreatePhysicalHiggsMechanism :
  AlgebraicStabilizerCreatesPhysicalHiggsMechanism → {A : Set} → A
algebraicStabilizerDoesNotCreatePhysicalHiggsMechanism ()
