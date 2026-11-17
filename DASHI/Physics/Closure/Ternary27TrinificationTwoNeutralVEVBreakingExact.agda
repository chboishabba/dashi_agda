module DASHI.Physics.Closure.Ternary27TrinificationTwoNeutralVEVBreakingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.Ternary27TrinificationSMBridgeExact as SM
import DASHI.Physics.Closure.Ternary27TrinificationSU2RBreakingFrontierExact as Frontier

------------------------------------------------------------------------
-- TWO-NEUTRAL-VEV TRINIFICATION BREAKING CANDIDATE
--
-- Work on the same (1,3,bar3) matrix block after selecting the trinification
-- subgroup. Under the already-owned hypercharge generator
--
--   Y = -(1/6) X_L -(1/6) X_R -(1/2) T3_R,
--
-- E_32 and E_33 are both neutral.  Inside su(3)_L + su(3)_R:
--
--   one VEV E_33 leaves dimension 7;
--   two VEVs E_32,E_33 leave dimension 4,
--
-- with kernel su(2)_L plus X_L + 3 T3_R + X_R, whose -1/6 multiple is the
-- same U(1)_Y generator. SU(3)_C is untouched, so AFTER the trinification stage
-- the surviving compact algebra is the SM gauge algebra.
--
-- Important correction: imposing only E_32,E_33 directly on the full literal
-- 78-dimensional first-Tits cubic-symmetry algebra leaves a 49-dimensional
-- infinitesimal stabilizer.  Therefore the two VEVs do NOT by themselves prove
-- E6 -> SM.  A prior E6 -> SU(3)^3 selection/breaking stage is required.
------------------------------------------------------------------------

oneNeutralVEVLRStabilizerDimension : Nat
oneNeutralVEVLRStabilizerDimension = 7

twoNeutralVEVLRStabilizerDimension : Nat
twoNeutralVEVLRStabilizerDimension = 4

brokenLRGeneratorCount : Nat
brokenLRGeneratorCount = 12

fullLowEnergyGaugeLieDimensionAfterTrinification : Nat
fullLowEnergyGaugeLieDimensionAfterTrinification = 12

directTwoVEVFullE6StabilizerDimension : Nat
directTwoVEVFullE6StabilizerDimension = 49

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
    fullCompactLowEnergyLieAlgebraMatchesSMGaugeAlgebraAfterTrinification : Bool
    brokenLRGeneratorCountTwelve : Bool
    conditionalGaugeMassQuadraticRankTwelve : Bool
    calculationRestrictedToSelectedTrinificationStage : Bool
    directFullE6TwoVEVStabilizerDimension49PaidLocally : Bool
    directFullE6TwoVEVStabilizerEqualsSMGaugeAlgebra : Bool
    priorE6ToTrinificationStageRequired : Bool
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
    true true false true
    false false false false false false false false
    "Within the already-selected trinification subgroup, E_32,E_33 reduce SU(3)_L x SU(3)_R exactly to SU(2)_L x U(1)_Y and leave colour untouched. The full first-Tits E6 test instead leaves a 49-dimensional stabilizer, so the two VEVs are not a direct E6->SM mechanism. They constitute the second stage E6 -> trinification -> SM. Physical scalar content, potential choice, scale, couplings, DHR same-action and empirical breaking remain separate."

oldBreakingFrontier : Frontier.TrinificationSU2RBreakingFrontierReceipt
oldBreakingFrontier = Frontier.canonicalTrinificationSU2RBreakingFrontierReceipt

record PhysicalTwoVEVBreakingProducer : Set₁ where
  field
    ScalarFieldCopy : Set
    first27 second27 : ScalarFieldCopy
    priorE6ToTrinificationReceipt : Set
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

data TrinificationStabilizerCreatesDirectE6Breaking : Set where

algebraicStabilizerDoesNotCreatePhysicalHiggsMechanism :
  AlgebraicStabilizerCreatesPhysicalHiggsMechanism → {A : Set} → A
algebraicStabilizerDoesNotCreatePhysicalHiggsMechanism ()

trinificationResultDoesNotCreateDirectE6Breaking :
  TrinificationStabilizerCreatesDirectE6Breaking → {A : Set} → A
trinificationResultDoesNotCreateDirectE6Breaking ()
