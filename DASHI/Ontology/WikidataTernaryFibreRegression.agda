module DASHI.Ontology.WikidataTernaryFibreRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernaryOppositionEvidenceBridgeExact as Opposition
import DASHI.Cognition.PNF.BinaryBalancedTernaryAggregateLossExact as BinaryAggregate
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.TopDownObservationCalculusExact as TopDown
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.BalancedTernaryAntipodalResidualCodecExact as Codec
import DASHI.Foundations.BalancedTernaryDependentRecoverableBridgeExact as RecoverableBridge
import DASHI.Foundations.Base369InteractionAntipodalFibreExact as Interaction
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.TernaryNativeMinimalityExact as Native
import DASHI.Foundations.TernaryNineAntipodalD4SeparationExact as D4Sep
import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube
import DASHI.Ontology.DependentDefinitionFibreExact as Dependent

oneBitCannotReconstructSignedNeutralCoordinate :
  (observer : SSP.SSPTrit → Bool) → Native.Injective observer → ⊥
oneBitCannotReconstructSignedNeutralCoordinate = Native.noOneBitInjection

notPositiveStillDoesNotMeanStrictInverse :
  Native.positiveOnly SSP.sspNegOne ≡ Native.positiveOnly SSP.sspZero
notPositiveStillDoesNotMeanStrictInverse =
  Native.positiveOnlyCollapsesNegativeAndCentre

-- Top-down form of the same failure: the positive-only Boolean surface is not
-- sufficient for a consumer that needs the signed/neutral coordinate itself.
positiveOnlyIdentityNonDescent :
  Descent.ConsumerNonDescentWitness Native.positiveOnly (λ x → x)
positiveOnlyIdentityNonDescent =
  Descent.consumerNonDescentWitness
    SSP.sspNegOne SSP.sspZero
    Native.positiveOnlyCollapsesNegativeAndCentre
    Native.negativeNotZero

positiveOnlyCannotBeSufficientForSignedIdentity :
  Descent.ConsumerSufficient Native.positiveOnly (λ x → x) → ⊥
positiveOnlyCannotBeSufficientForSignedIdentity =
  Descent.nonDescentWitnessBlocksSufficiency positiveOnlyIdentityNonDescent

binarySimulationStillRoundTrips :
  (x : SSP.SSPTrit) → Native.decodeBinary (Native.encodeBinary x) ≡ x
binarySimulationStillRoundTrips = Native.binarySimulationRoundTrip

binarySimulationStillPreservesStrictAntipode :
  (x : SSP.SSPTrit) →
  Native.encodeBinary (Orbit.strictAntipode x)
  ≡ Native.binaryAntipode (Native.encodeBinary x)
binarySimulationStillPreservesStrictAntipode =
  Native.binarySimulationPreservesAntipode

oneBlockQuotientPlusResidualRoundTrips :
  (triple : Orbit.TritTriple) → Codec.decode27 (Codec.encode27 triple) ≡ triple
oneBlockQuotientPlusResidualRoundTrips = Codec.decodeAfterEncode27

-- Conversely, the exact quotient + dependent residual code is sufficient even
-- for the identity consumer on the whole 27-state block, because it separates
-- the fine carrier exactly.
antipodalDependentCodeSufficientForFineIdentity :
  Descent.ConsumerSufficient
    (TopDown.dependentCodeObserver RecoverableBridge.canonicalAntipodalDependentProjection)
    (λ triple → triple)
antipodalDependentCodeSufficientForFineIdentity =
  TopDown.dependentCodeIsAdequateForEveryConsumer
    RecoverableBridge.canonicalAntipodalDependentProjection
    (λ triple → triple)

threeBlockQuotientPlusResidualRoundTrips :
  (state : Cube.OneRoundInteractionState) →
  Codec.decodeRound (Codec.encodeRound state) ≡ state
threeBlockQuotientPlusResidualRoundTrips = Codec.decodeAfterEncodeRound

repoNativeTwentySevenCubedStill19683 :
  Interaction.fineInteractionStateCount ≡ 19683
repoNativeTwentySevenCubedStill19683 = Interaction.fineInteractionStateCountIs19683

blockwiseOrientationBaseStill2744 :
  Interaction.blockOrientationClassCount ≡ 2744
blockwiseOrientationBaseStill2744 = Interaction.blockOrientationClassCountIs2744

allNoncentralResidualStillHasEightOrientations :
  Interaction.allThreeNoncentralOrientationFibreSize ≡ 8
allNoncentralResidualStillHasEightOrientations =
  Interaction.allThreeNoncentralOrientationFibreSizeIsEight

strictAntipodeStillNotLogicalNegationByShape :
  Opposition.BalancedTernaryOppositionEvidenceBoundary.strictAntipodeIsLogicalNegationByCarrierShape
    Opposition.canonicalBalancedTernaryOppositionEvidenceBoundary
  ≡ false
strictAntipodeStillNotLogicalNegationByShape = refl

fiveAntipodalClassesStillNotFiveD4IrrepSpecies :
  D4Sep.TernaryNineAntipodalD4Boundary.fiveAntipodalOrbitClassesAreFiveD4IrrepSpecies
    D4Sep.canonicalTernaryNineAntipodalD4Boundary
  ≡ false
fiveAntipodalClassesStillNotFiveD4IrrepSpecies = refl

binaryAggregateStillErasesDirectedDisagreement :
  BinaryAggregate.acceptCount
    (BinaryAggregate.binaryProjectPositiveOnly BinaryAggregate.forwardDisagreement)
  ≡ BinaryAggregate.acceptCount
    (BinaryAggregate.binaryProjectPositiveOnly BinaryAggregate.reverseDisagreement)
binaryAggregateStillErasesDirectedDisagreement =
  BinaryAggregate.aggregateErasesDisagreementDirection

flatPositiveProductStillAdmitsInvalidCombination :
  Dependent.validFlat Dependent.flatToyotaFiestaExists ≡ false
flatPositiveProductStillAdmitsInvalidCombination =
  Dependent.flatToyotaFiestaNeedsPostHocRejection

dependentCarrierStillContainsOnlyValidCombinations :
  (vehicle : Dependent.Vehicle) →
  Dependent.validFlat (Dependent.flattenVehicle vehicle) ≡ true
dependentCarrierStillContainsOnlyValidCombinations =
  Dependent.dependentCarrierOnlyFlattensToValidCombinations
