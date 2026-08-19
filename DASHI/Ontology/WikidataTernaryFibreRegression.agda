module DASHI.Ontology.WikidataTernaryFibreRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernaryOppositionEvidenceBridgeExact as Opposition
import DASHI.Cognition.PNF.BinaryBalancedTernaryAggregateLossExact as BinaryAggregate
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.BalancedTernaryAntipodalResidualCodecExact as Codec
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
