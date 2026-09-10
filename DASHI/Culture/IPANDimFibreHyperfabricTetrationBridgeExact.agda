module DASHI.Culture.IPANDimFibreHyperfabricTetrationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Culture.IPAPhoneticFeatureLatticeExact as IPA
import DASHI.Culture.PhonologicalFeatureMatrixContrastExact as Phonology
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Biology.SelfIndexedParetoHyperfabricTetrationExact as Tetration
import DASHI.Cognition.RecursiveFibreTower as FibreTower

------------------------------------------------------------------------
-- IPA / N-DIMENSIONAL FIBRE / HYPERFABRIC / TETRATION CROSS-POLLINATION
--
-- The IPA chart is naturally read as a finite family of typed articulatory
-- coordinates.  A language phonology is not the whole chart: it is a
-- language-indexed admitted/contrastive fibre over phonetic possibilities.
-- An event/corpus analysis adds further observer/context/revision coordinates.
--
-- This is analogous to DASHI's N-dimensional hyperfabric principle that the
-- dimension belongs to the declared axis family, not to the number of
-- candidates or visual states.  It is NOT automatically tetration.  Tetration
-- only enters when the axis family itself is generated recursively, as in the
-- repo's self-indexed recurrence.
------------------------------------------------------------------------

data PhoneticAxisFamily : Set where
  consonantPlaceAxis : PhoneticAxisFamily
  consonantMannerAxis : PhoneticAxisFamily
  consonantVoicingAxis : PhoneticAxisFamily
  vowelHeightAxis : PhoneticAxisFamily
  vowelBacknessAxis : PhoneticAxisFamily
  vowelRoundingAxis : PhoneticAxisFamily
  secondaryLayerAxis : PhoneticAxisFamily
  languageContrastAxis : PhoneticAxisFamily
  corpusEventAxis : PhoneticAxisFamily
  provenanceRevisionAxis : PhoneticAxisFamily

axisReference : PhoneticAxisFamily → String
axisReference consonantPlaceAxis = "IPA.PlaceOfArticulation"
axisReference consonantMannerAxis = "IPA.MannerOfArticulation"
axisReference consonantVoicingAxis = "IPA.Voicing"
axisReference vowelHeightAxis = "IPA.VowelHeight"
axisReference vowelBacknessAxis = "IPA.VowelBackness"
axisReference vowelRoundingAxis = "IPA.Rounding"
axisReference secondaryLayerAxis = "IPA.SecondaryPhoneticLayer"
axisReference languageContrastAxis = "Phonology.LanguageContrastContext / PhonePairContrastReceipt"
axisReference corpusEventAxis = "IPA.EventPhoneticTranscriptionReceipt event coordinate"
axisReference provenanceRevisionAxis = "transcription/corpus/analysis revision and source coordinates"

record PhoneticHyperformalPoint : Set where
  constructor phonetic-hyperformal-point
  field
    symbolReference : String
    articulatoryReference : String
    acousticReference : String
    languageOrVarietyReference : String
    phonologicalContrastReference : String
    eventReference : String
    provenanceReference : String
    uncertaintyReference : String
open PhoneticHyperformalPoint public

record PhoneticFibreProjection : Set where
  constructor phonetic-fibre-projection
  field
    fullPointReference : String
    projectedAxisReference : String
    consumerReference : String
    omittedAxesReference : String
    projectionPaid : Bool
    omittedAxesAutomaticallyIrrelevant : Bool
open PhoneticFibreProjection public

record LanguagePhonologyFibre : Set where
  constructor language-phonology-fibre
  field
    languageOrVariety : String
    ipaPossibilitySpaceReference : String
    admittedPhoneInventoryReference : String
    contrastLedgerReference : String
    allophoneLedgerReference : String
    phonemeInventoryReference : String
    empiricalCoverageReference : String
    ipaChartEqualsLanguageInventory : Bool
open LanguagePhonologyFibre public

------------------------------------------------------------------------
-- Tetration boundary.
------------------------------------------------------------------------

record PhoneticRecursiveAxisGrowth : Set where
  constructor phonetic-recursive-axis-growth
  field
    level : Nat
    axisFamilyReference : String
    nextAxisFamilyGeneratedFromCurrentStates : Bool
    recursiveGenerationReceiptReference : String
    tetrationInterpretationAllowed : Bool
open PhoneticRecursiveAxisGrowth public

record IPANDimTetrationBoundary : Set where
  constructor ipa-ndim-tetration-boundary
  field
    ipaFeatureSpaceIsFiniteTypedProduct : Bool
    languagePhonologyIsConsumerIndexedFibre : Bool
    eventContextAddsIndependentAxes : Bool
    ndimAxisSemanticsRemainDeclared : Bool
    fixedFiniteFeatureProductIsTetration : Bool
    selfIndexedAxisGrowthMayBeTetrational : Bool
    phonemeInventoryCardinalityCreatesTetration : Bool
    projectionMakesOmittedAxesIrrelevant : Bool
    sameFeatureCoordinatesCreateSameSocialMeaning : Bool
open IPANDimTetrationBoundary public

canonicalIPANDimTetrationBoundary : IPANDimTetrationBoundary
canonicalIPANDimTetrationBoundary =
  ipa-ndim-tetration-boundary
    true true true true false true false false false

ipaBoundary : IPA.IPAPhoneticFeatureBoundary
ipaBoundary = IPA.canonicalIPAPhoneticFeatureBoundary

phonologyBoundary : Phonology.PhonologicalFeatureMatrixBoundary
phonologyBoundary = Phonology.canonicalPhonologicalFeatureMatrixBoundary

ndimBoundary : NDim.NDimParetoHyperfabricBoundary
ndimBoundary = NDim.canonicalNDimParetoHyperfabricBoundary

tetrationBoundary : Tetration.SelfIndexedParetoTetrationBoundary
tetrationBoundary = Tetration.canonicalSelfIndexedParetoTetrationBoundary

triadicTetrationLevelTwoStillTwentySeven :
  FibreTower.tetration 3 2 ≡ 27
triadicTetrationLevelTwoStillTwentySeven = FibreTower.triadicTetrationTwo

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data IPAChartEqualsPhonemeInventory : Set where
data FeatureProductCreatesTetration : Set where
data SameFeatureVectorCreatesSameMeaning : Set where
data ProjectionCreatesIrrelevance : Set where

data RecursiveGrowthCreatesEmpiricalPhonology : Set where

ipaChartDoesNotEqualLanguageInventory : IPAChartEqualsPhonemeInventory → ⊥
ipaChartDoesNotEqualLanguageInventory ()

finiteProductDoesNotCreateTetration : FeatureProductCreatesTetration → ⊥
finiteProductDoesNotCreateTetration ()

sameFeatureVectorDoesNotCreateSameMeaning : SameFeatureVectorCreatesSameMeaning → ⊥
sameFeatureVectorDoesNotCreateSameMeaning ()

projectionDoesNotEraseOmittedAxes : ProjectionCreatesIrrelevance → ⊥
projectionDoesNotEraseOmittedAxes ()

recursiveGrowthDoesNotCreateEmpiricalPhonology : RecursiveGrowthCreatesEmpiricalPhonology → ⊥
recursiveGrowthDoesNotCreateEmpiricalPhonology ()
