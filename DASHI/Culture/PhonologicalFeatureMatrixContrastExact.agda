module DASHI.Culture.PhonologicalFeatureMatrixContrastExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Culture.IPAPhoneticFeatureLatticeExact as IPA

------------------------------------------------------------------------
-- PHONOLOGICAL FEATURE MATRIX / LANGUAGE-RELATIVE CONTRAST
--
-- Open teaching/source cross-check:
-- Catherine Anderson et al., Essentials of Linguistics, phonetics/phonology
-- chapters on feature matrices, phonemes, contrastive distribution and
-- minimal pairs. Feature matrices describe segment properties; phonemic
-- status is language-relative and requires contrast/distribution evidence.
--
-- This owner complements, rather than replaces, the official IPA phonetic
-- lattice. IPA feature location != language phoneme inventory.
------------------------------------------------------------------------

data FeaturePolarity : Set where
  plus minus unspecified : FeaturePolarity

record DistinctiveFeature : Set where
  constructor distinctive-feature
  field
    featureName : String
    polarity : FeaturePolarity
    sourceReference : String
open DistinctiveFeature public

record SegmentFeatureMatrix : Set where
  constructor segment-feature-matrix
  field
    segmentSymbol : String
    phoneticReference : String
    featureSetReference : String
    voiceFeature : FeaturePolarity
    continuantFeature : FeaturePolarity
    nasalFeature : FeaturePolarity
    sonorantFeature : FeaturePolarity
    placeFeature : String
    mannerFeature : String
    matrixRevision : String
open SegmentFeatureMatrix public

record LanguageContrastContext : Set where
  constructor language-contrast-context
  field
    languageOrVariety : String
    communityOrCorpusReference : String
    corpusRevision : String
    analysisRevision : String
open LanguageContrastContext public

data DistributionRelation : Set where
  contrastiveDistribution complementaryDistribution freeVariation unresolvedDistribution : DistributionRelation

record PhonePairContrastReceipt : Set where
  constructor phone-pair-contrast-receipt
  field
    context : LanguageContrastContext
    phoneA : SegmentFeatureMatrix
    phoneB : SegmentFeatureMatrix
    distribution : DistributionRelation
    minimalPairReference : String
    nearMinimalPairReference : String
    environmentEvidenceReference : String
    meaningContrastReference : String
    phonemeA : String
    phonemeB : String
    distinctPhonemesPaid : Bool
    samePhonemePaid : Bool
open PhonePairContrastReceipt public

record LanguagePhonemeInventoryReceipt : Set where
  constructor language-phoneme-inventory-receipt
  field
    context : LanguageContrastContext
    phoneInventoryReference : String
    contrastLedgerReference : String
    allophoneLedgerReference : String
    phonemeInventoryReference : String
    inventoryCoverageReference : String
    sourceProvenance : String
    completeForDeclaredCoverage : Bool
open LanguagePhonemeInventoryReceipt public

------------------------------------------------------------------------
-- Status after the Ibrahim sibling traversal:
-- architecture is paid, but no concrete language inventory is promoted merely
-- by owning IPA or feature-matrix machinery.
------------------------------------------------------------------------

record PhonologyProducerFrontier : Set where
  constructor phonology-producer-frontier
  field
    featureMatrixArchitecturePaid : Bool
    contrastReceiptShapePaid : Bool
    languageInventoryReceiptShapePaid : Bool
    concreteLanguageContrastPaid : Bool
    concreteLanguageInventoryPaid : Bool
    architectureStillMissing : Bool
open PhonologyProducerFrontier public

currentPhonologyFrontier : PhonologyProducerFrontier
currentPhonologyFrontier =
  phonology-producer-frontier true true true false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FeatureDifferenceCreatesPhonemicContrast : Set where
data IPAInventoryCreatesLanguageInventory : Set where
data MinimalPairInOneLanguageTransfersToAnother : Set where
data OrthographyCreatesPhonologicalContrast : Set where

aFeatureDifferenceIsNotAutomaticallyPhonemic : FeatureDifferenceCreatesPhonemicContrast → ⊥
aFeatureDifferenceIsNotAutomaticallyPhonemic ()

ipaDoesNotCreateLanguageInventory : IPAInventoryCreatesLanguageInventory → ⊥
ipaDoesNotCreateLanguageInventory ()

contrastDoesNotTransferAcrossLanguages : MinimalPairInOneLanguageTransfersToAnother → ⊥
contrastDoesNotTransferAcrossLanguages ()

orthographyDoesNotCreateContrast : OrthographyCreatesPhonologicalContrast → ⊥
orthographyDoesNotCreateContrast ()

record PhonologicalFeatureMatrixBoundary : Set where
  constructor phonological-feature-matrix-boundary
  field
    phoneticAndPhonologicalLayersSeparate : Bool
    featureMatricesReusableAcrossAnalyses : Bool
    phonemeStatusLanguageIndexed : Bool
    minimalPairEvidenceExplicit : Bool
    ipaChartDefinesLanguageInventory : Bool
open PhonologicalFeatureMatrixBoundary public

canonicalPhonologicalFeatureMatrixBoundary : PhonologicalFeatureMatrixBoundary
canonicalPhonologicalFeatureMatrixBoundary =
  phonological-feature-matrix-boundary true true true true false
