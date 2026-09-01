module DASHI.Governance.DrugCategoryConsumerRelativeInverseCompositionExact where

open import DASHI.Core.Prelude

import DASHI.Governance.ContestedDrugCategoryAtlasBidiExact as Atlas
import DASHI.Governance.DrugCategoryPartialTranslationPathCategoryExact as Path
import DASHI.Governance.DrugCategoryConsumerIndexedTranslationAdmissionExact as Admission
import DASHI.Governance.DrugCategoryConsumerRelativeQuotientInverseExact as Inverse

------------------------------------------------------------------------
-- COMPOSITION OF CONSUMER-RELATIVE QUOTIENT INVERSES
--
-- Groupoid-like behaviour is admitted only on a declared consumer quotient.
-- If a required coordinate is preserved on p and q, it is preserved on p;q.
-- This does not create an inverse for coordinates erased by either segment.
------------------------------------------------------------------------

coordinatePreservedAppend :
  ∀ {a b c coordinate}
    {first : Path.TranslationPath a b}
    {second : Path.TranslationPath b c} →
  Path.CoordinatePreserved first coordinate →
  Path.CoordinatePreserved second coordinate →
  Path.CoordinatePreserved (Path.appendPath first second) coordinate
coordinatePreservedAppend Path.preservedId secondPreserved = secondPreserved
coordinatePreservedAppend
  (Path.preservedStep firstPreserved restPreserved)
  secondPreserved =
  Path.preservedStep
    firstPreserved
    (coordinatePreservedAppend restPreserved secondPreserved)

consumerPathSafetyComposes :
  ∀ {a b c consumer}
    {first : Path.TranslationPath a b}
    {second : Path.TranslationPath b c} →
  Admission.ConsumerPathSafe consumer first →
  Admission.ConsumerPathSafe consumer second →
  Admission.ConsumerPathSafe consumer (Path.appendPath first second)
consumerPathSafetyComposes firstSafe secondSafe requirement =
  coordinatePreservedAppend
    (firstSafe requirement)
    (secondSafe requirement)

consumerRelativeQuotientInverseComposes :
  ∀ {a b c consumer}
    {first : Path.TranslationPath a b}
    {second : Path.TranslationPath b c} →
  Inverse.ConsumerRelativeQuotientInverse consumer first →
  Inverse.ConsumerRelativeQuotientInverse consumer second →
  Inverse.ConsumerRelativeQuotientInverse
    consumer (Path.appendPath first second)
consumerRelativeQuotientInverseComposes firstInverse secondInverse =
  Inverse.consumerSafePathCreatesQuotientInverse
    (consumerPathSafetyComposes
      (Inverse.quotientInverseCreatesConsumerSafety firstInverse)
      (Inverse.quotientInverseCreatesConsumerSafety secondInverse))

------------------------------------------------------------------------
-- Canonical factorisation of the state -> clinical -> lived clinical quotient.
------------------------------------------------------------------------

stateClinicalPath :
  Path.TranslationPath Atlas.stateLegalChart Atlas.biomedicalChart
stateClinicalPath = Path.pathStep Path.stateClinicalLeg Path.pathId

clinicalLivedPath :
  Path.TranslationPath Atlas.biomedicalChart Atlas.livedSubjectChart
clinicalLivedPath = Path.pathStep Path.clinicalLivedLeg Path.pathId

stateClinicalClinicalSafe :
  Admission.ConsumerPathSafe Admission.clinicalSafetyConsumer stateClinicalPath
stateClinicalClinicalSafe Admission.clinicalRequiresClinicalFact =
  Path.preservedStep refl Path.preservedId

clinicalLivedClinicalSafe :
  Admission.ConsumerPathSafe Admission.clinicalSafetyConsumer clinicalLivedPath
clinicalLivedClinicalSafe Admission.clinicalRequiresClinicalFact =
  Path.preservedStep refl Path.preservedId

stateClinicalClinicalInverse :
  Inverse.ConsumerRelativeQuotientInverse
    Admission.clinicalSafetyConsumer stateClinicalPath
stateClinicalClinicalInverse =
  Inverse.consumerSafePathCreatesQuotientInverse stateClinicalClinicalSafe

clinicalLivedClinicalInverse :
  Inverse.ConsumerRelativeQuotientInverse
    Admission.clinicalSafetyConsumer clinicalLivedPath
clinicalLivedClinicalInverse =
  Inverse.consumerSafePathCreatesQuotientInverse clinicalLivedClinicalSafe

composedClinicalInverse :
  Inverse.ConsumerRelativeQuotientInverse
    Admission.clinicalSafetyConsumer
    (Path.appendPath stateClinicalPath clinicalLivedPath)
composedClinicalInverse =
  consumerRelativeQuotientInverseComposes
    stateClinicalClinicalInverse clinicalLivedClinicalInverse

composedClinicalPathIsCanonical :
  Path.appendPath stateClinicalPath clinicalLivedPath
  ≡ Path.stateClinicalLivedPath
composedClinicalPathIsCanonical = refl

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data ConsumerInverseCompositionPromotesGlobalGroupoid : Set where

data ClinicalCompositionPromotesSubjectInverse : Set where

data SegmentSafetyPromotesUnrequiredCoordinateSafety : Set where

consumerInverseCompositionDoesNotPromoteGlobalGroupoid :
  ConsumerInverseCompositionPromotesGlobalGroupoid → ⊥
consumerInverseCompositionDoesNotPromoteGlobalGroupoid ()

clinicalCompositionDoesNotPromoteSubjectInverse :
  ClinicalCompositionPromotesSubjectInverse → ⊥
clinicalCompositionDoesNotPromoteSubjectInverse ()

segmentSafetyDoesNotPromoteUnrequiredCoordinateSafety :
  SegmentSafetyPromotesUnrequiredCoordinateSafety → ⊥
segmentSafetyDoesNotPromoteUnrequiredCoordinateSafety ()

record ConsumerRelativeInverseCompositionBoundary : Set where
  constructor consumerRelativeInverseCompositionBoundary
  field
    consumerSafePathsCompose : Bool
    consumerSafePathsComposeIsTrue : consumerSafePathsCompose ≡ true
    quotientInversesComposeOnSameConsumer : Bool
    quotientInversesComposeOnSameConsumerIsTrue :
      quotientInversesComposeOnSameConsumer ≡ true
    clinicalQuotientCompositionCreatesGlobalSemanticGroupoid : Bool
    clinicalQuotientCompositionCreatesGlobalSemanticGroupoidIsFalse :
      clinicalQuotientCompositionCreatesGlobalSemanticGroupoid ≡ false
    compositionRecoversErasedSubjectHistory : Bool
    compositionRecoversErasedSubjectHistoryIsFalse :
      compositionRecoversErasedSubjectHistory ≡ false

canonicalConsumerRelativeInverseCompositionBoundary :
  ConsumerRelativeInverseCompositionBoundary
canonicalConsumerRelativeInverseCompositionBoundary =
  consumerRelativeInverseCompositionBoundary
    true refl
    true refl
    false refl
    false refl
