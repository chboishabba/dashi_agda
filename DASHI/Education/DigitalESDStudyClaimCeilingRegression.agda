module DASHI.Education.DigitalESDStudyClaimCeilingRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Biology.CausalEstimandStatisticalRealisationExact as Statistical
import DASHI.Biology.CausalEstimatorGuaranteesExact as Guarantees

studyClaimCoordinateCountRegression : Ceiling.studyClaimCoordinateCount ≡ 16
studyClaimCoordinateCountRegression = refl

designBoundaryReuseRegression :
  Ceiling.designBoundary ≡ Design.canonicalEvidenceDesignBoundary
designBoundaryReuseRegression = refl

implicationConeBoundaryReuseRegression :
  Ceiling.implicationConeBoundary ≡ Cone.canonicalExperimentalAssertionConeBoundary
implicationConeBoundaryReuseRegression = refl

statisticalBoundaryReuseRegression :
  Ceiling.statisticalBoundary ≡ Statistical.canonicalCausalEstimandStatisticalRealisationBoundary
statisticalBoundaryReuseRegression = refl

guaranteeBoundaryReuseRegression :
  Ceiling.guaranteeBoundary ≡ Guarantees.canonicalCausalEstimatorGuaranteeBoundary
guaranteeBoundaryReuseRegression = refl

attributedSourceRetainedRegression :
  Ceiling.StudyClaimCeilingBoundary.attributedSourceObjectRetained
    Ceiling.canonicalStudyClaimCeilingBoundary
  ≡ true
attributedSourceRetainedRegression = refl

sampleSizeRetainedRegression :
  Ceiling.StudyClaimCeilingBoundary.sampleSizeAndAnalysisNRetained
    Ceiling.canonicalStudyClaimCeilingBoundary
  ≡ true
sampleSizeRetainedRegression = refl

unreportedSampleSizeHasNoFabricatedNatRegression :
  Ceiling.StudyClaimCeilingBoundary.unreportedSampleSizeHasNoFabricatedNat
    Ceiling.canonicalStudyClaimCeilingBoundary
  ≡ true
unreportedSampleSizeHasNoFabricatedNatRegression = refl

uncertaintyRetainedRegression :
  Ceiling.StudyClaimCeilingBoundary.uncertaintyAndIntervalSemanticsRetained
    Ceiling.canonicalStudyClaimCeilingBoundary
  ≡ true
uncertaintyRetainedRegression = refl

claimStrengthBoundedRegression :
  Ceiling.StudyClaimCeilingBoundary.claimStrengthBoundedByDesignAndReceipts
    Ceiling.canonicalStudyClaimCeilingBoundary
  ≡ true
claimStrengthBoundedRegression = refl

reportedPValueNotCausalRegression :
  Ceiling.ReportedPValueCreatesCausalIdentification → ⊥
reportedPValueNotCausalRegression = Ceiling.reportedPValueDoesNotCreateCausalIdentification

sampleSizeNotRepresentativenessRegression :
  Ceiling.LargeSampleCreatesRepresentativePopulation → ⊥
sampleSizeNotRepresentativenessRegression = Ceiling.largeSampleDoesNotCreateRepresentativePopulation

ciNotTransportRegression :
  Ceiling.ConfidenceIntervalCreatesPopulationTransport → ⊥
ciNotTransportRegression = Ceiling.confidenceIntervalDoesNotCreatePopulationTransport

qualitativeNotPrevalenceRegression :
  Ceiling.QualitativeFindingCreatesPopulationPrevalence → ⊥
qualitativeNotPrevalenceRegression = Ceiling.qualitativeFindingDoesNotCreatePopulationPrevalence

studyFindingNotSystemTransformationRegression :
  Ceiling.StudyFindingCreatesSystemTransformation → ⊥
studyFindingNotSystemTransformationRegression = Ceiling.studyFindingDoesNotCreateSystemTransformation

unreportedUncertaintyNotInventedRegression :
  Ceiling.MissingUncertaintyMayBeInvented → ⊥
unreportedUncertaintyNotInventedRegression = Ceiling.missingUncertaintyMayNotBeInvented
