module DASHI.Physics.Catalysis.HighEntropyMBeneDFTScalingWitnessAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition

------------------------------------------------------------------------
-- DFT SCALING-WITNESS ACQUISITION
--
-- The generic residual-scaling theorem is already owned.  This module records
-- the exact empirical/numerical receipt still needed to instantiate it for the
-- reported high-entropy MBene system.
------------------------------------------------------------------------

record DFTSeparatingPairTarget : Set where
  constructor dft-separating-pair-target
  field
    leftConfiguration rightConfiguration : String
    coarseDescriptorName : String
    residualDescriptorName : String
    targetEnergyName : String

    sameCoarseDescriptorExtracted : Bool
    residualSeparationExtracted : Bool
    targetEnergySeparationExtracted : Bool

    sourceTableOrFigureLocator : String
    rawNumericalDataLocator : String

open DFTSeparatingPairTarget public

record ExactWitnessReady (target : DFTSeparatingPairTarget) : Set where
  constructor exact-witness-ready
  field
    sameCoarseReady : sameCoarseDescriptorExtracted target ≡ true
    residualReady : residualSeparationExtracted target ≡ true
    targetEnergyReady : targetEnergySeparationExtracted target ≡ true

open ExactWitnessReady public

------------------------------------------------------------------------
-- Acquisition is separate from proof readiness.
------------------------------------------------------------------------

record DFTWitnessAcquisition : Set where
  constructor dft-witness-acquisition
  field
    sourceTarget : Acquisition.SourceAcquisitionTarget
    candidatePairIdentified : Bool
    descriptorValuesExtracted : Bool
    residualValuesExtracted : Bool
    targetEnergyValuesExtracted : Bool
    equalityOrTolerancePolicyDeclared : Bool

open DFTWitnessAcquisition public

record DFTWitnessAcquisitionBoundary : Set where
  constructor dft-witness-acquisition-boundary
  field
    paperMechanismClaimEqualsExactNumericalWitness : Bool
    paperMechanismClaimEqualsExactNumericalWitnessIsFalse :
      paperMechanismClaimEqualsExactNumericalWitness ≡ false

    bibliographicAccessEqualsNumericalExtraction : Bool
    bibliographicAccessEqualsNumericalExtractionIsFalse :
      bibliographicAccessEqualsNumericalExtraction ≡ false

    approximateDescriptorMatchEqualsLiteralAgdaEquality : Bool
    approximateDescriptorMatchEqualsLiteralAgdaEqualityIsFalse :
      approximateDescriptorMatchEqualsLiteralAgdaEquality ≡ false

    tolerancePolicyMayBeNeededForFloatingDFTData : Bool
    tolerancePolicyMayBeNeededForFloatingDFTDataIsTrue :
      tolerancePolicyMayBeNeededForFloatingDFTData ≡ true

canonicalDFTWitnessAcquisitionBoundary : DFTWitnessAcquisitionBoundary
canonicalDFTWitnessAcquisitionBoundary =
  dft-witness-acquisition-boundary false refl false refl false refl true refl

------------------------------------------------------------------------
-- Current acquisition state: source identified and mechanism inspected, exact
-- same-coarse separating pair not yet extracted.
------------------------------------------------------------------------

canonicalPaperAcquisitionTarget : Acquisition.SourceAcquisitionTarget
canonicalPaperAcquisitionTarget = record
  { citationLabel =
      "Bharadwaj H and Ranganathan, npj Computational Materials (2026), DOI 10.1038/s41524-026-02287-4"
  ; pageLocator = "full paper / supplementary numerical data"
  ; primaryRoute = Acquisition.publisherBackfile
  ; alternateRoute = Acquisition.directDigitalArchive
  ; fullTextAcquired = true
  ; primaryTextInspected = true
  ; transcriptionExtracted = false
  }

canonicalCurrentDFTWitnessAcquisition : DFTWitnessAcquisition
canonicalCurrentDFTWitnessAcquisition = record
  { sourceTarget = canonicalPaperAcquisitionTarget
  ; candidatePairIdentified = false
  ; descriptorValuesExtracted = false
  ; residualValuesExtracted = false
  ; targetEnergyValuesExtracted = false
  ; equalityOrTolerancePolicyDeclared = false
  }

------------------------------------------------------------------------
-- BIDI acquisition compiler: the reverse theorem tells us exactly what to
-- search for next rather than treating LIVE as an unstructured gap.
------------------------------------------------------------------------

record ReverseAcquisitionObligation : Set where
  constructor reverse-acquisition-obligation
  field
    findPairSharingCoarseDescriptor : Bool
    findPairSharingCoarseDescriptorIsTrue :
      findPairSharingCoarseDescriptor ≡ true

    extractLocalChargeOrNeighbourhoodResidual : Bool
    extractLocalChargeOrNeighbourhoodResidualIsTrue :
      extractLocalChargeOrNeighbourhoodResidual ≡ true

    extractCOOHStarTargetEnergetics : Bool
    extractCOOHStarTargetEnergeticsIsTrue :
      extractCOOHStarTargetEnergetics ≡ true

    declareExactOrToleranceEqualityPolicy : Bool
    declareExactOrToleranceEqualityPolicyIsTrue :
      declareExactOrToleranceEqualityPolicy ≡ true

canonicalReverseAcquisitionObligation : ReverseAcquisitionObligation
canonicalReverseAcquisitionObligation =
  reverse-acquisition-obligation true refl true refl true refl true refl
