module DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact where

------------------------------------------------------------------------
-- 2B URANO INTEGRAL-MODULE PARITY RECEIPT
--
-- EXTERNAL SOURCE
--
-- Satoru Urano,
-- "Monstrous moonshine and indecomposable modules for integral group rings",
-- Ph.D. thesis, University of Tsukuba (2023), DOI 10.15068/0002008083.
--
-- The indexed thesis statement used here says for a Monster element of type
-- 2B:
--
--   * no trivial Z_2 indecomposable occurs in V_n tensor Z_2 for odd n;
--   * no I_2 indecomposable occurs for even n,
--
-- where I_p is the rank p-1 augmentation-quotient module in the exact
-- sequence
--
--   0 -> Z_p -> Z_p[H_p] -> I_p -> 0.
--
-- The same source states that the corresponding graded ring homomorphism for
-- the 2B case gives the Hauptmodul T_{4A}.
--
-- ATTRIBUTION FIREWALL
--
-- These are parity/exclusion constraints on source-native integral modules.
-- They do NOT:
--   * give the five supersingular inertia sectors;
--   * compute the geometric weights 3,3,2,1,1;
--   * identify Z_2 or I_2 with any Igusa/inertia sector;
--   * prove the prime=level localization used by DASHI.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source attribution.
------------------------------------------------------------------------

uranoThesis : Source.AttributedSource
uranoThesis =
  Source.mkDOISource
    "Satoru Urano"
    "Monstrous moonshine and indecomposable modules for integral group rings"
    "Ph.D. thesis, University of Tsukuba"
    "2023"
    "10.15068/0002008083"
    "https://tsukuba.repo.nii.ac.jp/records/2008083"
    (Source.namedSourceKind "doctoral thesis")
    "source for the 2B parity-dependent exclusions of the trivial Z_2 and augmentation-quotient I_2 indecomposable module types and for the associated T_4A graded ring-homomorphism Hauptmodul statement; not a source for DASHI Igusa/inertia sectors or sector lengths"
    Source.publicAttribution

uranoTwoBParitySourceAtlas : Source.AttributedSourceAtlas
uranoTwoBParitySourceAtlas =
  Source.mkSourceAtlas
    "Urano 2B integral-module parity receipt"
    "DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact"
    (uranoThesis ∷ [])
    "records only the indexed thesis 2B parity exclusions and T_4A functional; all geometric-sector interpretation remains outside the source claim"

------------------------------------------------------------------------
-- 2. Source-native abstract module labels.
------------------------------------------------------------------------

data TwoBModuleTag : Set where
  trivialZ2 :
    TwoBModuleTag
  augmentationQuotientI2 :
    TwoBModuleTag
  otherIntegralModuleTag :
    TwoBModuleTag

data DegreeParity : Set where
  evenDegree :
    DegreeParity
  oddDegree :
    DegreeParity

------------------------------------------------------------------------
-- 3. Exact sourced exclusions.
--
-- This is intentionally an exclusion relation, not an "allowed" classifier:
-- the source statements below do not prove that every non-forbidden type
-- occurs.
------------------------------------------------------------------------

data TwoBSourceForbidden :
    DegreeParity ->
    TwoBModuleTag ->
    Set where

  oddDegreeForbidsTrivial :
    TwoBSourceForbidden
      oddDegree
      trivialZ2

  evenDegreeForbidsAugmentationQuotient :
    TwoBSourceForbidden
      evenDegree
      augmentationQuotientI2

data OddDegreeContainsTrivialZ2 : Set where
data EvenDegreeContainsAugmentationQuotientI2 : Set where

oddDegreeTrivialSummandExcluded :
  OddDegreeContainsTrivialZ2 -> ⊥
oddDegreeTrivialSummandExcluded ()

evenDegreeAugmentationQuotientExcluded :
  EvenDegreeContainsAugmentationQuotientI2 -> ⊥
evenDegreeAugmentationQuotientExcluded ()

------------------------------------------------------------------------
-- 4. Source-backed Hauptmodul receipt.
------------------------------------------------------------------------

record TwoBGreenFunctionalReceipt : Set where
  constructor two-b-green-functional-receipt
  field
    sourceUsesIntegralRepresentationRingFunctional : Bool
    sourceTwoBFunctionalProducesT4A : Bool
    sourceStatementIsGraded : Bool
    sourceDeterminesFiveGeometricSectors : Bool
    sourceDeterminesSectorCompositionLengths : Bool

canonicalTwoBGreenFunctionalReceipt :
  TwoBGreenFunctionalReceipt
canonicalTwoBGreenFunctionalReceipt =
  two-b-green-functional-receipt
    true true true false false

------------------------------------------------------------------------
-- 5. Non-identification firewalls.
------------------------------------------------------------------------

data TrivialZ2IsIdentityInertiaSector : Set where
data I2IsOrderFourInertiaSector : Set where
data ParityDecompositionIsFiveSectorLocalization : Set where
data T4AFunctionalIsDuncanSwisherCorrectionTerm : Set where
data SourceExclusionsDetermineAllIndecomposableMultiplicity : Set where

trivialZ2NotIdentifiedWithIdentityInertia :
  TrivialZ2IsIdentityInertiaSector -> ⊥
trivialZ2NotIdentifiedWithIdentityInertia ()

i2NotIdentifiedWithOrderFourInertia :
  I2IsOrderFourInertiaSector -> ⊥
i2NotIdentifiedWithOrderFourInertia ()

parityDecompositionIsNotFiveSectorLocalization :
  ParityDecompositionIsFiveSectorLocalization -> ⊥
parityDecompositionIsNotFiveSectorLocalization ()

t4AFunctionalNotPromotedToDuncanSwisherCorrection :
  T4AFunctionalIsDuncanSwisherCorrectionTerm -> ⊥
t4AFunctionalNotPromotedToDuncanSwisherCorrection ()

sourceExclusionsDoNotDetermineAllMultiplicities :
  SourceExclusionsDetermineAllIndecomposableMultiplicity -> ⊥
sourceExclusionsDoNotDetermineAllMultiplicities ()

------------------------------------------------------------------------
-- 6. Live boundary.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.externalDuncanSwisherSourceClaim

-- The generic ClaimOrigin enum has no Urano-specific constructor.  The source
-- identity is carried by uranoThesis above; do NOT read claimOrigin as author
-- attribution for the thesis result.  Keep the boolean/source atlas as the
-- authoritative provenance surface.

record TwoBUranoIntegralModuleParityBoundary : Set where
  constructor two-b-urano-integral-module-parity-boundary
  field
    uranoThesisExplicitlyAttributed : Bool
    oddDegreeTrivialZ2ExclusionSourced : Bool
    evenDegreeI2ExclusionSourced : Bool
    i2AugmentationQuotientDefinitionSourced : Bool
    twoBGreenFunctionalT4ASourced : Bool
    fiveSectorLocalizationSourced : Bool
    sectorLengthsThreeThreeTwoOneOneSourced : Bool
    indecomposableLabelsIdentifiedWithInertiaSectors : Bool
    sourceExclusionsPromotedToCompleteMultiplicityClassification : Bool
    attributionFirewallPreserved : Bool

canonicalTwoBUranoIntegralModuleParityBoundary :
  TwoBUranoIntegralModuleParityBoundary
canonicalTwoBUranoIntegralModuleParityBoundary =
  two-b-urano-integral-module-parity-boundary
    true true true true true false false false false true
