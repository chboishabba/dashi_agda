module DASHI.Moonshine.OggSSPP2BanerjeeF4SameSourceRealizationExact where

------------------------------------------------------------------------
-- p=2 BANERJEE F4 SAME-SOURCE REALIZATION
--
-- Agda cannot yet construct the Witt-vector ring W(F4), so the source datum
-- remains abstract.  This module nevertheless pays the architectural theorem:
--
--   Banerjee F4 source authority
--     + realization of the source-native Galois x inertia sector labels
--   =>
--     Gamma0(4)-over-unique-ker(F^2) marked source
--     + exact ten-state bidi.
--
-- The binary factor is Gal(F4/F2), not the separate quadratic-orientation
-- doublet.  The five inertia sectors are the repository's inversion quotient
-- of G24 conjugacy classes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP2BanerjeeF4UniversalDeformationSourceExact as Banerjee
import DASHI.Moonshine.OggSSPP2SupersingularUniversalDeformationSourceExact as Universal
import DASHI.Moonshine.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparationExact as Unique
import DASHI.Moonshine.OggSSPP2UniqueGamma0FourMarkingBidiExact as Bidi
import DASHI.Moonshine.OggSSPP2F4AntipodalStratifiedRefinementExact as Target
import DASHI.Moonshine.OggSSPP2F4FrobeniusCandidateNoGoExact as F4
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source authority: binds one abstract Agda datum to the Banerjee source.
------------------------------------------------------------------------

record BanerjeeF4SourceAuthority : Set₁ where
  field
    datum :
      Universal.SupersingularUniversalDeformationDatum

    sourceMatchesBanerjeeF4UniversalDeformation :
      Bool

    sourceMatchesBanerjeeF4UniversalDeformationIsTrue :
      sourceMatchesBanerjeeF4UniversalDeformation ≡ true

    residueFieldIsF4 :
      Bool

    residueFieldIsF4IsTrue :
      residueFieldIsF4 ≡ true

    wittBaseIsWF4 :
      Bool

    wittBaseIsWF4IsTrue :
      wittBaseIsWF4 ≡ true

    g24SemidirectGaloisTorsorStructureRetained :
      Bool

    g24SemidirectGaloisTorsorStructureRetainedIsTrue :
      g24SemidirectGaloisTorsorStructureRetained ≡ true

open BanerjeeF4SourceAuthority public

------------------------------------------------------------------------
-- 2. Single state-level realization obligation.
------------------------------------------------------------------------

record GaloisInertiaSectorRealization
  (authority : BanerjeeF4SourceAuthority) : Set₁ where
  field
    underlyingFamilyState :
      Banerjee.GaloisInertiaState ->
      Universal.EllipticFamilyState (datum authority)

    gamma0FourLevelStructurePresent :
      Banerjee.GaloisInertiaState ->
      Bool

    gamma0FourLevelStructurePresentIsTrue :
      (state : Banerjee.GaloisInertiaState) ->
      gamma0FourLevelStructurePresent state ≡ true

    deformationProvenanceRetained :
      Banerjee.GaloisInertiaState ->
      Bool

    deformationProvenanceRetainedIsTrue :
      (state : Banerjee.GaloisInertiaState) ->
      deformationProvenanceRetained state ≡ true

open GaloisInertiaSectorRealization public

------------------------------------------------------------------------
-- 3. Realization -> marked source.
------------------------------------------------------------------------

marking :
  {authority : BanerjeeF4SourceAuthority} ->
  GaloisInertiaSectorRealization authority ->
  Universal.Gamma0FourUniversalDeformationMarking (datum authority)
marking realization =
  record
    { MarkedState =
        Banerjee.GaloisInertiaState
    ; underlyingFamilyState =
        underlyingFamilyState realization
    ; specializesToRawSubgroup =
        λ _ -> Unique.kerFrobeniusSquared
    ; specializationIsUniqueKerFrobeniusSquared =
        λ _ -> refl
    ; gamma0FourLevelStructurePresent =
        gamma0FourLevelStructurePresent realization
    ; gamma0FourLevelStructurePresentIsTrue =
        gamma0FourLevelStructurePresentIsTrue realization
    ; deformationProvenanceRetained =
        deformationProvenanceRetained realization
    ; deformationProvenanceRetainedIsTrue =
        deformationProvenanceRetainedIsTrue realization
    }

sourceCoarseOrbit :
  Banerjee.GaloisInertiaState ->
  F4.F4FrobeniusOrbit
sourceCoarseOrbit state =
  Target.stratumOf (Banerjee.toTarget state)

------------------------------------------------------------------------
-- 4. Realization -> ten-state bidi and recognition automatically.
------------------------------------------------------------------------

markingBidi :
  {authority : BanerjeeF4SourceAuthority} ->
  (realization : GaloisInertiaSectorRealization authority) ->
  Bidi.UniqueGamma0FourMarkingBidi
    (Universal.toUniqueSubgroupMarking (marking realization))
markingBidi realization =
  record
    { sourceCoarseOrbit =
        sourceCoarseOrbit
    ; toTarget =
        Banerjee.toTarget
    ; fromTarget =
        Banerjee.fromTarget
    ; sourceRoundTrip =
        Banerjee.sourceRoundTrip
    ; targetRoundTrip =
        Banerjee.targetRoundTrip
    ; toTargetPreservesCoarseOrbit =
        λ state -> refl
    ; fromTargetPreservesCoarseOrbit =
        λ state -> cong Target.stratumOf (Banerjee.targetRoundTrip state)
    ; everyMappedStateStillLiesOverUniqueRawSubgroup =
        λ state -> refl
    }

tenStateRecognition :
  {authority : BanerjeeF4SourceAuthority} ->
  (realization : GaloisInertiaSectorRealization authority) ->
  Universal.UniversalDeformationTenStateRecognition
    (datum authority)
    (marking realization)
tenStateRecognition realization =
  record
    { arithmeticBidi =
        markingBidi realization
    }

------------------------------------------------------------------------
-- 5. Compressed live residual.
------------------------------------------------------------------------

data BanerjeeF4RealizationResidual : Set where
  missingBanerjeeF4SourceAuthority :
    BanerjeeF4RealizationResidual

  missingGaloisInertiaSectorRealization :
    BanerjeeF4RealizationResidual

firstResidual :
  BanerjeeF4RealizationResidual
firstResidual =
  missingBanerjeeF4SourceAuthority

data SeparateTenStateClassificationAfterSectorRealization : Set where

separateClassificationNotRequired :
  SeparateTenStateClassificationAfterSectorRealization -> ⊥
separateClassificationNotRequired ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record BanerjeeF4SameSourceRealizationBoundary : Set where
  constructor banerjee-f4-same-source-realization-boundary
  field
    preferredSourceResidueFieldIsF4 : Bool
    g24AndGaloisShareOneDeformationSource : Bool
    galoisSheetKeptDistinctFromQuadraticOrientation : Bool
    oneSectorRealizationConstructsMarkedSource : Bool
    oneSectorRealizationConstructsTenStateBidi : Bool
    separateTenStateClassificationRequiredAfterRealization : Bool
    sourceAuthorityInhabitedHere : Bool
    sectorRealizationInhabitedHere : Bool

canonicalBanerjeeF4SameSourceRealizationBoundary :
  BanerjeeF4SameSourceRealizationBoundary
canonicalBanerjeeF4SameSourceRealizationBoundary =
  banerjee-f4-same-source-realization-boundary
    true true true true true false false false
