module DASHI.Moonshine.OggSSPP2OrientedInertiaUniversalDeformationRealizationExact where

------------------------------------------------------------------------
-- p=2 ORIENTED-INERTIA REALIZATION INSIDE A UNIVERSAL DEFORMATION
--
-- DASHI CONTRIBUTION
--
-- The repository already owns a classically sourced ten-state candidate
--
--   2 quadratic orientations x 5 binary-tetrahedral inversion-orbits.
--
-- This module makes the remaining source theorem precise:
-- realize THOSE states as genuine marked states of one supersingular
-- universal-deformation family.
--
-- Once such a realization exists, the Gamma_0(4) marked source and the exact
-- ten-state bidi are constructed automatically.  Thus
--
--   "construct marked states"
--   +
--   "prove ten-state classification"
--
-- collapse to one source-level realization obligation.
--
-- This does NOT identify the ten states with ten coarse Gamma_0(4) subgroup
-- choices; the raw subgroup remains the unique ker(F^2).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP2SupersingularUniversalDeformationSourceExact as Universal
import DASHI.Moonshine.OggSSPP2OrientedInertiaTenStateRecognitionExact as Oriented
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparationExact as Unique
import DASHI.Moonshine.OggSSPP2UniqueGamma0FourMarkingBidiExact as Bidi
import DASHI.Moonshine.OggSSPP2F4AntipodalStratifiedRefinementExact as Target
import DASHI.Moonshine.OggSSPP2F4FrobeniusCandidateNoGoExact as F4
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Direct exact rechart from oriented inertia to the paid stratified target.
------------------------------------------------------------------------

toTarget :
  Oriented.P2OrientedInertiaState ->
  Target.F4StratifiedTargetState
toTarget
  (Oriented.firstGaloisOrientation , Inertia.identityInertiaOrbit) =
  Target.fixedZeroRefinement
toTarget
  (Oriented.conjugateGaloisOrientation , Inertia.identityInertiaOrbit) =
  Target.fixedOneRefinement
toTarget
  (Oriented.firstGaloisOrientation , Inertia.centralMinusOneInertiaOrbit) =
  Target.conjugateRefinement Compression.lowerSide Target.firstAxisNoncentral
toTarget
  (Oriented.conjugateGaloisOrientation , Inertia.centralMinusOneInertiaOrbit) =
  Target.conjugateRefinement Compression.upperSide Target.firstAxisNoncentral
toTarget
  (Oriented.firstGaloisOrientation , Inertia.orderFourInertiaOrbit) =
  Target.conjugateRefinement Compression.lowerSide Target.secondAxisNoncentral
toTarget
  (Oriented.conjugateGaloisOrientation , Inertia.orderFourInertiaOrbit) =
  Target.conjugateRefinement Compression.upperSide Target.secondAxisNoncentral
toTarget
  (Oriented.firstGaloisOrientation , Inertia.orderThreePairInertiaOrbit) =
  Target.conjugateRefinement Compression.lowerSide Target.equalSignNoncentral
toTarget
  (Oriented.conjugateGaloisOrientation , Inertia.orderThreePairInertiaOrbit) =
  Target.conjugateRefinement Compression.upperSide Target.equalSignNoncentral
toTarget
  (Oriented.firstGaloisOrientation , Inertia.orderSixPairInertiaOrbit) =
  Target.conjugateRefinement Compression.lowerSide Target.oppositeSignNoncentral
toTarget
  (Oriented.conjugateGaloisOrientation , Inertia.orderSixPairInertiaOrbit) =
  Target.conjugateRefinement Compression.upperSide Target.oppositeSignNoncentral

fromTarget :
  Target.F4StratifiedTargetState ->
  Oriented.P2OrientedInertiaState
fromTarget Target.fixedZeroRefinement =
  Oriented.firstGaloisOrientation , Inertia.identityInertiaOrbit
fromTarget Target.fixedOneRefinement =
  Oriented.conjugateGaloisOrientation , Inertia.identityInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.lowerSide Target.firstAxisNoncentral) =
  Oriented.firstGaloisOrientation , Inertia.centralMinusOneInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.upperSide Target.firstAxisNoncentral) =
  Oriented.conjugateGaloisOrientation , Inertia.centralMinusOneInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.lowerSide Target.secondAxisNoncentral) =
  Oriented.firstGaloisOrientation , Inertia.orderFourInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.upperSide Target.secondAxisNoncentral) =
  Oriented.conjugateGaloisOrientation , Inertia.orderFourInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.lowerSide Target.equalSignNoncentral) =
  Oriented.firstGaloisOrientation , Inertia.orderThreePairInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.upperSide Target.equalSignNoncentral) =
  Oriented.conjugateGaloisOrientation , Inertia.orderThreePairInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.lowerSide Target.oppositeSignNoncentral) =
  Oriented.firstGaloisOrientation , Inertia.orderSixPairInertiaOrbit
fromTarget
  (Target.conjugateRefinement Compression.upperSide Target.oppositeSignNoncentral) =
  Oriented.conjugateGaloisOrientation , Inertia.orderSixPairInertiaOrbit

sourceRoundTrip :
  (state : Oriented.P2OrientedInertiaState) ->
  fromTarget (toTarget state) ≡ state
sourceRoundTrip
  (Oriented.firstGaloisOrientation , Inertia.identityInertiaOrbit) = refl
sourceRoundTrip
  (Oriented.conjugateGaloisOrientation , Inertia.identityInertiaOrbit) = refl
sourceRoundTrip
  (Oriented.firstGaloisOrientation , Inertia.centralMinusOneInertiaOrbit) = refl
sourceRoundTrip
  (Oriented.conjugateGaloisOrientation , Inertia.centralMinusOneInertiaOrbit) = refl
sourceRoundTrip
  (Oriented.firstGaloisOrientation , Inertia.orderFourInertiaOrbit) = refl
sourceRoundTrip
  (Oriented.conjugateGaloisOrientation , Inertia.orderFourInertiaOrbit) = refl
sourceRoundTrip
  (Oriented.firstGaloisOrientation , Inertia.orderThreePairInertiaOrbit) = refl
sourceRoundTrip
  (Oriented.conjugateGaloisOrientation , Inertia.orderThreePairInertiaOrbit) = refl
sourceRoundTrip
  (Oriented.firstGaloisOrientation , Inertia.orderSixPairInertiaOrbit) = refl
sourceRoundTrip
  (Oriented.conjugateGaloisOrientation , Inertia.orderSixPairInertiaOrbit) = refl

targetRoundTrip :
  (state : Target.F4StratifiedTargetState) ->
  toTarget (fromTarget state) ≡ state
targetRoundTrip Target.fixedZeroRefinement = refl
targetRoundTrip Target.fixedOneRefinement = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.lowerSide Target.firstAxisNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.upperSide Target.firstAxisNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.lowerSide Target.secondAxisNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.upperSide Target.secondAxisNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.lowerSide Target.equalSignNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.upperSide Target.equalSignNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.lowerSide Target.oppositeSignNoncentral) = refl
targetRoundTrip
  (Target.conjugateRefinement Compression.upperSide Target.oppositeSignNoncentral) = refl

------------------------------------------------------------------------
-- 2. One source-side realization obligation.
------------------------------------------------------------------------

record OrientedInertiaDeformationRealization
  (datum : Universal.SupersingularUniversalDeformationDatum) : Set₁ where
  field
    underlyingFamilyState :
      Oriented.P2OrientedInertiaState ->
      Universal.EllipticFamilyState datum

    gamma0FourLevelStructurePresent :
      Oriented.P2OrientedInertiaState ->
      Bool

    gamma0FourLevelStructurePresentIsTrue :
      (state : Oriented.P2OrientedInertiaState) ->
      gamma0FourLevelStructurePresent state ≡ true

    deformationProvenanceRetained :
      Oriented.P2OrientedInertiaState ->
      Bool

    deformationProvenanceRetainedIsTrue :
      (state : Oriented.P2OrientedInertiaState) ->
      deformationProvenanceRetained state ≡ true

open OrientedInertiaDeformationRealization public

------------------------------------------------------------------------
-- 3. Realization -> marked universal-deformation source.
------------------------------------------------------------------------

marking :
  {datum : Universal.SupersingularUniversalDeformationDatum} ->
  OrientedInertiaDeformationRealization datum ->
  Universal.Gamma0FourUniversalDeformationMarking datum
marking realization =
  record
    { MarkedState =
        Oriented.P2OrientedInertiaState
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

------------------------------------------------------------------------
-- 4. Realization -> exact ten-state bidi automatically.
------------------------------------------------------------------------

sourceCoarseOrbit :
  Oriented.P2OrientedInertiaState ->
  F4.F4FrobeniusOrbit
sourceCoarseOrbit state =
  Target.stratumOf (toTarget state)

markingBidi :
  {datum : Universal.SupersingularUniversalDeformationDatum} ->
  (realization : OrientedInertiaDeformationRealization datum) ->
  Bidi.UniqueGamma0FourMarkingBidi
    (Universal.toUniqueSubgroupMarking (marking realization))
markingBidi realization =
  record
    { sourceCoarseOrbit =
        sourceCoarseOrbit
    ; toTarget =
        toTarget
    ; fromTarget =
        fromTarget
    ; sourceRoundTrip =
        sourceRoundTrip
    ; targetRoundTrip =
        targetRoundTrip
    ; toTargetPreservesCoarseOrbit =
        λ state -> refl
    ; fromTargetPreservesCoarseOrbit =
        λ state -> cong Target.stratumOf (targetRoundTrip state)
    ; everyMappedStateStillLiesOverUniqueRawSubgroup =
        λ state -> refl
    }

tenStateRecognition :
  {datum : Universal.SupersingularUniversalDeformationDatum} ->
  (realization : OrientedInertiaDeformationRealization datum) ->
  Universal.UniversalDeformationTenStateRecognition
    datum
    (marking realization)
tenStateRecognition realization =
  record
    { arithmeticBidi =
        markingBidi realization
    }

------------------------------------------------------------------------
-- 5. Frontier compression.
------------------------------------------------------------------------

data SeparateMarkedStateAndTenStateProofsRequired : Set where

separateProofsNotRequiredAfterRealization :
  SeparateMarkedStateAndTenStateProofsRequired -> ⊥
separateProofsNotRequiredAfterRealization ()

data OrientedInertiaCarrierIsGamma04CoarseFibre : Set where

orientedInertiaDoesNotBecomeGamma04CoarseFibre :
  OrientedInertiaCarrierIsGamma04CoarseFibre -> ⊥
orientedInertiaDoesNotBecomeGamma04CoarseFibre ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record OrientedInertiaUniversalDeformationRealizationBoundary : Set where
  constructor oriented-inertia-universal-deformation-realization-boundary
  field
    classicallySourcedTenStateVocabularyReused : Bool
    exactRechartToPaidStratifiedTargetOwned : Bool
    oneRealizationConstructsMarkedSource : Bool
    oneRealizationConstructsTenStateBidi : Bool
    separateTenStateClassificationProofRequired : Bool
    gamma04CoarseLevelFibreIdentifiedWithTenStates : Bool
    realizationInhabitedHere : Bool

canonicalOrientedInertiaUniversalDeformationRealizationBoundary :
  OrientedInertiaUniversalDeformationRealizationBoundary
canonicalOrientedInertiaUniversalDeformationRealizationBoundary =
  oriented-inertia-universal-deformation-realization-boundary
    true true true true false false false
