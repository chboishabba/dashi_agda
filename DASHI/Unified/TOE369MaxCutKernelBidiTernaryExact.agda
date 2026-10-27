module DASHI.Unified.TOE369MaxCutKernelBidiTernaryExact where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed
import DASHI.Moonshine.Base369Ternary27CharacterAdjacencyEquivarianceExact as Character
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Moonshine.Monster3BPhaseTransportExact as Monster
import DASHI.Reasoning.Trialectic369Selected3BFullGradeActionMaxCutExact as FullGrade
import DASHI.Reasoning.Trialectic369Selected3BProjectedActionMaxCutExact as Projected
import DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact as KernelSame
import DASHI.Moonshine.MonsterGradedVOASelected3BSameElementBidiExact as SelectedSame
import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as SingleAction
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as TernaryReduction
import DASHI.Wikimedia.IbrahimMonster3BLinearShortestFrontierCorrectionExact as Ibrahim

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F.
--
-- O. Converge the existing max-cut, kernel-BIDI, and ternary-27 owners.
-- R. Reuse the canonical theorem owners above.
-- C. Export only exact aliases and non-promotion theorems.
-- S. Keep carrier identity, action identity, and representation promotion
--    separate. Keep ESD surfaces read-only.
-- L. This lane owns only TOE normalization.
-- P. Preconditions: donor owners exist and retain theorem ownership.
--    Invariants: no cardinality or character coincidence creates an action.
--    Postconditions: both TOE roots can reach each exact firewall.
-- G. Original authors and source repositories retain attribution.
-- F. Exact-head Agda validation is required before kernel certification.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Ternary-27 exact symmetry.
------------------------------------------------------------------------

toe27RotationOrderThree :
  (point : Geometry.Ternary27Point) →
  Spectral.rotateXYZ
    (Spectral.rotateXYZ
      (Spectral.rotateXYZ point))
  ≡ point
toe27RotationOrderThree = Spectral.rotateXYZOrderThree

toe27OriginFixed :
  Spectral.rotateXYZ Geometry.origin ≡ Geometry.origin
toe27OriginFixed = Spectral.originFixedByRotation

FullCubeRotationFree : Set
FullCubeRotationFree =
  (point : Geometry.Ternary27Point) →
  Spectral.rotateXYZ point ≡ point →
  ⊥

toe27FullCubeRotationNotFree :
  FullCubeRotationFree → ⊥
toe27FullCubeRotationNotFree free =
  free Geometry.origin toe27OriginFixed

toe27MonsterPhaseConjugationIntertwiner =
  Signed.monsterAxisReflectionIntertwines

toe27MonsterRepresentationNotPromoted :
  Signed.SignedTernaryVoxelSymmetryBoundary.voxelRepresentationOfMonsterEstablished
    Signed.canonicalSignedTernaryVoxelSymmetryBoundary
  ≡ false
toe27MonsterRepresentationNotPromoted = refl

toe27MonsterEmbeddingNotPromoted :
  Signed.SignedTernaryVoxelSymmetryBoundary.signedPermutationGroupEmbeddedInMonster
    Signed.canonicalSignedTernaryVoxelSymmetryBoundary
  ≡ false
toe27MonsterEmbeddingNotPromoted = refl

toe27PhaseReductionNotGlobalInversion :
  TernaryReduction.phasePreservingReductionEqualsFullGlobalInversion
    TernaryReduction.currentTernary27ReductionBoundary
  ≡ false
toe27PhaseReductionNotGlobalInversion =
  TernaryReduction.phasePreservingReductionEqualsFullGlobalInversionIsFalse

toe27OrbitIndexingNotSemanticIdentity :
  TernaryReduction.orbitToComplementModeIndexingIsSemanticIdentity
    TernaryReduction.currentTernary27ReductionBoundary
  ≡ false
toe27OrbitIndexingNotSemanticIdentity =
  TernaryReduction.orbitToComplementModeIndexingIsSemanticIdentityIsFalse

toe27ReductionNotMonster42SameObject :
  TernaryReduction.reducedFifteenIsMonster42dSameObject
    TernaryReduction.currentTernary27ReductionBoundary
  ≡ false
toe27ReductionNotMonster42SameObject =
  TernaryReduction.reducedFifteenIsMonster42dSameObjectIsFalse

------------------------------------------------------------------------
-- Selected-3B max-cut partitions.
------------------------------------------------------------------------

toeFullGradeDimensionDoesNotCreateFaithfulness :
  FullGrade.LinearDimensionCreatesFaithfulness → ⊥
toeFullGradeDimensionDoesNotCreateFaithfulness =
  FullGrade.dimensionDoesNotCreateFaithfulness

toeFullGradeSameCarrierDoesNotCreateActionAgreement :
  FullGrade.SameCarrierCreatesFullGradeActionAgreement → ⊥
toeFullGradeSameCarrierDoesNotCreateActionAgreement =
  FullGrade.sameCarrierDoesNotCreateActionAgreement

toeFullGradeCharacterDoesNotCreateActionAgreement :
  FullGrade.CharacterCreatesFullGradeActionAgreement → ⊥
toeFullGradeCharacterDoesNotCreateActionAgreement =
  FullGrade.characterDoesNotCreateActionAgreement

toeProjectedDimensionDoesNotCreateAction :
  Projected.DirectSumDimensionCreatesProjectedAction → ⊥
toeProjectedDimensionDoesNotCreateAction =
  Projected.dimensionDoesNotCreateProjectedAction

toeCoordinateRetractionDoesNotCreateProjectedAction :
  Projected.CoordinateRetractionCreatesProjectedLinearAction → ⊥
toeCoordinateRetractionDoesNotCreateProjectedAction =
  Projected.coordinateRetractionDoesNotCreateProjectedAction

toeProjectedCharacterDoesNotCreateAction :
  Projected.CharacterCreatesProjectedAction → ⊥
toeProjectedCharacterDoesNotCreateAction =
  Projected.characterDoesNotCreateProjectedAction

------------------------------------------------------------------------
-- Kernel BIDI bindings.
--
-- The tranche runner calls this the CFFI kernel-BIDI coordinate.
-- No separate CFFI theorem owner exists in dashi_agda.
-- These are the exact proof-bearing kernel and selected-element owners.
------------------------------------------------------------------------

toeKernelTrace53DoesNotIdentify3B :
  KernelSame.Actual3BKernelSameElementBoundary.trace53AloneIdentifiesMonster3B
    KernelSame.canonicalActual3BKernelSameElementBoundary
  ≡ false
toeKernelTrace53DoesNotIdentify3B = refl

toeKernelCharacterIsotypyDoesNotConstructActionIntertwiner :
  KernelSame.Actual3BKernelSameElementBoundary.characterIsotypyConstructsActionIntertwiner
    KernelSame.canonicalActual3BKernelSameElementBoundary
  ≡ false
toeKernelCharacterIsotypyDoesNotConstructActionIntertwiner = refl

toeKernelActualZetaRecognitionStillOpen :
  KernelSame.Actual3BKernelSameElementBoundary.actualZetaRecognitionProvedHere
    KernelSame.canonicalActual3BKernelSameElementBoundary
  ≡ false
toeKernelActualZetaRecognitionStillOpen = refl

toeKernelFullHyperformalActionStillOpen :
  KernelSame.Actual3BKernelSameElementBoundary.fullHyperfabricMonsterActionProvedHere
    KernelSame.canonicalActual3BKernelSameElementBoundary
  ≡ false
toeKernelFullHyperformalActionStillOpen = refl

toeSelectedSameElementClass3BStillOpen :
  SelectedSame.Selected3BSameElementBoundary.selectedElementProvedMonsterClass3BHere
    SelectedSame.canonicalSelected3BSameElementBoundary
  ≡ false
toeSelectedSameElementClass3BStillOpen = refl

toeSingleActionProducerStillOpen :
  SingleAction.SingleActionProducerBoundary.actualSingleProducerInhabitedHere
    SingleAction.canonicalSingleActionProducerBoundary
  ≡ false
toeSingleActionProducerStillOpen = refl

------------------------------------------------------------------------
-- Ibrahim non-promotion partitions.
------------------------------------------------------------------------

toeFiniteChartDoesNotCreateLinearMultiplicityAction :
  Ibrahim.FiniteChartCreatesLinearMultiplicityAction → ⊥
toeFiniteChartDoesNotCreateLinearMultiplicityAction =
  Ibrahim.finiteChartDoesNotCreateLinearMultiplicityAction

toeNinetySlicesDoNotCreatePermutationRepresentation :
  Ibrahim.NinetySlicesCreatePermutationRepresentation → ⊥
toeNinetySlicesDoNotCreatePermutationRepresentation =
  Ibrahim.ninetySlicesDoNotCreatePermutationRepresentation

toeCharacterDoesNotCreateHomEvaluation :
  Ibrahim.CharacterCreatesHomEvaluation → ⊥
toeCharacterDoesNotCreateHomEvaluation =
  Ibrahim.characterDoesNotCreateHomEvaluation

toePermutationNoGoDoesNotCreateLinearAction :
  Ibrahim.NonPermutationNoGoCreatesLinearAction → ⊥
toePermutationNoGoDoesNotCreateLinearAction =
  Ibrahim.noGoDoesNotCreateLinearAction
