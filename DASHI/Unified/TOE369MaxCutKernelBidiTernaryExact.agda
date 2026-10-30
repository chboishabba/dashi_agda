module DASHI.Unified.TOE369MaxCutKernelBidiTernaryExact where
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as NativeIdentity
import DASHI.Combinatorics.GraphColouring369PantsQidParetoSnowballExact as NativeQid369
import DASHI.Combinatorics.GraphColouring369PantsWeightedMaxCutExact as NativeMaxCut369
import DASHI.Reasoning.TrialecticWeightedGraphFaceMediationSelectedExact as SelectedFace369
import DASHI.Combinatorics.GraphColouring369PantsHomomorphismBoundaryExact as GridPants369
import DASHI.Combinatorics.GraphColouringHomomorphismCoreExact as GridColour
import DASHI.Combinatorics.GraphColouring369PantsGridAdjacencyExact as NativeGridPants
import DASHI.Reasoning.TrialecticWeightedDirectedGraph369Exact as WeightedGraph369
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as DirectedObserver
import DASHI.Core.ConsumerDescentMinimalObserverExact as DirectedDescent

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_)
open import Data.List using (List)
open import Data.Unit using (⊤)

import DASHI.Foundations.SSPTritCarrier as SSP
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

toe27MonsterPhaseConjugationIntertwiner :
  (frequency : Spectral.AxisFrequency) →
  (trit : SSP.SSPTrit) →
  Fourier.phaseToMonster
    (Character.axisCharacterValue
      (Spectral.conjugateFrequency frequency) trit)
  ≡
  Monster.transportPhase Monster.invertsGenerator
    (Fourier.phaseToMonster
      (Character.axisCharacterValue frequency trit))
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

------------------------------------------------------------------------
-- Source-typed weighted directed-graph/trialectic regression.
-- This is not a Monster action, a smooth pants gluing, or an actual
-- C3-equivariant weighted representation.
------------------------------------------------------------------------

toeWeightedMatrixDigraphRoundTrip :
  WeightedGraph369.digraphToMatrix
    (WeightedGraph369.matrixToDigraph
      WeightedGraph369.dankaWeightedMatrixTenths)
  ≡ WeightedGraph369.dankaWeightedMatrixTenths
toeWeightedMatrixDigraphRoundTrip =
  WeightedGraph369.matrixDigraphRoundTrip
    WeightedGraph369.dankaWeightedMatrixTenths

toeWeightedGraphHasSixArrows :
  WeightedGraph369.nonzeroEdgeCount ≡ 6
toeWeightedGraphHasSixArrows = WeightedGraph369.sixArrowsIncludingOneLoop

toeWeightRotationNotAutomaticallyC3 :
  ((source target : DirectedObserver.Participant3) ->
    WeightedGraph369.dankaWeight
      (WeightedGraph369.rotateVertex source)
      (WeightedGraph369.rotateVertex target)
    ≡ WeightedGraph369.dankaWeight source target) -> ⊥
toeWeightRotationNotAutomaticallyC3 =
  WeightedGraph369.weightedDankaGraphNotC3Invariant

toeWeightedGraphDoesNotDetermineAttachedFace :
  DirectedDescent.FactorsThrough
    WeightedGraph369.graphObserver
    WeightedGraph369.triadicConsumer -> ⊥
toeWeightedGraphDoesNotDetermineAttachedFace =
  WeightedGraph369.matrixDoesNotDetermineTrialecticFace

------------------------------------------------------------------------
-- Native ternary-27 -> finite pants path graph max-cut.
-- Do not identify the 3-vertex weighted fixture with this 27-grid, or
-- a finite pants graph with a smooth TQFT.  These are constructed terms,
-- with independent kernel verification still outstanding.
------------------------------------------------------------------------

toeNativeVoxelPantsGraphHom :
  GridColour.GraphHom
    GridPants369.nativeVoxelGrid GridPants369.nativePantsGrid
toeNativeVoxelPantsGraphHom =
  GridPants369.nativeVoxelToPantsGraphHom

toeNativePantsGridHasTwoColouring :
  GridColour.Colouring
    GridPants369.nativePantsGrid
    NativeGridPants.twoColourPalette
toeNativePantsGridHasTwoColouring =
  NativeGridPants.pantsTwoColouring

toeNoSingletonColouringPants :
  GridColour.Colouring
    GridPants369.nativePantsGrid
    (GridColour.paletteGraph ⊤ (λ _ _ -> ⊥))
    -> ⊥
toeNoSingletonColouringPants =
  NativeGridPants.noOneColouringOfPantsGrid

toeSixPermutationImagesDistinct :
  (left right : NativeGridPants.S3CoordinatePermutation) ->
  NativeGridPants.actS3Pants
    left NativeGridPants.s3DistinctAnchor
  ≡ NativeGridPants.actS3Pants
    right NativeGridPants.s3DistinctAnchor
  -> left ≡ right
toeSixPermutationImagesDistinct =
  NativeGridPants.s3AnchorImageInjective

------------------------------------------------------------------------
-- Selected finite attached-face mediation: a source-independent chart,
-- NOT a universal inferred face law.  The output fails graph-only descent.
------------------------------------------------------------------------

toeSelectedOutputNoGraphOnlyDecoder :
  DirectedDescent.FactorsThrough
    WeightedGraph369.graphObserver
    SelectedFace369.selectedOutputConsumer -> ⊥
toeSelectedOutputNoGraphOnlyDecoder =
  SelectedFace369.selectedNextDepthOutputCannotFactorThroughGraph

------------------------------------------------------------------------
-- Native 27-grid QID + genuine weighted maximum-cut Pareto max-cut.
-- QID is concept identity only; no graph-object or Monster same-object claim.
------------------------------------------------------------------------

toeNativeEdgewiseWeightedMaximumCut :
  (edges : List NativeMaxCut369.NativeWeightedEdge) ->
  (candidate : NativeMaxCut369.Partition) ->
  NativeMaxCut369.cutScore candidate edges
  ≤ NativeMaxCut369.cutScore NativeMaxCut369.checkerCut edges
toeNativeEdgewiseWeightedMaximumCut =
  NativeMaxCut369.checkerMaximumCut

toeNative54UnitCutWitness :
  NativeMaxCut369.cutScore
    NativeMaxCut369.checkerCut
    NativeMaxCut369.unitNativeGridEdges ≡ 54
toeNative54UnitCutWitness =
  NativeMaxCut369.checkerWitnessScoreIs54

toeVerifiedConceptQidsRetainNoAuthority :
  NativeIdentity.SnowballExternalIdentityPolicy.externalIdentityCreatesSemanticAuthority
    NativeIdentity.canonicalExternalIdentityPolicy ≡ false
toeVerifiedConceptQidsRetainNoAuthority =
  NativeQid369.verifiedConceptDoesNotCreateAuthority
