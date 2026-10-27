module DASHI.Unified.TOE369MaxCutKernelBidiTernaryExact where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

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
import DASHI.ComputerScience.TriadicFin27Byte256ABIExact as ABI
import DASHI.ComputerScience.TriadicScalarCompactCodecReferenceExact as CodecRef
import DASHI.ComputerScience.TriadicU8RuntimeOracleCrossRepoExact as HostU8
import DASHI.ComputerScience.TriadicCompiledScalarU8RuntimeExact as CompiledU8

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
-- Exact finite-27 codec BIDI normalization.
--
-- Reuse the canonical ABI functions and both inverse laws.  This pays the
-- finite Agda carrier BIDI coordinate only.  Runtime and device promotion
-- remain governed by the non-promotion theorems below.
------------------------------------------------------------------------

TernaryEncodedState : Set
TernaryEncodedState = CodecRef.Encoded3

TernaryState27 : Set
TernaryState27 = ABI.State27

toe27StateCode : TernaryEncodedState → TernaryState27
toe27StateCode = ABI.stateCode

toe27StateDecode : TernaryState27 → TernaryEncodedState
toe27StateDecode = ABI.stateDecode

toe27StateDecodeStateCode :
  (e : TernaryEncodedState) →
  toe27StateDecode (toe27StateCode e) ≡ e
toe27StateDecodeStateCode = ABI.stateDecode-stateCode

toe27StateCodeStateDecode :
  (i : TernaryState27) →
  toe27StateCode (toe27StateDecode i) ≡ i
toe27StateCodeStateDecode = ABI.stateCode-stateDecode

------------------------------------------------------------------------
-- Ternary-27 byte ABI / compiled host boundary.
--
-- Reuse the existing ABI and runtime owners. The finite codec and compiled
-- host byte are paid. Rust, CUDA, ROCm, device equivalence, and Agda-kernel
-- promotion remain unpaid. This is the normalized CFFI/kernel-BIDI boundary.
------------------------------------------------------------------------

toe27FiniteStateABIExact :
  ABI.finite27StateIndexPaid ABI.canonicalTriadicByteABIBoundary ≡ true
toe27FiniteStateABIExact = refl

toe27ByteCarrierABIExact :
  ABI.byteSizedFiniteCarrierPaid ABI.canonicalTriadicByteABIBoundary ≡ true
toe27ByteCarrierABIExact = refl

toe27CompiledHostU8Exact :
  CompiledU8.compiledHostU8Oracle CompiledU8.currentRuntimeRoadmapAdvance ≡ true
toe27CompiledHostU8Exact = refl

toe27RustBindingStillUnpaid :
  ABI.rustU8BindingPaid ABI.canonicalTriadicByteABIBoundary ≡ false
toe27RustBindingStillUnpaid = refl

toe27CUDABindingStillUnpaid :
  ABI.cudaUint8BindingPaid ABI.canonicalTriadicByteABIBoundary ≡ false
toe27CUDABindingStillUnpaid = refl

toe27ROCmBindingStillUnpaid :
  ABI.rocmUint8BindingPaid ABI.canonicalTriadicByteABIBoundary ≡ false
toe27ROCmBindingStillUnpaid = refl

toe27HostByteDoesNotCreateDeviceByte :
  HostU8.HostByteImpliesDeviceByte → ⊥
toe27HostByteDoesNotCreateDeviceByte =
  HostU8.hostByteDoesNotCreateDeviceByte

toe27RuntimeSourceDoesNotCreateKernelCertification :
  HostU8.RuntimeSourceImpliesKernelCertification → ⊥
toe27RuntimeSourceDoesNotCreateKernelCertification =
  HostU8.runtimeSourceDoesNotCreateKernelCertification

toe27CompilerSuccessDoesNotCreateAgdaKernelSuccess :
  CompiledU8.CompilerSuccessImpliesAgdaKernelSuccess → ⊥
toe27CompilerSuccessDoesNotCreateAgdaKernelSuccess =
  CompiledU8.compilerSuccessDoesNotCreateKernelSuccess

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
