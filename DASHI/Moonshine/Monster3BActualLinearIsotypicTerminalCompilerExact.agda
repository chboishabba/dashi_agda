module DASHI.Moonshine.Monster3BActualLinearIsotypicTerminalCompilerExact where

------------------------------------------------------------------------
-- ACTUAL MONSTER LINEAR / ISOTYPIC TERMINAL COMPILER
--
-- Reusable restriction, character, Schur, Maschke, isotypic, copy-count,
-- multiplicity-coordinate and finite-copy tensor mathematics is no longer the
-- Monster-specific frontier.
--
-- The live character/isotypy payment is one SAME-object transport: attach the
-- actual linear W_zeta|E sector and H_zeta to the common finite-dimensional
-- representation theory and prove that the already certified actual-kernel
-- character identity is literally
--
--   chi(W_zeta|E) = 90 * chi(H_zeta)
--
-- on those SAME linear representation objects.
--
-- Companion Lean then supplies the generic FDRep/module adapter, simple-source
-- classifier, Maschke semisimplicity, dimension ratio, isotypic finite-copy
-- assembly, Schur multiplicity coordinates and the canonical post-isotypy
-- tensor equivalence. Agda-native historical linear wrappers remain explicit
-- because Lean theorem authority is not imported across kernels.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta
import DASHI.Moonshine.Monster3BLinearActionProofRelevantHardeningExact as Hardening
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannUniquenessBidiExact as Uniqueness
import DASHI.Moonshine.Monster3BCommonRepresentationTransportExact as Common
import DASHI.Moonshine.Monster3BHZetaCharacterTransportCompilerExact as HCompiler
import DASHI.Moonshine.Monster3BProofRelevantRecognitionHardeningExact as Recognition
import DASHI.Moonshine.Monster3BInvariantRestrictionLeanReceiptExact as Restriction
import DASHI.Moonshine.Monster3BLinearEigenspaceRestrictionLeanReceiptExact as Eigenspace
import DASHI.Moonshine.Monster3BSchurFromSimpleFDRepLeanReceiptExact as SimpleSchur
import DASHI.Moonshine.Monster3BWholeCharacterLiveTailLeanReceiptExact as WholeCharacter
import DASHI.Moonshine.Monster3BWholeCharacterIsotypicAssemblyLeanReceiptExact as Isotypic
import DASHI.Moonshine.Monster3BTwoIsotypicBlockAssemblyLeanReceiptExact as TwoBlock
import DASHI.Moonshine.Monster3BMultiplicitySchurCoordinatesLeanReceiptExact as Schur
import DASHI.Moonshine.Monster3BTensorFiniteCopiesLeanReceiptExact as Tensor

------------------------------------------------------------------------
-- 1. One exact actual-input packet.
------------------------------------------------------------------------

record ActualMonsterLinearInputPacket
    {Monster K : Set}
    {bridge}
    (weightLegacy : WeightTwo.WeightTwoLinearActionBridge {Monster} {K} bridge)
    (zetaLegacy : LinearZeta.LinearSingleActionProducer)
    (theory : Uniqueness.IrreducibleCharacterDetermination)
    : Setω where
  field
    paidWeightTwoLinearBridge :
      Hardening.PaidWeightTwoLinearActionBridge weightLegacy

    paidLiteralZetaLinearRestriction :
      Hardening.PaidLinearSingleActionProducer zetaLegacy

    literalSchrodingerAttachment :
      Common.LiteralSchrodingerCommonTheoryAttachment theory

    actualSelectedConstituentAttachment :
      Common.ActualHZetaConstituentCommonTheoryAttachment theory

    ActualWholeWZetaRestrictedFDRepSameObject : Set
    actualWholeWZetaRestrictedFDRepSameObjectWitness :
      ActualWholeWZetaRestrictedFDRepSameObject

    ActualHZetaSimpleComplexFDRepSameObject : Set
    actualHZetaSimpleComplexFDRepSameObjectWitness :
      ActualHZetaSimpleComplexFDRepSameObject

    -- The true character/isotypy seam. The actual-kernel/class side already
    -- owns the ninety-Heisenberg character statement; this witness transports
    -- that statement onto the SAME actual linear W_zeta|E and H_zeta FDReps.
    ActualKernelNinetyCharacterIsSameLinearWholeCharacter : Set
    actualKernelNinetyCharacterIsSameLinearWholeCharacterWitness :
      ActualKernelNinetyCharacterIsSameLinearWholeCharacter

open ActualMonsterLinearInputPacket public

------------------------------------------------------------------------
-- 2. H_zeta recognition is no longer an independent leaf after the packet.
------------------------------------------------------------------------

compileActualPaidHZetaRecognition :
  ∀ {Monster K bridge}
    (weightLegacy : WeightTwo.WeightTwoLinearActionBridge {Monster} {K} bridge)
    (zetaLegacy : LinearZeta.LinearSingleActionProducer)
    (theory : Uniqueness.IrreducibleCharacterDetermination) →
  (packet : ActualMonsterLinearInputPacket weightLegacy zetaLegacy theory) →
  Recognition.PaidSchrodingerIsActualHZeta
    (HCompiler.compiledLegacyHZetaRecognition
      theory
      (Common.compileCharacterTransport theory
        (literalSchrodingerAttachment packet)
        (actualSelectedConstituentAttachment packet)))
compileActualPaidHZetaRecognition weightLegacy zetaLegacy theory packet =
  Common.compilePaidHZetaRecognition theory
    (literalSchrodingerAttachment packet)
    (actualSelectedConstituentAttachment packet)

------------------------------------------------------------------------
-- 3. Remaining actual post-recognition representation payload.
--
-- Tensor evaluation has been removed from this packet: after actual isotypy and
-- Schur multiplicity coordinates, companion Lean derives the canonical tensor
-- finite-copy equivalence using mathlib `TensorProduct.piScalarRight`.
------------------------------------------------------------------------

record ActualMultiplicityActionPayment : Set where
  field
    ActualSuzukiNormalizerActionOnSZeta : Set
    AbsoluteZetaOrientation : Set
    ActualTwelveSeventyEightActionIntertwiner : Set

    actualSuzukiNormalizerActionOnSZetaWitness :
      ActualSuzukiNormalizerActionOnSZeta
    absoluteZetaOrientationWitness : AbsoluteZetaOrientation
    actualTwelveSeventyEightActionIntertwinerWitness :
      ActualTwelveSeventyEightActionIntertwiner

open ActualMultiplicityActionPayment public

------------------------------------------------------------------------
-- 4. Non-promotion boundaries.
------------------------------------------------------------------------

data CharacterFamilyCreatesActualInputPacket : Set where
data KernelCharacterCreatesLinearCharacterTransport : Set where
data SchurCoordinatesCreateNormalizerAction : Set where
data SourceRestrictionCompilerCreatesActualInvariantSubspace : Set where

characterFamilyDoesNotCreateActualInputPacket :
  CharacterFamilyCreatesActualInputPacket → ⊥
characterFamilyDoesNotCreateActualInputPacket ()

kernelCharacterDoesNotCreateLinearCharacterTransport :
  KernelCharacterCreatesLinearCharacterTransport → ⊥
kernelCharacterDoesNotCreateLinearCharacterTransport ()

schurCoordinatesDoNotCreateNormalizerAction :
  SchurCoordinatesCreateNormalizerAction → ⊥
schurCoordinatesDoNotCreateNormalizerAction ()

sourceRestrictionCompilerDoesNotCreateActualInvariantSubspace :
  SourceRestrictionCompilerCreatesActualInvariantSubspace → ⊥
sourceRestrictionCompilerDoesNotCreateActualInvariantSubspace ()

------------------------------------------------------------------------
-- 5. Machine-readable terminal boundary.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    proofRelevantWeightTwoWrapperAvailable : Bool
    proofRelevantZetaLinearWrapperAvailable : Bool
    invariantRestrictionCompilerSourceWritten : Bool
    linearEigenspaceCompilerSourceWritten : Bool
    restrictionLinearityIsCompilerOutputOnLeanPath : Bool
    simpleFDRepSchurSourceWritten : Bool
    schurRemainsIndependentMonsterInput : Bool
    fdrepModuleAdapterSourceWritten : Bool
    wholeCharacterSimpleClassifierSourceWritten : Bool
    maschkeSemisimplicitySourceWritten : Bool
    characterDimensionRatioSourceWritten : Bool
    arbitrarySimpleClassifierRemainsIndependentMonsterInput : Bool
    semisimplicityRemainsIndependentMonsterInput : Bool
    separateFinrankRatioRemainsIndependentMonsterInput : Bool
    commonTheoryHZetaCompilerAvailable : Bool
    hZetaRecognitionCompilerClosesAfterPacket : Bool
    genericIsotypicTailSourceWritten : Bool
    postRecognitionNinetyCompilerSourceWritten : Bool
    complementaryTwelveSeventyEightTailSourceWritten : Bool
    genericSchurMultiplicityTailSourceWritten : Bool
    genericCoordinateEvaluationRecoverySourceWritten : Bool
    postIsotypyTensorEquivalenceSourceWritten : Bool
    tensorEquivalenceRemainsIndependentMonsterInput : Bool

    actualMonsterLinearInputPacketInhabitedHere : Bool
    actualWholeCharacterSameObjectTransportPaidHere : Bool
    actualWholeSectorIsotypicEquivalencePaidHere : Bool
    actualCopyCountNinetyPaidHere : Bool
    actualSuzukiNormalizerActionPaidHere : Bool
    absoluteZetaOrientationPaidHere : Bool
    actualTwelveSeventyEightActionIntertwinerPaidHere : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true
  (Restriction.restrictedRepresentationCompilerSourceWritten Restriction.canonicalBoundary)
  (Eigenspace.literalLinearEigenspaceCompilerSourceWritten Eigenspace.canonicalBoundary)
  true
  (SimpleSchur.simpleFDRepEndRankOneSourceWritten SimpleSchur.canonicalBoundary)
  false
  (WholeCharacter.fdrepModuleAdapterSourceWritten WholeCharacter.canonicalBoundary)
  (WholeCharacter.wholeCharacterSimpleSourceClassifierSourceWritten WholeCharacter.canonicalBoundary)
  (WholeCharacter.maschkeSemisimplicitySourceWritten WholeCharacter.canonicalBoundary)
  (WholeCharacter.characterCoefficientDimensionRatioSourceWritten WholeCharacter.canonicalBoundary)
  false false false
  true true
  (Isotypic.classifierToIsotypicAssemblySourceWritten Isotypic.canonicalBoundary)
  (Isotypic.postRecognitionCopyCountCompilerSourceWritten Isotypic.canonicalBoundary)
  (TwoBlock.complementaryTwoBlockLinearAssemblySourceWritten TwoBlock.canonicalBoundary)
  (Schur.genericSchurCoordinateCompilerSourceWritten Schur.canonicalBoundary)
  (Schur.coordinateEvaluationRecoverySourceWritten Schur.canonicalBoundary)
  (Tensor.postIsotypyTensorEquivalenceSourceWritten Tensor.canonicalBoundary)
  false
  false false false false false false false
