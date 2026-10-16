module DASHI.Moonshine.Monster3BActualLinearIsotypicTerminalCompilerExact where

------------------------------------------------------------------------
-- ACTUAL MONSTER LINEAR / ISOTYPIC TERMINAL COMPILER
--
-- Reusable restriction, character, Schur, Maschke, isotypic, copy-count,
-- multiplicity-coordinate, tensor, and two-simple character-determination
-- mathematics is no longer the Monster-specific frontier.
--
-- The live H_zeta/W_zeta character payment is one SAME-object transport:
--
--   chi(W_zeta|E) = 90 * chi(H_zeta)
--
-- on the actual linear FDRep objects.  Companion Lean then supplies the generic
-- isotypic/multiplicity consequences.
--
-- Likewise, once an actual 6.Suz/normalizer multiplicity action exists, the
-- historical `12+78` action decomposition does not require a separately
-- postulated intertwiner: the live two-simple character compiler derives its
-- representation multiplicities from a SAME-object selected-phase character
-- identity.  The actual normalizer action, absolute zeta orientation and that
-- same-object character transport remain the scientific inputs.
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
import DASHI.Moonshine.Monster3BCharacterDeterminationLiveLeanReceiptExact as Character12Plus78

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

    -- The true H_zeta/W_zeta character seam. The actual-kernel/class side owns
    -- the ninety-Heisenberg character statement; this witness transports that
    -- statement onto the SAME actual linear W_zeta|E and H_zeta FDReps.
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
-- 3. Remaining actual multiplicity-action payload.
--
-- Tensor evaluation and the abstract 12+78 representation decomposition are
-- compiler consequences after the same-object action/character inputs.  The
-- remaining payload is therefore the actual multiplicity action itself, phase
-- orientation, and transport of the source-paid selected-phase 12+78 character
-- onto that SAME action.
------------------------------------------------------------------------

record ActualMultiplicityActionPayment : Set where
  field
    ActualSuzukiNormalizerActionOnSZeta : Set
    AbsoluteZetaOrientation : Set
    ActualSelectedPhaseTwelveSeventyEightCharacterIsSameMultiplicityAction : Set

    actualSuzukiNormalizerActionOnSZetaWitness :
      ActualSuzukiNormalizerActionOnSZeta
    absoluteZetaOrientationWitness : AbsoluteZetaOrientation
    actualSelectedPhaseTwelveSeventyEightCharacterIsSameMultiplicityActionWitness :
      ActualSelectedPhaseTwelveSeventyEightCharacterIsSameMultiplicityAction

open ActualMultiplicityActionPayment public

------------------------------------------------------------------------
-- 4. Non-promotion boundaries.
------------------------------------------------------------------------

data CharacterFamilyCreatesActualInputPacket : Set where
data KernelCharacterCreatesLinearCharacterTransport : Set where
data CharacterOccurrenceCreatesMultiplicityAction : Set where
data SourceRestrictionCompilerCreatesActualInvariantSubspace : Set where

characterFamilyDoesNotCreateActualInputPacket :
  CharacterFamilyCreatesActualInputPacket → ⊥
characterFamilyDoesNotCreateActualInputPacket ()

kernelCharacterDoesNotCreateLinearCharacterTransport :
  KernelCharacterCreatesLinearCharacterTransport → ⊥
kernelCharacterDoesNotCreateLinearCharacterTransport ()

characterOccurrenceDoesNotCreateMultiplicityAction :
  CharacterOccurrenceCreatesMultiplicityAction → ⊥
characterOccurrenceDoesNotCreateMultiplicityAction ()

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
    twoSimpleCharacterMultiplicitySourceWritten : Bool
    twelveSeventyEightIntertwinerRemainsIndependentMonsterInput : Bool

    actualMonsterLinearInputPacketInhabitedHere : Bool
    actualWholeCharacterSameObjectTransportPaidHere : Bool
    actualWholeSectorIsotypicEquivalencePaidHere : Bool
    actualCopyCountNinetyPaidHere : Bool
    actualSuzukiNormalizerActionPaidHere : Bool
    absoluteZetaOrientationPaidHere : Bool
    actualSuzukiMultiplicityCharacterTransportPaidHere : Bool
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
  (Character12Plus78.twoSimpleCharacterMultiplicitySourceWritten Character12Plus78.canonicalBoundary)
  false
  false false false false false false false
