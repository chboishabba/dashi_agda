module DASHI.Moonshine.Monster3BActualLinearIsotypicTerminalCompilerExact where

------------------------------------------------------------------------
-- ACTUAL MONSTER LINEAR / ISOTYPIC TERMINAL COMPILER
--
-- Reusable restriction, character, Schur, Maschke, isotypic, copy-count,
-- multiplicity-coordinate, tensor, two-simple character determination and the
-- underlying normalizer action on equivariant Hom are no longer independent
-- Monster-specific mathematics.
--
-- The live H_zeta/W_zeta character payment is one SAME-object transport:
--
--   chi(W_zeta|E) = 90 * chi(H_zeta)
--
-- on the actual linear FDRep objects.
--
-- For the multiplicity representation, companion Lean now source-writes the
-- canonical normalizer action on Hom_E(H_zeta,W_zeta):
--
--   n.f = rho_W(n) o f o rho_H(n)^(-1).
--
-- Therefore one should not separately postulate an action on a third S_zeta
-- carrier.  The remaining actual inputs are the same-object normalizer lifts on
-- H_zeta and W_zeta, their projective/cocycle compatibility, absolute zeta
-- orientation, and transport of the source-paid selected-phase 12+78 character
-- onto that induced Hom action.
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
import DASHI.Moonshine.Monster3BNormalizerHomActionLeanReceiptExact as HomAction

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
    ActualKernelNinetyCharacterIsSameLinearWholeCharacter : Set
    actualKernelNinetyCharacterIsSameLinearWholeCharacterWitness :
      ActualKernelNinetyCharacterIsSameLinearWholeCharacter
open ActualMonsterLinearInputPacket public

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
-- Remaining actual multiplicity-action payload.
------------------------------------------------------------------------

record ActualMultiplicityActionPayment : Set where
  field
    ActualNormalizerLiftsOnHZetaAndWZeta : Set
    ActualProjectiveCocycleLawsOnSameLifts : Set
    AbsoluteZetaOrientation : Set
    ActualSelectedPhaseTwelveSeventyEightCharacterIsSameInducedHomAction : Set

    actualNormalizerLiftsOnHZetaAndWZetaWitness :
      ActualNormalizerLiftsOnHZetaAndWZeta
    actualProjectiveCocycleLawsOnSameLiftsWitness :
      ActualProjectiveCocycleLawsOnSameLifts
    absoluteZetaOrientationWitness : AbsoluteZetaOrientation
    actualSelectedPhaseTwelveSeventyEightCharacterIsSameInducedHomActionWitness :
      ActualSelectedPhaseTwelveSeventyEightCharacterIsSameInducedHomAction
open ActualMultiplicityActionPayment public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data CharacterFamilyCreatesActualInputPacket : Set where
data KernelCharacterCreatesLinearCharacterTransport : Set where
data CharacterOccurrenceCreatesNormalizerLifts : Set where
data SourceHomCompilerCreatesActualNormalizerLifts : Set where

characterFamilyDoesNotCreateActualInputPacket :
  CharacterFamilyCreatesActualInputPacket → ⊥
characterFamilyDoesNotCreateActualInputPacket ()
kernelCharacterDoesNotCreateLinearCharacterTransport :
  KernelCharacterCreatesLinearCharacterTransport → ⊥
kernelCharacterDoesNotCreateLinearCharacterTransport ()
characterOccurrenceDoesNotCreateNormalizerLifts :
  CharacterOccurrenceCreatesNormalizerLifts → ⊥
characterOccurrenceDoesNotCreateNormalizerLifts ()
sourceHomCompilerDoesNotCreateActualNormalizerLifts :
  SourceHomCompilerCreatesActualNormalizerLifts → ⊥
sourceHomCompilerDoesNotCreateActualNormalizerLifts ()

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
    inducedHomNormalizerActionSourceWritten : Bool
    independentMultiplicityNormalizerActionRemainsInput : Bool

    actualMonsterLinearInputPacketInhabitedHere : Bool
    actualWholeCharacterSameObjectTransportPaidHere : Bool
    actualWholeSectorIsotypicEquivalencePaidHere : Bool
    actualCopyCountNinetyPaidHere : Bool
    actualNormalizerLiftsPaidHere : Bool
    actualProjectiveCocycleLawsPaidHere : Bool
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
  (HomAction.inducedHomNormalizerActionSourceWritten HomAction.canonicalBoundary)
  false
  false false false false false false false false
