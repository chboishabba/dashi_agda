module DASHI.Moonshine.Monster3BActualLinearIsotypicTerminalCompilerExact where

------------------------------------------------------------------------
-- ACTUAL MONSTER LINEAR / ISOTYPIC TERMINAL COMPILER
--
-- Reusable restriction, character, Schur, isotypic, copy-count and multiplicity
-- coordinate mathematics is no longer the Monster-specific frontier.
--
-- The Agda-native compatibility path below still accepts the historical paid
-- weight-two/zeta-linear wrappers, because Agda cannot import Lean theorem
-- authority.  Companion Lean now proves that, once the SAME actual invariant
-- linear subspaces / central linear operator are attached, restriction
-- linearity and inclusion intertwiners are compiler outputs.  Mathlib also
-- supplies Schur automatically once the SAME H_zeta is attached as a simple
-- finite-dimensional representation over the algebraically closed coefficient
-- field.
--
-- Therefore this packet no longer requests a free-standing Monster Schur
-- certificate.  It requests the more fundamental same-object simple-FDRep
-- attachment from which the companion theorem derives Schur.
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
import DASHI.Moonshine.Monster3BWholeCharacterIsotypicAssemblyLeanReceiptExact as Isotypic
import DASHI.Moonshine.Monster3BTwoIsotypicBlockAssemblyLeanReceiptExact as TwoBlock
import DASHI.Moonshine.Monster3BMultiplicitySchurCoordinatesLeanReceiptExact as Schur

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
    -- Agda-native proof authority for the historical APIs.  On the companion
    -- Lean path their zero/add/scalar restriction laws are compiler outputs from
    -- actual invariant-subspace data rather than independent mathematics.
    paidWeightTwoLinearBridge :
      Hardening.PaidWeightTwoLinearActionBridge weightLegacy

    paidLiteralZetaLinearRestriction :
      Hardening.PaidLinearSingleActionProducer zetaLegacy

    literalSchrodingerAttachment :
      Common.LiteralSchrodingerCommonTheoryAttachment theory

    actualSelectedConstituentAttachment :
      Common.ActualHZetaConstituentCommonTheoryAttachment theory

    ActualWholeSectorSimpleTypeClassifier : Set
    actualWholeSectorSimpleTypeClassifierWitness :
      ActualWholeSectorSimpleTypeClassifier

    ActualWholeSectorSemisimpleFinite : Set
    actualWholeSectorSemisimpleFiniteWitness :
      ActualWholeSectorSemisimpleFinite

    ActualWholeSectorFinrank65610 : Set
    actualWholeSectorFinrank65610Witness :
      ActualWholeSectorFinrank65610

    ActualHZetaFinrank729 : Set
    actualHZetaFinrank729Witness : ActualHZetaFinrank729

    -- Fundamental cross-kernel same-object attachment.  Once this is paid on
    -- the companion Lean representation, Mathlib's Schur theorem supplies the
    -- rank-one/scalar self-intertwiner fact; no separate scientific Schur input
    -- is required.
    ActualHZetaSimpleComplexFDRepSameObject : Set
    actualHZetaSimpleComplexFDRepSameObjectWitness :
      ActualHZetaSimpleComplexFDRepSameObject

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
------------------------------------------------------------------------

record ActualMultiplicityActionPayment : Set where
  field
    ActualSuzukiNormalizerActionOnSZeta : Set
    AbsoluteZetaOrientation : Set
    ActualTwelveSeventyEightActionIntertwiner : Set
    ActualTensorEvaluationEquivalence : Set

    actualSuzukiNormalizerActionOnSZetaWitness :
      ActualSuzukiNormalizerActionOnSZeta
    absoluteZetaOrientationWitness : AbsoluteZetaOrientation
    actualTwelveSeventyEightActionIntertwinerWitness :
      ActualTwelveSeventyEightActionIntertwiner
    actualTensorEvaluationEquivalenceWitness : ActualTensorEvaluationEquivalence

open ActualMultiplicityActionPayment public

------------------------------------------------------------------------
-- 4. Non-promotion boundaries.
------------------------------------------------------------------------

data CharacterFamilyCreatesActualInputPacket : Set where
data FinrankCreatesSimpleTypeClassifier : Set where
data SchurCoordinatesCreateNormalizerAction : Set where
data SourceRestrictionCompilerCreatesActualInvariantSubspace : Set where

characterFamilyDoesNotCreateActualInputPacket :
  CharacterFamilyCreatesActualInputPacket → ⊥
characterFamilyDoesNotCreateActualInputPacket ()

finrankDoesNotCreateSimpleTypeClassifier :
  FinrankCreatesSimpleTypeClassifier → ⊥
finrankDoesNotCreateSimpleTypeClassifier ()

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
    commonTheoryHZetaCompilerAvailable : Bool
    hZetaRecognitionCompilerClosesAfterPacket : Bool
    genericIsotypicTailSourceWritten : Bool
    postRecognitionNinetyCompilerSourceWritten : Bool
    complementaryTwelveSeventyEightTailSourceWritten : Bool
    genericSchurMultiplicityTailSourceWritten : Bool
    genericCoordinateEvaluationRecoverySourceWritten : Bool

    actualMonsterLinearInputPacketInhabitedHere : Bool
    actualWholeSectorSimpleTypeClassifierPaidHere : Bool
    actualWholeSectorIsotypicEquivalencePaidHere : Bool
    actualCopyCountNinetyPaidHere : Bool
    actualSuzukiNormalizerActionPaidHere : Bool
    absoluteZetaOrientationPaidHere : Bool
    actualTwelveSeventyEightActionIntertwinerPaidHere : Bool
    actualTensorEvaluationEquivalencePaidHere : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true
  (Restriction.restrictedRepresentationCompilerSourceWritten Restriction.canonicalBoundary)
  (Eigenspace.literalLinearEigenspaceCompilerSourceWritten Eigenspace.canonicalBoundary)
  true
  (SimpleSchur.simpleFDRepEndRankOneSourceWritten SimpleSchur.canonicalBoundary)
  false
  true true
  (Isotypic.classifierToIsotypicAssemblySourceWritten Isotypic.canonicalBoundary)
  (Isotypic.postRecognitionCopyCountCompilerSourceWritten Isotypic.canonicalBoundary)
  (TwoBlock.complementaryTwoBlockLinearAssemblySourceWritten TwoBlock.canonicalBoundary)
  (Schur.genericSchurCoordinateCompilerSourceWritten Schur.canonicalBoundary)
  (Schur.coordinateEvaluationRecoverySourceWritten Schur.canonicalBoundary)
  false false false false false false false false
