module DASHI.Moonshine.Monster3BActualLinearIsotypicTerminalCompilerExact where

------------------------------------------------------------------------
-- ACTUAL MONSTER LINEAR / ISOTYPIC TERMINAL COMPILER
--
-- The reusable representation-theory tail is no longer the research frontier.
-- This owner collapses the surviving Monster 3B debt into one proof-relevant
-- packet of SAME literal inputs.  In particular it consumes:
--
--   * a paid full weight-two linear bridge;
--   * a paid linear restriction to the SAME literal zeta eigensector;
--   * the literal Schrodinger model and one actual W_zeta|E constituent inside
--     one common irreducible-character theory;
--   * explicit whole-sector classifier/semisimplicity/finrank/Schur hypotheses
--     needed by the generic Lean isotypic and multiplicity compilers.
--
-- Once the common-theory attachments are present, H_zeta recognition and the
-- action intertwiner are compiled immediately by the existing Agda theorem.
-- Whole-sector finite-copy assembly, n=90, Schur Hom coordinates and coordinate
-- evaluation/recovery are already generic companion-Lean compilers; this file
-- records their availability but does not import Lean source as Agda proof.
--
-- The actual 6.Suz/normalizer action on S_zeta, absolute zeta orientation and a
-- tensor evaluation equivalence remain actual representation data rather than
-- consequences of cardinality or character-family occurrence.
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

    SameHZetaSchurScalarCertificate : Set
    sameHZetaSchurScalarCertificateWitness : SameHZetaSchurScalarCertificate

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

characterFamilyDoesNotCreateActualInputPacket :
  CharacterFamilyCreatesActualInputPacket → ⊥
characterFamilyDoesNotCreateActualInputPacket ()

finrankDoesNotCreateSimpleTypeClassifier :
  FinrankCreatesSimpleTypeClassifier → ⊥
finrankDoesNotCreateSimpleTypeClassifier ()

schurCoordinatesDoNotCreateNormalizerAction :
  SchurCoordinatesCreateNormalizerAction → ⊥
schurCoordinatesDoNotCreateNormalizerAction ()

------------------------------------------------------------------------
-- 5. Machine-readable terminal boundary.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    proofRelevantWeightTwoWrapperAvailable : Bool
    proofRelevantZetaLinearWrapperAvailable : Bool
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
  true true true true
  (Isotypic.classifierToIsotypicAssemblySourceWritten Isotypic.canonicalBoundary)
  (Isotypic.postRecognitionCopyCountCompilerSourceWritten Isotypic.canonicalBoundary)
  (TwoBlock.complementaryTwoBlockLinearAssemblySourceWritten TwoBlock.canonicalBoundary)
  (Schur.genericSchurCoordinateCompilerSourceWritten Schur.canonicalBoundary)
  (Schur.coordinateEvaluationRecoverySourceWritten Schur.canonicalBoundary)
  false false false false false false false false
