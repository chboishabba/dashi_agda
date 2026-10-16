module DASHI.Moonshine.Monster3BLinearIsotypicCurrentMaxCutExact where

------------------------------------------------------------------------
-- CURRENT MONSTER 3B LINEAR / ISOTYPIC MAX-CUT
--
-- Reusable representation-theory plumbing is now separated from the actual
-- Monster same-object inputs.  The generic tail includes:
--
--   * semisimple one-type isotypic assembly;
--   * post-recognition copy-count cancellation;
--   * complementary 12/78 block assembly;
--   * Schur multiplicity coordinates Hom_G(H,H^n) ~= k^n;
--   * exact finite-copy coordinate evaluation/recovery.
--
-- None of those generic compilers constructs the literal Monster W_zeta/H_zeta
-- attachment, the actual simple-type classifier, the 6.Suz/normalizer action,
-- absolute zeta orientation or the 12+78 action intertwiner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannIrreducibilityClosureExact as Irr
import DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptExact as Character
import DASHI.Moonshine.Monster3BWholeCharacterIsotypicAssemblyLeanReceiptExact as Isotypic
import DASHI.Moonshine.Monster3BTwoIsotypicBlockAssemblyLeanReceiptExact as TwoBlock
import DASHI.Moonshine.Monster3BMultiplicitySchurCoordinatesLeanReceiptExact as Schur
import DASHI.Moonshine.Monster3BActualLinearIsotypicTerminalCompilerExact as Terminal
import DASHI.Moonshine.Monster3BLinearActionProofRelevantHardeningExact as LinearHardening
import DASHI.Wikimedia.IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact as Phase1278
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta

record Boundary : Set where
  constructor boundary
  field
    schrodingerActionOwned : Bool
    schrodingerIrreducibilityPaid : Bool
    schrodingerLiteralCharacterExecutablePaid : Bool
    genericIsotypicAssemblySourceWritten : Bool
    postRecognitionCopyCountCompilerSourceWritten : Bool
    genericTwoBlockAssemblySourceWritten : Bool
    genericSchurMultiplicityCoordinatesSourceWritten : Bool
    genericCoordinateEvaluationRecoverySourceWritten : Bool
    actualInputPacketTyped : Bool
    hZetaRecognitionClosesAfterActualPacket : Bool

    selectedPhaseTwelveCharacterFamilyPaid : Bool
    selectedPhaseSeventyEightCharacterFamilyPaid : Bool
    selectedPhaseTotalDegree65610Paid : Bool
    weightTwoProofRelevantWrapperAvailable : Bool
    zetaLinearProofRelevantWrapperAvailable : Bool

    actualPaidWeightTwoLinearBridgeInhabited : Bool
    actualPaidLinearZetaRestrictionInhabited : Bool
    actualMonsterSimpleTypeClassifierPaid : Bool
    actualWholeSectorIsotypicLinearEquivalencePaid : Bool
    actualCopyCountNinetyPaidAfterRecognition : Bool
    actualMultiplicityHomEvaluationPaid : Bool
    actualSuzukiNormalizerActionPaid : Bool
    actualTwelveSeventyEightActionIntertwinerPaid : Bool
    absoluteZetaOrientationPaid : Bool
    actualTensorEvaluationEquivalencePaid : Bool
    fin90BasisNeededBeforeRepresentationRecognition : Bool

    nextResidual : String
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true
  true
  true
  (Isotypic.classifierToIsotypicAssemblySourceWritten Isotypic.canonicalBoundary)
  (Isotypic.postRecognitionCopyCountCompilerSourceWritten Isotypic.canonicalBoundary)
  (TwoBlock.complementaryTwoBlockLinearAssemblySourceWritten TwoBlock.canonicalBoundary)
  (Schur.genericSchurCoordinateCompilerSourceWritten Schur.canonicalBoundary)
  (Schur.coordinateEvaluationRecoverySourceWritten Schur.canonicalBoundary)
  true
  (Terminal.hZetaRecognitionCompilerClosesAfterPacket Terminal.canonicalBoundary)
  (Phase1278.selectedPhase8748CharacterFamilyPaid Phase1278.currentPhaseCharacterWeldFrontier)
  (Phase1278.selectedPhase56862CharacterFamilyPaid Phase1278.currentPhaseCharacterWeldFrontier)
  (Phase1278.selectedPhase65610DegreePaid Phase1278.currentPhaseCharacterWeldFrontier)
  (LinearHardening.paidWeightTwoWrapperAvailable LinearHardening.canonicalBoundary)
  (LinearHardening.paidLinearZetaWrapperAvailable LinearHardening.canonicalBoundary)
  false false false false false false false false false false false
  "The reusable tail is exhausted at source level. Supply one ActualMonsterLinearInputPacket: a paid full weight-two linear bridge, the SAME literal zeta-sector linear restriction, common-theory attachments for the literal Schrodinger model and an actual W_zeta|E constituent, and proof-relevant whole-sector classifier/semisimplicity/finrank/Schur inputs. The existing Agda compiler then closes H_zeta recognition/action intertwining; companion Lean compilers assemble W_zeta|E ~= H_zeta^n, force n=90 post-recognition, and identify the multiplicity Hom with 90 scalar coordinates with exact coordinate recovery. Remaining actual representation data are the 6.Suz/normalizer action on S_zeta, absolute zeta orientation, the 12+78 action intertwiner and any desired tensor evaluation equivalence. Fin90 remains downstream coordinates, never a pre-recognition representation surrogate."

linearZetaFrontier : LinearZeta.LinearZetaSectorFrontier
linearZetaFrontier = LinearZeta.currentLinearZetaSectorFrontier

irreducibilityBoundary : Irr.Boundary
irreducibilityBoundary = Irr.canonicalBoundary

characterBoundary : Character.Boundary
characterBoundary = Character.canonicalBoundary
