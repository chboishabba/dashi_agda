module DASHI.Moonshine.Monster3BLinearIsotypicCurrentMaxCutExact where

------------------------------------------------------------------------
-- CURRENT MONSTER 3B LINEAR / ISOTYPIC MAX-CUT
--
-- This owner composes only already-owned repository facts and source receipts.
-- It deliberately distinguishes:
--
--   * model-side Schrodinger action/irreducibility/character arithmetic;
--   * generic semisimple/isotypic assembly source in companion Lean;
--   * selected-phase 12+78 CHARACTER-FAMILY occurrence;
--   * the still-unpaid SAME literal Monster linear carrier/action bindings.
--
-- In particular, neither 65610 = 90*729 nor 12+78=90 creates an isotypic
-- decomposition or an actual multiplicity action before the linear same-object
-- representation is paid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannIrreducibilityClosureExact as Irr
import DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptExact as Character
import DASHI.Moonshine.Monster3BWholeCharacterIsotypicAssemblyLeanReceiptExact as Isotypic
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
    actualTwelveSeventyEightActionIntertwinerPaid : Bool
    absoluteZetaOrientationPaid : Bool
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
  (Phase1278.selectedPhase8748CharacterFamilyPaid Phase1278.currentPhaseCharacterWeldFrontier)
  (Phase1278.selectedPhase56862CharacterFamilyPaid Phase1278.currentPhaseCharacterWeldFrontier)
  (Phase1278.selectedPhase65610DegreePaid Phase1278.currentPhaseCharacterWeldFrontier)
  (LinearHardening.paidWeightTwoWrapperAvailable LinearHardening.canonicalBoundary)
  (LinearHardening.paidLinearZetaWrapperAvailable LinearHardening.canonicalBoundary)
  false false false false false false false false false
  "First inhabit the proof-relevant weight-two Monster linear bridge and SAME literal zeta-eigenspace linear restriction. Then package the actual restricted E-action and explicit Schrodinger module in one representation theory and prove the simple-type classifier consumed by the generic isotypic assembly. Only after the resulting W_zeta|E ~= H_zeta^n same-object equivalence may 65610 = 90*729 lawfully force n=90. Next form S_zeta = Hom_E(H_zeta,W_zeta), prove evaluation/recovery and the actual 6.Suz action, and only then select any Fin90 basis required by downstream coordinate consumers. The 12+78 character-family occurrence is already paid; do not schedule further degree/occurrence discovery as if it were the representation action theorem."

-- Expose the two legacy frontiers that this max-cut supersedes as navigation
-- only; they are not theorem authority for the newly hardened payments.
linearZetaFrontier : LinearZeta.LinearZetaSectorFrontier
linearZetaFrontier = LinearZeta.currentLinearZetaSectorFrontier

irreducibilityBoundary : Irr.Boundary
irreducibilityBoundary = Irr.canonicalBoundary

characterBoundary : Character.Boundary
characterBoundary = Character.canonicalBoundary
