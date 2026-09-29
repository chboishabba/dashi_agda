{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayConcreteSemanticsResidualRound521Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND521: RESIDUAL AFTER CONCRETE STRUCTURAL/T1/T4 SEMANTICS
--                         + EXTENSIONALIZED REPRESENTED OS0/OS5
--
-- Starting from R518:
--
--   * R519 makes all eight T4 endpoint meanings constructor/same-object facts
--     once the canonical C source exists;
--   * R520 removes the two represented OS extensionality assumptions by using
--     the least pointwise-extensional closure of the canonical OS predicates.
--
-- The concrete-semantics route therefore has NO remaining opaque endpoint
-- predicate leaves.
--
-- Honest residual:
--   15 source-analysis leaves
--   16 source<->literal attachment leaves
--    2 rich source-bundle realizations (all-G structure + literal T1 family)
--   -----------------------------------------------------------------------
--   33 total
--
-- The C-source package consumed by R519 is not added as a nineteenth hidden
-- object: its physical contents are exactly the C leaves already present in
-- the attachment/analysis queues.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayGoal1ExactResidualMaxCutRound496Exact as R496
import DASHI.Physics.YangMills.YangMillsClayPostQuantitativeResidualRound515Exact as R515
import DASHI.Physics.YangMills.YangMillsClayPostStructuralT1ResidualRound518Exact as R518
import DASHI.Physics.YangMills.YangMillsConcreteT4SemanticsRound519Exact as R519
import DASHI.Physics.YangMills.YangMillsExtensionalizedRepresentedOS05Round520Exact as R520

sourceAnalysisLeaves : List R496.ResidualLeaf
sourceAnalysisLeaves = R515.sourceAnalysisLeaves

sourceLiteralAttachmentLeaves : List R496.ResidualLeaf
sourceLiteralAttachmentLeaves =
    R496.aFiniteEuclideanSameObjectAttachment
  ∷ R496.aFiniteBosonicSameObjectAttachment
  ∷ R496.aFiniteWilsonRPSameObjectAttachment
  ∷ R496.a2BetaMarkGeneratedHistoryShell
  ∷ R496.a3StressDensityIsLiteralFiniteMeasure
  ∷ R496.a3SourceOSIsLiteralSchwinger
  ∷ R496.a3CylinderEventIndicatorSemantics
  ∷ R496.a3CylinderExpectationIntegralIdentification
  ∷ R496.a45QuantitativeFiniteExpectationAttachment
  ∷ R496.c1CurvatureGaugeLocalSemantics
  ∷ R496.c2PhysicalRemainderIsCompositeTail
  ∷ R496.c3OneStepAFRGIdentification
  ∷ R496.c4FiniteStressInsertionIsCMP119Local
  ∷ R496.c4StressCompletionIsCompletedMarkedStress
  ∷ R496.c4CompletedStressIsClayStress
  ∷ R496.c4DensityAnchoredLaneInstantiation
  ∷ []

addedSourceLeaves : List R518.AddedSourceLeaf
addedSourceLeaves = R518.addedSourceLeaves

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

sourceAnalysisLeafCount : Nat
sourceAnalysisLeafCount = listLength sourceAnalysisLeaves

sourceLiteralAttachmentLeafCount : Nat
sourceLiteralAttachmentLeafCount = listLength sourceLiteralAttachmentLeaves

addedSourceLeafCount : Nat
addedSourceLeafCount = listLength addedSourceLeaves

endpointSemanticLeafCount : Nat
endpointSemanticLeafCount = zero

residualLeafCount : Nat
residualLeafCount =
  add sourceAnalysisLeafCount
    (add sourceLiteralAttachmentLeafCount addedSourceLeafCount)
  where
  add : Nat → Nat → Nat
  add zero n = n
  add (suc m) n = suc (add m n)

representedRegularityExtensionalityStillResidual : Bool
representedRegularityExtensionalityStillResidual = false

representedGrowthExtensionalityStillResidual : Bool
representedGrowthExtensionalityStillResidual = false

opaqueEndpointSemanticLeafStillResidual : Bool
opaqueEndpointSemanticLeafStillResidual = false

round521ConcreteSemanticsResidualCompilerLevel : ProofLevel
round521ConcreteSemanticsResidualCompilerLevel = machineChecked

round521T4EndpointCompilerLevel : ProofLevel
round521T4EndpointCompilerLevel =
  R519.round519T4EndpointInterpretationLevel

round521RepresentedOSClosureCompilerLevel : ProofLevel
round521RepresentedOSClosureCompilerLevel =
  R520.round520ExtensionalClosureCompilerLevel
