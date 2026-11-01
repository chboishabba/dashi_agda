{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayMeasureCompleteResidualRound540Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND540: MEASURE-COMPLETE PREFERRED RESIDUAL
--
-- R537 had the correct whole-projective extension shape but still inherited one
-- hidden hypothesis from the old "event algebra" naming convention:
-- the literal cylinder events must actually satisfy Boolean-algebra laws.
--
-- R538 also makes positivity explicit.
--
-- Therefore the complete preferred logical residual is:
--
--   13 prior source-analysis leaves
--    5 source/literal applicability attachments
--    2 rich structural/T1 source bundles
--    1 density->normalized finite-measure source map
--    5 C physical source packages
--    1 cylinder-event Boolean-algebra realization
--   -----------------------------------
--   27 total obligations
--
-- The count increases by one because a previously hidden measure-theory
-- hypothesis is now explicit.  No theorem regressed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayProjectivePreferredResidualRound537Exact as R537
import DASHI.Physics.YangMills.YangMillsCylinderEventBooleanAlgebraRound539Exact as R539

data MeasureCompletionLeaf : Set where
  cylinderEventBooleanAlgebra : MeasureCompletionLeaf

measureCompletionLeafLevel : MeasureCompletionLeaf → ProofLevel
measureCompletionLeafLevel cylinderEventBooleanAlgebra =
  R539.literalRound539CylinderEventBooleanAlgebraLevel

measureCompletionLeaves : List MeasureCompletionLeaf
measureCompletionLeaves = cylinderEventBooleanAlgebra ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

add : Nat → Nat → Nat
add zero n = n
add (suc m) n = suc (add m n)

priorResidualCount : Nat
priorResidualCount = R537.residualLeafCount

measureCompletionLeafCount : Nat
measureCompletionLeafCount = listLength measureCompletionLeaves

residualLeafCount : Nat
residualLeafCount =
  add priorResidualCount measureCompletionLeafCount

positiveCylinderProbabilityRequired : Bool
positiveCylinderProbabilityRequired = true

cylinderBooleanAlgebraRequired : Bool
cylinderBooleanAlgebraRequired = true

wholeProjectiveExtensionRequired : Bool
wholeProjectiveExtensionRequired = true

selectedSingleCutoffExtensionAllowedAsPreferredRoute : Bool
selectedSingleCutoffExtensionAllowedAsPreferredRoute = false

opaqueEndpointSemanticLeavesRemaining : Bool
opaqueEndpointSemanticLeavesRemaining = false

round540MeasureCompleteResidualCompilerLevel : ProofLevel
round540MeasureCompleteResidualCompilerLevel = machineChecked
