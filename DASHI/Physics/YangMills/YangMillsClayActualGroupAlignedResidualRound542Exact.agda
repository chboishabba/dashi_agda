{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayActualGroupAlignedResidualRound542Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND542: ACTUAL-GROUP-ALIGNED PREFERRED RESIDUAL
--
-- R540 made the measure-theory hypotheses complete (27 obligations).
-- R541 exposes one further all-G requirement:
--
--   the classified quantitative package used by G1 must be the SAME actual
--   compact-simple group/Lie algebra carried by the structural Clay index.
--
-- A family/classification tag alone is not a physical-group identification.
--
-- Preferred logical residual = 28.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayMeasureCompleteResidualRound540Exact as R540
import DASHI.Physics.YangMills.YangMillsActualGroupQuantitativeAlignmentRound541Exact as R541

data GroupAlignmentLeaf : Set where
  actualGroupQuantitativeAlignment : GroupAlignmentLeaf

groupAlignmentLeafLevel : GroupAlignmentLeaf → ProofLevel
groupAlignmentLeafLevel actualGroupQuantitativeAlignment =
  R541.literalRound541ActualGroupQuantitativeAlignmentLevel

groupAlignmentLeaves : List GroupAlignmentLeaf
groupAlignmentLeaves = actualGroupQuantitativeAlignment ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

add : Nat → Nat → Nat
add zero n = n
add (suc m) n = suc (add m n)

priorResidualCount : Nat
priorResidualCount = R540.residualLeafCount

groupAlignmentLeafCount : Nat
groupAlignmentLeafCount = listLength groupAlignmentLeaves

residualLeafCount : Nat
residualLeafCount =
  add priorResidualCount groupAlignmentLeafCount

classificationTagAloneIdentifiesActualGaugeGroup : Bool
classificationTagAloneIdentifiesActualGaugeGroup = false

actualCarrierAndLieOperationsMustAlign : Bool
actualCarrierAndLieOperationsMustAlign = true

su2ValidationCanPayActualGroupAlignment : Bool
su2ValidationCanPayActualGroupAlignment = false

opaqueEndpointSemanticLeavesRemaining : Bool
opaqueEndpointSemanticLeavesRemaining = false

round542ActualGroupAlignedResidualCompilerLevel : ProofLevel
round542ActualGroupAlignedResidualCompilerLevel = machineChecked
