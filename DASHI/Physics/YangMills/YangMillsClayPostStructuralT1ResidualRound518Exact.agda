{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPostStructuralT1ResidualRound518Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND518: RESIDUAL AFTER STRUCTURAL + T1 CONCRETE SEMANTICS
--
-- R517 replaces the three structural endpoint predicates by:
--   * one proof-bearing all-group CompactSimpleLieGroup source bundle;
--   * a constructor-selected Euclidean-R4 spacetime.
--
-- R516 replaces ten opaque T1 endpoint predicates by the actual finite/RG
-- source objects.  Published finite Euclidean/RP applicability were already
-- counted in R515.  The extra source realization that must remain visible is
-- the literal beta-driven CMP119/CMP122 Section-2 density/bounds family.
--
-- Therefore endpoint vocabulary shrinks from 21 to the eight T4 predicates,
-- but two rich source inputs replace the removed opaque fields.
--
-- Residual accounting:
--   15 source-analysis leaves inherited from R515
--   18 source<->literal attachments inherited from R515
--    8 T4 endpoint-semantic leaves
--    2 new explicit source-bundle realizations
--   --------------------------------------------
--   43 honest residual obligations
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayGoal1ExactResidualMaxCutRound496Exact as R496
import DASHI.Physics.YangMills.YangMillsClayPostQuantitativeResidualRound515Exact as R515
import DASHI.Physics.YangMills.YangMillsConcreteT1SemanticsRound516Exact as R516
import DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Exact as R517

data AddedSourceLeaf : Set where
  allGroupCompactSimpleWitness : AddedSourceLeaf
  literalCMP119Section2Family : AddedSourceLeaf

addedSourceLeafLevel : AddedSourceLeaf → ProofLevel
addedSourceLeafLevel allGroupCompactSimpleWitness =
  R517.literalRound517AllGroupCompactSimpleSourceLevel
addedSourceLeafLevel literalCMP119Section2Family =
  R516.literalRound516ConcreteT1SourceBundleLevel

sourceAnalysisLeaves : List R496.ResidualLeaf
sourceAnalysisLeaves = R515.sourceAnalysisLeaves

sourceLiteralAttachmentLeaves : List R496.ResidualLeaf
sourceLiteralAttachmentLeaves = R515.sourceLiteralAttachmentLeaves

remainingEndpointSemanticLeaves : List R496.ResidualLeaf
remainingEndpointSemanticLeaves =
    R496.t4GaugeInvariantLocalObservableSemantics
  ∷ R496.t4CurvatureCorrespondenceSemantics
  ∷ R496.t4CurvatureGaugeInvariantSemantics
  ∷ R496.t4CurvatureLocalitySemantics
  ∷ R496.t4ShortDistanceAFSemantics
  ∷ R496.t4StressTensorAndOPESemantics
  ∷ R496.t4PhysicalOPECoefficientSemantics
  ∷ R496.t4PhysicalOPERemainderSemantics
  ∷ []

addedSourceLeaves : List AddedSourceLeaf
addedSourceLeaves =
    allGroupCompactSimpleWitness
  ∷ literalCMP119Section2Family
  ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

sourceAnalysisLeafCount : Nat
sourceAnalysisLeafCount = listLength sourceAnalysisLeaves

sourceLiteralAttachmentLeafCount : Nat
sourceLiteralAttachmentLeafCount = listLength sourceLiteralAttachmentLeaves

endpointSemanticLeafCount : Nat
endpointSemanticLeafCount = listLength remainingEndpointSemanticLeaves

addedSourceLeafCount : Nat
addedSourceLeafCount = listLength addedSourceLeaves

residualLeafCount : Nat
residualLeafCount =
  add sourceAnalysisLeafCount
    (add sourceLiteralAttachmentLeafCount
      (add endpointSemanticLeafCount addedSourceLeafCount))
  where
  add : Nat → Nat → Nat
  add zero n = n
  add (suc m) n = suc (add m n)

structuralEndpointPredicatesStillResidual : Bool
structuralEndpointPredicatesStillResidual = false

t1EndpointPredicatesStillResidual : Bool
t1EndpointPredicatesStillResidual = false

t4EndpointPredicatesStillResidual : Bool
t4EndpointPredicatesStillResidual = true

round518PostStructuralT1ResidualCompilerLevel : ProofLevel
round518PostStructuralT1ResidualCompilerLevel = machineChecked
