{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPeriodicSegmentCommutationRound162Exact where

------------------------------------------------------------------------
-- ROUND162 BIDI / CROSS-POLLINATION:
-- PERIODIC SEGMENT COMMUTATION IS REPOSITORY ARITHMETIC, NOT SOURCE INPUT
--
-- R150/R152/R158 still carried `PeriodicSegmentCommutation n` as an input.
-- But the repository already proves cyclic successor/predecessor are mutual
-- inverses on the literal finite torus.  Coordinate updates therefore commute:
-- different axes commute definitionally, while opposite steps on one axis both
-- reduce to the same coordinate by the existing inverse laws.
--
-- We lift this from one signed step, to one step past a word, to arbitrary word
-- translations, and finally to the straight segment words used by CMP98/CMP109.
-- Hence translation commutation is no longer a physical/source-facing receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (CyclicIndex; zeroᵢ; sucᵢ; pair)
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Adjacency
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Closure
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word

------------------------------------------------------------------------
-- Same-coordinate signed steps commute because +/- are mutual inverses.
------------------------------------------------------------------------

coordinateStepsCommute :
  ∀ {n} (coordinate : CyclicIndex (suc n))
    (left right : Bool) →
  Adjacency.stepCoordinate right
    (Adjacency.stepCoordinate left coordinate)
  ≡ Adjacency.stepCoordinate left
      (Adjacency.stepCoordinate right coordinate)
coordinateStepsCommute coordinate false false = refl
coordinateStepsCommute coordinate true true = refl
coordinateStepsCommute coordinate false true =
  trans
    (Closure.successorAfterPredecessor coordinate)
    (sym (Closure.predecessorAfterSuccessor coordinate))
coordinateStepsCommute coordinate true false =
  trans
    (Closure.predecessorAfterSuccessor coordinate)
    (sym (Closure.successorAfterPredecessor coordinate))

------------------------------------------------------------------------
-- Literal four-axis update commutation.
------------------------------------------------------------------------

signedStepCommutes :
  ∀ {n} (block : Blocks.PeriodicBlock n)
    (left right : Word.SignedAxis4) →
  Bond.walkStep (Bond.walkStep block left) right
  ≡ Bond.walkStep (Bond.walkStep block right) left
signedStepCommutes
  (pair (pair c0 c1) (pair c2 c3))
  (pair zeroᵢ left) (pair zeroᵢ right) =
  Closure.blockExtensionality
    (coordinateStepsCommute c0 left right) refl refl refl
signedStepCommutes block
  (pair zeroᵢ left) (pair (sucᵢ zeroᵢ) right) = refl
signedStepCommutes block
  (pair zeroᵢ left) (pair (sucᵢ (sucᵢ zeroᵢ)) right) = refl
signedStepCommutes block
  (pair zeroᵢ left) (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) right) = refl

signedStepCommutes block
  (pair (sucᵢ zeroᵢ) left) (pair zeroᵢ right) = refl
signedStepCommutes
  (pair (pair c0 c1) (pair c2 c3))
  (pair (sucᵢ zeroᵢ) left) (pair (sucᵢ zeroᵢ) right) =
  Closure.blockExtensionality
    refl (coordinateStepsCommute c1 left right) refl refl
signedStepCommutes block
  (pair (sucᵢ zeroᵢ) left) (pair (sucᵢ (sucᵢ zeroᵢ)) right) = refl
signedStepCommutes block
  (pair (sucᵢ zeroᵢ) left)
  (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) right) = refl

signedStepCommutes block
  (pair (sucᵢ (sucᵢ zeroᵢ)) left) (pair zeroᵢ right) = refl
signedStepCommutes block
  (pair (sucᵢ (sucᵢ zeroᵢ)) left) (pair (sucᵢ zeroᵢ) right) = refl
signedStepCommutes
  (pair (pair c0 c1) (pair c2 c3))
  (pair (sucᵢ (sucᵢ zeroᵢ)) left)
  (pair (sucᵢ (sucᵢ zeroᵢ)) right) =
  Closure.blockExtensionality
    refl refl (coordinateStepsCommute c2 left right) refl
signedStepCommutes block
  (pair (sucᵢ (sucᵢ zeroᵢ)) left)
  (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) right) = refl

signedStepCommutes block
  (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) left) (pair zeroᵢ right) = refl
signedStepCommutes block
  (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) left)
  (pair (sucᵢ zeroᵢ) right) = refl
signedStepCommutes block
  (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) left)
  (pair (sucᵢ (sucᵢ zeroᵢ)) right) = refl
signedStepCommutes
  (pair (pair c0 c1) (pair c2 c3))
  (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) left)
  (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) right) =
  Closure.blockExtensionality
    refl refl refl (coordinateStepsCommute c3 left right)

------------------------------------------------------------------------
-- Lift pairwise step commutation to arbitrary translation words.
------------------------------------------------------------------------

stepCommutesWithWalk :
  ∀ {n} (block : Blocks.PeriodicBlock n)
    (direction : Word.SignedAxis4)
    (directions : List Word.SignedAxis4) →
  Bond.walk (Bond.walkStep block direction) directions
  ≡ Bond.walkStep (Bond.walk block directions) direction
stepCommutesWithWalk block direction [] = refl
stepCommutesWithWalk block direction (other ∷ directions) =
  trans
    (cong
      (λ start → Bond.walk start directions)
      (signedStepCommutes block direction other))
    (stepCommutesWithWalk
      (Bond.walkStep block other) direction directions)

walkWordsCommute :
  ∀ {n} (block : Blocks.PeriodicBlock n)
    (left right : List Word.SignedAxis4) →
  Bond.walk (Bond.walk block left) right
  ≡ Bond.walk (Bond.walk block right) left
walkWordsCommute block [] right = refl
walkWordsCommute block (direction ∷ directions) right =
  trans
    (walkWordsCommute
      (Bond.walkStep block direction) directions right)
    (cong
      (λ start → Bond.walk start directions)
      (stepCommutesWithWalk block direction right))

------------------------------------------------------------------------
-- Exact owner consumed by R150/R152/R158.
------------------------------------------------------------------------

periodicSegmentCommutation : ∀ n → Embed.PeriodicSegmentCommutation n
periodicSegmentCommutation n = record
  { Embed.PeriodicSegmentCommutation.translationsCommute =
      λ point left right →
        walkWordsCommute point
          (Periodic.segmentWord left)
          (Periodic.segmentWord right)
  }

periodicSingleStepCommutationRound162Level : ProofLevel
periodicSingleStepCommutationRound162Level = machineChecked

periodicWordTranslationCommutationRound162Level : ProofLevel
periodicWordTranslationCommutationRound162Level = machineChecked

periodicSegmentCommutationRound162Level : ProofLevel
periodicSegmentCommutationRound162Level = machineChecked

-- This discharges the old `physicalPeriodicCoordinateTranslationCommutationInputsLevel`
-- role for the repository's literal periodic torus carrier.  No source theorem is
-- needed for coordinate-translation commutation itself.
