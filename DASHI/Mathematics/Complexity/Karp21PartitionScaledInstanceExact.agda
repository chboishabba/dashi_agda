module DASHI.Mathematics.Complexity.Karp21PartitionScaledInstanceExact where

------------------------------------------------------------------------
-- Karp PARTITION -> MAX CUT: actual UNLABELLED signed integer source.
-- For integer edge weights 4*c_i*c_j and threshold T*T, the E20
-- threshold equivalence no longer requires a ceiling operation.
--
-- This module proves the existential source/target witness iff at the
-- fully typed list-of-integers and Boolean-label level. No search,
-- SAT oracle or hidden solution data is used by the instance map.
-- It does not claim the explicit binary graph encoder/machine cost.
--
-- Original: Richard M. Karp (1972), DOI 10.1007/978-1-4684-2001-2_9.
-- DASHI construction: integer scaling as an equivalent reduction,
-- reusing the signed complete-graph objective and existing square order.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer as Int using (ℤ; +_; _+_; _*_; _≤_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21PartitionCutQuadraticExact as Cut
import DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact as Scaled

-- Selection carries one Boolean choice for each *input element*.
-- Unlike an index-free Boolean function this preserves multiplicity
-- of identical signed source values and stays finite by construction.
Selection : List ℤ → Set
Selection [] = ⊤
Selection (_ ∷ xs) = Bool × Selection xs

annotate : (parts : List ℤ) → Selection parts →
  List (ℤ × Bool)
annotate [] tt = []
annotate (x ∷ xs) (bit , tail) =
  (x , bit) ∷ annotate xs tail

sourceTotal : List ℤ → ℤ
sourceTotal [] = + 0
sourceTotal (x ∷ xs) = x + sourceTotal xs

taggedTotalMatchesSource :
  (parts : List ℤ) (choice : Selection parts) →
  Cut.signedTotal (annotate parts choice) ≡ sourceTotal parts
taggedTotalMatchesSource [] tt = refl
taggedTotalMatchesSource (x ∷ xs) (bit , tail) =
  cong (λ remainder → x + remainder)
    (taggedTotalMatchesSource xs tail)

-- These are genuine existential YES predicates: a witness must include
-- all Boolean labels, and its per-instance objective is an actual
-- complete-graph weighted crossing-edge sum.
PartitionYES : List ℤ → Set
PartitionYES parts =
  Σ (Selection parts)
    (λ choice →
      Cut.leftTotal (annotate parts choice) ≡
      Cut.rightTotal (annotate parts choice))

ScaledCutYES : List ℤ → Set
ScaledCutYES parts =
  Σ (Selection parts)
    (λ choice →
      (sourceTotal parts * sourceTotal parts) ≤
        (Int.+ 4) * Cut.completeGraphCut (annotate parts choice))

partitionWitnessToScaledCutWitness :
  (parts : List ℤ) → PartitionYES parts → ScaledCutYES parts
partitionWitnessToScaledCutWitness parts (choice , balance) =
  choice ,
    subst
      (λ threshold →
        threshold ≤
          (Int.+ 4) * Cut.completeGraphCut (annotate parts choice))
      (cong (λ t → t * t)
        (taggedTotalMatchesSource parts choice))
      (Scaled.balancedImpliesScaledThreshold
        (annotate parts choice) balance)

scaledCutWitnessToPartitionWitness :
  (parts : List ℤ) → ScaledCutYES parts → PartitionYES parts
scaledCutWitnessToPartitionWitness parts (choice , accepted) =
  choice ,
    Scaled.scaledThresholdImpliesBalanced
      (annotate parts choice)
      (subst
        (λ threshold →
          threshold ≤
            (Int.+ 4) * Cut.completeGraphCut (annotate parts choice))
        (sym (cong (λ t → t * t)
          (taggedTotalMatchesSource parts choice)))
        accepted)

signedPartitionScaledCutInstanceIff :
  (parts : List ℤ) →
  PR.Iff (PartitionYES parts) (ScaledCutYES parts)
signedPartitionScaledCutInstanceIff parts =
  PR.iff
    (partitionWitnessToScaledCutWitness parts)
    (scaledCutWitnessToPartitionWitness parts)

-- The all-false assignment witnesses every zero-total instance.
chooseFalse : (parts : List ℤ) → Selection parts
chooseFalse [] = tt
chooseFalse (x ∷ xs) = false , chooseFalse xs

allFalseHasZeroLeft :
  (parts : List ℤ) →
  Cut.leftTotal (annotate parts (chooseFalse parts)) ≡ + 0
allFalseHasZeroLeft [] = refl
allFalseHasZeroLeft (x ∷ xs) =
  allFalseHasZeroLeft xs

allFalseHasFullRight :
  (parts : List ℤ) →
  Cut.rightTotal (annotate parts (chooseFalse parts)) ≡
  sourceTotal parts
allFalseHasFullRight [] = refl
allFalseHasFullRight (x ∷ xs) =
  cong (λ tail → x + tail) (allFalseHasFullRight xs)

zeroTotalPartitionYES :
  (parts : List ℤ) →
  sourceTotal parts ≡ + 0 →
  PartitionYES parts
zeroTotalPartitionYES parts totalZero =
  chooseFalse parts ,
    trans
      (allFalseHasZeroLeft parts)
      (sym
        (trans (allFalseHasFullRight parts) totalZero))


------------------------------------------------------------------------
-- Total input-level branch selection. A zero-total partition is always
-- accepted; the corresponding literal Karp MaxCut instance cannot have
-- the zero threshold, so it becomes a fixed 2-vertex, unit-edge YES
-- graph. The remaining branch is the scaled complete weighted graph.
--
-- This Target is an algebraic graph-construction representation: a
-- concrete byte-level GraphInstance serializer with polynomial clock is
-- *not* produced by this record. It must be proved separately before
-- promotion to the Karp MAX CUT polynomial reduction in PR.
------------------------------------------------------------------------

open import Relation.Nullary.Decidable.Core using (yes; no)

data CutTarget : Set where
  unitEdgeYes : CutTarget
  scaledComplete : List ℤ → CutTarget

cutTargetAccepts : CutTarget → Set
cutTargetAccepts unitEdgeYes = ⊤
cutTargetAccepts (scaledComplete parts) = ScaledCutYES parts

partitionToScaledCutTarget : List ℤ → CutTarget
partitionToScaledCutTarget parts
  with Int._≟_ (sourceTotal parts) (+ 0)
... | yes _ = unitEdgeYes
... | no _ = scaledComplete parts

sourcePartitionIffConstructedTarget :
  (parts : List ℤ) →
  PR.Iff
    (PartitionYES parts)
    (cutTargetAccepts (partitionToScaledCutTarget parts))
sourcePartitionIffConstructedTarget parts
  with Int._≟_ (sourceTotal parts) (+ 0)
... | yes totalZero =
  PR.iff
    (λ _ → tt)
    (λ _ → zeroTotalPartitionYES parts totalZero)
... | no _ =
  signedPartitionScaledCutInstanceIff parts
