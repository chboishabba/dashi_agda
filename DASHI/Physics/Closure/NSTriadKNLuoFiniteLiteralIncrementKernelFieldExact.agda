module DASHI.Physics.Closure.NSTriadKNLuoFiniteLiteralIncrementKernelFieldExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions
-- of Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Close the finite complex literal increment-kernel field.  Pairwise spatial
-- increment coefficients are identified with the exact four-transform
-- multiplier, lifted to arbitrary finite folds, and partitioned by a total
-- three-way classifier into r_{p,1}, r_{p,2}, and the hard tail.  Ownership,
-- exclusivity, reconstruction, and all three whole-fold identities are
-- derived; none is accepted as an input field.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality as Eq using (cong₂)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNLuoFiniteComplexWeightedIncrementExact as Complex
import DASHI.Physics.Closure.NSTriadKNLuoFiniteComplexTranslationTensorConvolutionExact as Tensor
import DASHI.Physics.Closure.NSTriadKNLuoThreeWayPairPartitionExact as Piece

complexPairSum :
  ∀ {r} {F : C3.RealField r} {A : Set} →
  List A → (A → C3.Complex F) → C3.Complex F
complexPairSum {F = F} [] value = C3.complexZero F
complexPairSum (x ∷ xs) value =
  C3.complexAdd (value x) (complexPairSum xs value)

complexPairSumCongruent :
  ∀ {r} {F : C3.RealField r} {A : Set}
    (xs : List A) (left right : A → C3.Complex F) →
  ((x : A) → left x ≡ right x) →
  complexPairSum xs left ≡ complexPairSum xs right
complexPairSumCongruent [] left right pointwise = refl
complexPairSumCongruent (x ∷ xs) left right pointwise
  rewrite pointwise x
        | complexPairSumCongruent xs left right pointwise = refl

complexThreeWayPartitionReconstructsFold :
  ∀ {r} {F : C3.RealField r} {A : Set}
    (classify : A → Piece.PairPiece)
    (value : A → C3.Complex F)
    (xs : List A) →
  complexPairSum xs value
  ≡ C3.complexAdd
      (complexPairSum
        (Piece.rp1Pairs (Piece.partitionPairs classify xs)) value)
      (C3.complexAdd
        (complexPairSum
          (Piece.rp2Pairs (Piece.partitionPairs classify xs)) value)
        (complexPairSum
          (Piece.hardTailPairs (Piece.partitionPairs classify xs)) value))
complexThreeWayPartitionReconstructsFold {F = F} classify value []
  rewrite Algebra.complexAddZeroLeft (C3.complexZero F)
        | Algebra.complexAddZeroLeft (C3.complexZero F) = refl
complexThreeWayPartitionReconstructsFold {F = F}
  classify value (x ∷ xs)
  with classify x | Piece.partitionPairs classify xs
     | complexThreeWayPartitionReconstructsFold classify value xs
... | Piece.rp1Piece | Piece.partition low high tail | induction
  rewrite induction =
  R.solve 4
    (λ head a b c →
      (head R.⊕ (a R.⊕ (b R.⊕ c)))
      R.⊜ ((head R.⊕ a) R.⊕ (b R.⊕ c)))
    refl (value x)
    (complexPairSum low value)
    (complexPairSum high value)
    (complexPairSum tail value)
  where module R = Ring.Solver F
... | Piece.rp2Piece | Piece.partition low high tail | induction
  rewrite induction =
  R.solve 4
    (λ head a b c →
      (head R.⊕ (a R.⊕ (b R.⊕ c)))
      R.⊜ (a R.⊕ ((head R.⊕ b) R.⊕ c)))
    refl (value x)
    (complexPairSum low value)
    (complexPairSum high value)
    (complexPairSum tail value)
  where module R = Ring.Solver F
... | Piece.hardTailPiece | Piece.partition low high tail | induction
  rewrite induction =
  R.solve 4
    (λ head a b c →
      (head R.⊕ (a R.⊕ (b R.⊕ c)))
      R.⊜ (a R.⊕ (b R.⊕ (head R.⊕ c))))
    refl (value x)
    (complexPairSum low value)
    (complexPairSum high value)
    (complexPairSum tail value)
  where module R = Ring.Solver F

record FiniteLiteralIncrementKernel
    {r : Level}
    (F : C3.RealField r)
    (system : Complex.FiniteComplexCharacterSystem F)
    : Set (lsuc r) where
  field
    Pair : Set
    pairs : List Pair
    classify : Pair → Piece.PairPiece
    leftMode rightMode : Pair → Complex.Mode system
    leftCoefficient rightCoefficient :
      Complex.Mode system → C3.Complex F

open FiniteLiteralIncrementKernel public

literalPairContribution :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  Pair data → C3.Complex F
literalPairContribution {system = system} data pair =
  Tensor.finiteComplexIncrementTensorPairCoefficient
    system (leftCoefficient data) (rightCoefficient data)
    (leftMode data pair) (rightMode data pair)

multiplierPairContribution :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  Pair data → C3.Complex F
multiplierPairContribution {system = system} data pair =
  Tensor.finiteComplexMultiplierTensorPairCoefficient
    system (leftCoefficient data) (rightCoefficient data)
    (leftMode data pair) (rightMode data pair)

literalPairCoefficientIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system)
    (pair : Pair data) →
  literalPairContribution data pair
  ≡ multiplierPairContribution data pair
literalPairCoefficientIdentification {system = system} data pair =
  Tensor.finiteComplexTranslationTensorConvolutionIdentity
    system (leftCoefficient data) (rightCoefficient data)
    (leftMode data pair) (rightMode data pair)

literalWholeFoldIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system)
    (selected : List (Pair data)) →
  complexPairSum selected (literalPairContribution data)
  ≡ complexPairSum selected (multiplierPairContribution data)
literalWholeFoldIdentification data selected =
  complexPairSumCongruent selected
    (literalPairContribution data)
    (multiplierPairContribution data)
    (literalPairCoefficientIdentification data)

partitionAt :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  Piece.ThreeWayPartition (Pair data)
partitionAt data = Piece.partitionPairs (classify data) (pairs data)

rp1SelectedPairs rp2SelectedPairs hardTailSelectedPairs :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  List (Pair data)
rp1SelectedPairs data = Piece.rp1Pairs (partitionAt data)
rp2SelectedPairs data = Piece.rp2Pairs (partitionAt data)
hardTailSelectedPairs data = Piece.hardTailPairs (partitionAt data)

RP1Owned RP2Owned HardTailOwned :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  Pair data → Set
RP1Owned data pair = classify data pair ≡ Piece.rp1Piece
RP2Owned data pair = classify data pair ≡ Piece.rp2Piece
HardTailOwned data pair = classify data pair ≡ Piece.hardTailPiece

data PairOwnership
    {r : Level} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system)
    (pair : Pair data) : Set where
  ownsRP1 : RP1Owned data pair → PairOwnership data pair
  ownsRP2 : RP2Owned data pair → PairOwnership data pair
  ownsHardTail : HardTailOwned data pair → PairOwnership data pair

pairHasExactlyOneOwner :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system)
    (pair : Pair data) → PairOwnership data pair
pairHasExactlyOneOwner data pair with classify data pair
... | Piece.rp1Piece = ownsRP1 refl
... | Piece.rp2Piece = ownsRP2 refl
... | Piece.hardTailPiece = ownsHardTail refl

rp1AndRp2Impossible :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    {data : FiniteLiteralIncrementKernel F system}
    {pair : Pair data} →
  RP1Owned data pair → RP2Owned data pair → ⊥
rp1AndRp2Impossible refl ()

rp1AndHardTailImpossible :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    {data : FiniteLiteralIncrementKernel F system}
    {pair : Pair data} →
  RP1Owned data pair → HardTailOwned data pair → ⊥
rp1AndHardTailImpossible refl ()

rp2AndHardTailImpossible :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    {data : FiniteLiteralIncrementKernel F system}
    {pair : Pair data} →
  RP2Owned data pair → HardTailOwned data pair → ⊥
rp2AndHardTailImpossible refl ()

literalThreePieceReconstruction :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  complexPairSum (pairs data) (literalPairContribution data)
  ≡ C3.complexAdd
      (complexPairSum (rp1SelectedPairs data)
        (literalPairContribution data))
      (C3.complexAdd
        (complexPairSum (rp2SelectedPairs data)
          (literalPairContribution data))
        (complexPairSum (hardTailSelectedPairs data)
          (literalPairContribution data)))
literalThreePieceReconstruction data =
  complexThreeWayPartitionReconstructsFold
    (classify data) (literalPairContribution data) (pairs data)

rp1WholeFoldIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  complexPairSum (rp1SelectedPairs data) (literalPairContribution data)
  ≡ complexPairSum (rp1SelectedPairs data)
      (multiplierPairContribution data)
rp1WholeFoldIdentification data =
  literalWholeFoldIdentification data (rp1SelectedPairs data)

rp2WholeFoldIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  complexPairSum (rp2SelectedPairs data) (literalPairContribution data)
  ≡ complexPairSum (rp2SelectedPairs data)
      (multiplierPairContribution data)
rp2WholeFoldIdentification data =
  literalWholeFoldIdentification data (rp2SelectedPairs data)

tailWholeFoldIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  complexPairSum (hardTailSelectedPairs data)
      (literalPairContribution data)
  ≡ complexPairSum (hardTailSelectedPairs data)
      (multiplierPairContribution data)
tailWholeFoldIdentification data =
  literalWholeFoldIdentification data (hardTailSelectedPairs data)

literalIncrementKernelThreePieceMultiplierIdentity :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  complexPairSum (pairs data) (literalPairContribution data)
  ≡ C3.complexAdd
      (complexPairSum (rp1SelectedPairs data)
        (multiplierPairContribution data))
      (C3.complexAdd
        (complexPairSum (rp2SelectedPairs data)
          (multiplierPairContribution data))
        (complexPairSum (hardTailSelectedPairs data)
          (multiplierPairContribution data)))
literalIncrementKernelThreePieceMultiplierIdentity data =
  begin
    complexPairSum (pairs data) (literalPairContribution data)
  ≡⟨ literalThreePieceReconstruction data ⟩
    C3.complexAdd
      (complexPairSum (rp1SelectedPairs data)
        (literalPairContribution data))
      (C3.complexAdd
        (complexPairSum (rp2SelectedPairs data)
          (literalPairContribution data))
        (complexPairSum (hardTailSelectedPairs data)
          (literalPairContribution data)))
  ≡⟨ cong₂ C3.complexAdd
       (rp1WholeFoldIdentification data)
       (cong₂ C3.complexAdd
         (rp2WholeFoldIdentification data)
         (tailWholeFoldIdentification data)) ⟩
    C3.complexAdd
      (complexPairSum (rp1SelectedPairs data)
        (multiplierPairContribution data))
      (C3.complexAdd
        (complexPairSum (rp2SelectedPairs data)
          (multiplierPairContribution data))
        (complexPairSum (hardTailSelectedPairs data)
          (multiplierPairContribution data)))
  ∎
