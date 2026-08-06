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
... | Piece.rp1Piece | Piece.partition low high tail | induction =
  let
    h : C3.Complex F
    h = value x
    a : C3.Complex F
    a = complexPairSum low value
    b : C3.Complex F
    b = complexPairSum high value
    c : C3.Complex F
    c = complexPairSum tail value
  in
  R.solve 4
    (λ h′ a′ b′ c′ →
      (h′ R.⊕ (a′ R.⊕ (b′ R.⊕ c′)))
      R.⊜ ((h′ R.⊕ a′) R.⊕ (b′ R.⊕ c′)))
    induction h a b c
  where module R = Ring.Solver F
... | Piece.rp2Piece | Piece.partition low high tail | induction =
  let
    h : C3.Complex F
    h = value x
    a : C3.Complex F
    a = complexPairSum low value
    b : C3.Complex F
    b = complexPairSum high value
    c : C3.Complex F
    c = complexPairSum tail value
  in
  R.solve 4
    (λ h′ a′ b′ c′ →
      (h′ R.⊕ (a′ R.⊕ (b′ R.⊕ c′)))
      R.⊜ (a′ R.⊕ ((h′ R.⊕ b′) R.⊕ c′)))
    induction h a b c
  where module R = Ring.Solver F
... | Piece.hardTailPiece | Piece.partition low high tail | induction =
  let
    h : C3.Complex F
    h = value x
    a : C3.Complex F
    a = complexPairSum low value
    b : C3.Complex F
    b = complexPairSum high value
    c : C3.Complex F
    c = complexPairSum tail value
  in
  R.solve 4
    (λ h′ a′ b′ c′ →
      (h′ R.⊕ (a′ R.⊕ (b′ R.⊕ c′)))
      R.⊜ (a′ R.⊕ (b′ R.⊕ (h′ R.⊕ c′))))
    induction h a b c
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
    (kernel : FiniteLiteralIncrementKernel F system) →
  FiniteLiteralIncrementKernel.Pair kernel → C3.Complex F
literalPairContribution {system = system} kernel pair =
  Tensor.finiteComplexIncrementTensorPairCoefficient
    system (leftCoefficient kernel) (rightCoefficient kernel)
    (leftMode kernel pair) (rightMode kernel pair)

multiplierPairContribution :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system) →
  FiniteLiteralIncrementKernel.Pair kernel → C3.Complex F
multiplierPairContribution {system = system} kernel pair =
  Tensor.finiteComplexMultiplierTensorPairCoefficient
    system (leftCoefficient kernel) (rightCoefficient kernel)
    (leftMode kernel pair) (rightMode kernel pair)

literalPairCoefficientIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system)
    (pair : FiniteLiteralIncrementKernel.Pair kernel) →
  literalPairContribution kernel pair
  ≡ multiplierPairContribution kernel pair
literalPairCoefficientIdentification {system = system} kernel pair =
  Tensor.finiteComplexTranslationTensorConvolutionIdentity
    system (leftCoefficient kernel) (rightCoefficient kernel)
    (leftMode kernel pair) (rightMode kernel pair)

literalWholeFoldIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system)
    (selected : List (FiniteLiteralIncrementKernel.Pair kernel)) →
  complexPairSum selected (literalPairContribution kernel)
  ≡ complexPairSum selected (multiplierPairContribution kernel)
literalWholeFoldIdentification kernel selected =
  complexPairSumCongruent selected
    (literalPairContribution kernel)
    (multiplierPairContribution kernel)
    (literalPairCoefficientIdentification kernel)

partitionAt :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system) →
  Piece.ThreeWayPartition (FiniteLiteralIncrementKernel.Pair kernel)
partitionAt kernel = Piece.partitionPairs (classify kernel) (pairs kernel)

rp1SelectedPairs rp2SelectedPairs hardTailSelectedPairs :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system) →
  List (FiniteLiteralIncrementKernel.Pair kernel)
rp1SelectedPairs kernel = Piece.rp1Pairs (partitionAt kernel)
rp2SelectedPairs kernel = Piece.rp2Pairs (partitionAt kernel)
hardTailSelectedPairs kernel = Piece.hardTailPairs (partitionAt kernel)

rp1Owned rp2Owned hardTailOwned :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system) →
  FiniteLiteralIncrementKernel.Pair kernel → Set
rp1Owned kernel pair = classify kernel pair ≡ Piece.rp1Piece
rp2Owned kernel pair = classify kernel pair ≡ Piece.rp2Piece
hardTailOwned kernel pair = classify kernel pair ≡ Piece.hardTailPiece

data PairOwnership
    {r : Level} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system)
    (pair : FiniteLiteralIncrementKernel.Pair kernel) : Set where
  ownsRP1 : rp1Owned kernel pair → PairOwnership kernel pair
  ownsRP2 : rp2Owned kernel pair → PairOwnership kernel pair
  ownsHardTail : hardTailOwned kernel pair → PairOwnership kernel pair

pairHasExactlyOneOwner :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system)
    (pair : FiniteLiteralIncrementKernel.Pair kernel) → PairOwnership kernel pair
pairHasExactlyOneOwner kernel pair with classify kernel pair
... | Piece.rp1Piece = ownsRP1 refl
... | Piece.rp2Piece = ownsRP2 refl
... | Piece.hardTailPiece = ownsHardTail refl

rp1AndRp2Impossible :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    {kernel : FiniteLiteralIncrementKernel F system}
    {pair : FiniteLiteralIncrementKernel.Pair kernel} →
  rp1Owned kernel pair → rp2Owned kernel pair → ⊥
rp1AndRp2Impossible refl ()

rp1AndHardTailImpossible :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    {kernel : FiniteLiteralIncrementKernel F system}
    {pair : FiniteLiteralIncrementKernel.Pair kernel} →
  rp1Owned kernel pair → hardTailOwned kernel pair → ⊥
rp1AndHardTailImpossible refl ()

rp2AndHardTailImpossible :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    {kernel : FiniteLiteralIncrementKernel F system}
    {pair : FiniteLiteralIncrementKernel.Pair kernel} →
  rp2Owned kernel pair → hardTailOwned kernel pair → ⊥
rp2AndHardTailImpossible refl ()

literalThreePieceReconstruction :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system) →
  complexPairSum (pairs kernel) (literalPairContribution kernel)
  ≡ C3.complexAdd
      (complexPairSum (rp1SelectedPairs kernel)
        (literalPairContribution kernel))
      (C3.complexAdd
        (complexPairSum (rp2SelectedPairs kernel)
          (literalPairContribution kernel))
        (complexPairSum (hardTailSelectedPairs kernel)
          (literalPairContribution kernel)))
literalThreePieceReconstruction kernel =
  complexThreeWayPartitionReconstructsFold
    (classify kernel) (literalPairContribution kernel) (pairs kernel)

rp1WholeFoldIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system) →
  complexPairSum (rp1SelectedPairs kernel) (literalPairContribution kernel)
  ≡ complexPairSum (rp1SelectedPairs kernel)
      (multiplierPairContribution kernel)
rp1WholeFoldIdentification kernel =
  literalWholeFoldIdentification kernel (rp1SelectedPairs kernel)

rp2WholeFoldIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system) →
  complexPairSum (rp2SelectedPairs kernel) (literalPairContribution kernel)
  ≡ complexPairSum (rp2SelectedPairs kernel)
      (multiplierPairContribution kernel)
rp2WholeFoldIdentification kernel =
  literalWholeFoldIdentification kernel (rp2SelectedPairs kernel)

tailWholeFoldIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system) →
  complexPairSum (hardTailSelectedPairs kernel)
      (literalPairContribution kernel)
  ≡ complexPairSum (hardTailSelectedPairs kernel)
      (multiplierPairContribution kernel)
tailWholeFoldIdentification kernel =
  literalWholeFoldIdentification kernel (hardTailSelectedPairs kernel)

literalIncrementKernelThreePieceMultiplierIdentity :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (kernel : FiniteLiteralIncrementKernel F system) →
  complexPairSum (pairs kernel) (literalPairContribution kernel)
  ≡ C3.complexAdd
      (complexPairSum (rp1SelectedPairs kernel)
        (multiplierPairContribution kernel))
      (C3.complexAdd
        (complexPairSum (rp2SelectedPairs kernel)
          (multiplierPairContribution kernel))
        (complexPairSum (hardTailSelectedPairs kernel)
          (multiplierPairContribution kernel)))
literalIncrementKernelThreePieceMultiplierIdentity kernel =
  begin
    complexPairSum (pairs kernel) (literalPairContribution kernel)
  ≡⟨ literalThreePieceReconstruction kernel ⟩
    C3.complexAdd
      (complexPairSum (rp1SelectedPairs kernel)
        (literalPairContribution kernel))
      (C3.complexAdd
        (complexPairSum (rp2SelectedPairs kernel)
          (literalPairContribution kernel))
        (complexPairSum (hardTailSelectedPairs kernel)
          (literalPairContribution kernel)))
  ≡⟨ cong₂ C3.complexAdd
       (rp1WholeFoldIdentification kernel)
       (cong₂ C3.complexAdd
         (rp2WholeFoldIdentification kernel)
         (tailWholeFoldIdentification kernel)) ⟩
    C3.complexAdd
      (complexPairSum (rp1SelectedPairs kernel)
        (multiplierPairContribution kernel))
      (C3.complexAdd
        (complexPairSum (rp2SelectedPairs kernel)
          (multiplierPairContribution kernel))
        (complexPairSum (hardTailSelectedPairs kernel)
          (multiplierPairContribution kernel)))
  ∎
