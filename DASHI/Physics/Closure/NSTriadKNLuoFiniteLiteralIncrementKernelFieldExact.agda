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
-- Close the complete finite complex version of the literal increment-kernel
-- Fourier field.  The source contribution for a pair is the finite spatial
-- weighted increment tensor coefficient.  The target contribution is the
-- exact four-transform multiplier coefficient.  Their equality is proved
-- pairwise and lifted to arbitrary finite pair folds.
--
-- A total three-way classifier then partitions the complete pair list into
-- r_{p,1}, r_{p,2}, and hard-tail pieces.  The code proves reconstruction,
-- pair ownership, pairwise exclusivity, and the final three-piece multiplier
-- identity.  No whole-fold equality or boundary receipt is accepted as a
-- field.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong₂; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNLuoFiniteComplexWeightedIncrementExact as Complex
import DASHI.Physics.Closure.NSTriadKNLuoFiniteComplexTranslationTensorConvolutionExact as Tensor
import DASHI.Physics.Closure.NSTriadKNLuoThreeWayPairPartitionExact as Piece

complexPairSum :
  ∀ {r} {F : C3.RealField r} {Pair : Set} →
  List Pair → (Pair → C3.Complex F) → C3.Complex F
complexPairSum {F = F} [] contribution = C3.complexZero F
complexPairSum (pair ∷ pairs) contribution =
  C3.complexAdd
    (contribution pair)
    (complexPairSum pairs contribution)

complexPairSumCongruent :
  ∀ {r} {F : C3.RealField r} {Pair : Set}
    (pairs : List Pair)
    (source target : Pair → C3.Complex F) →
  ((pair : Pair) → source pair ≡ target pair) →
  complexPairSum pairs source ≡ complexPairSum pairs target
complexPairSumCongruent [] source target pointwise = refl
complexPairSumCongruent (pair ∷ pairs) source target pointwise
  rewrite pointwise pair
        | complexPairSumCongruent pairs source target pointwise = refl

complexThreeWayPartitionReconstructsFold :
  ∀ {r} {F : C3.RealField r} {Pair : Set}
    (classify : Pair → Piece.PairPiece)
    (contribution : Pair → C3.Complex F)
    (pairs : List Pair) →
  complexPairSum pairs contribution
  ≡ C3.complexAdd
      (complexPairSum
        (Piece.rp1Pairs (Piece.partitionPairs classify pairs))
        contribution)
      (C3.complexAdd
        (complexPairSum
          (Piece.rp2Pairs (Piece.partitionPairs classify pairs))
          contribution)
        (complexPairSum
          (Piece.hardTailPairs (Piece.partitionPairs classify pairs))
          contribution))
complexThreeWayPartitionReconstructsFold {F = F}
  classify contribution []
  rewrite Algebra.complexAddZeroLeft (C3.complexZero F)
        | Algebra.complexAddZeroLeft (C3.complexZero F) = refl
complexThreeWayPartitionReconstructsFold {F = F}
  classify contribution (pair ∷ pairs)
  with classify pair | Piece.partitionPairs classify pairs
     | complexThreeWayPartitionReconstructsFold
         classify contribution pairs
... | Piece.rp1Piece | Piece.partition rp1 rp2 tail | induction
  rewrite induction =
  R.solve 4
    (λ head low high tailValue →
      (head R.⊕ (low R.⊕ (high R.⊕ tailValue)))
      R.⊜
      ((head R.⊕ low) R.⊕ (high R.⊕ tailValue)))
    refl
    (contribution pair)
    (complexPairSum rp1 contribution)
    (complexPairSum rp2 contribution)
    (complexPairSum tail contribution)
  where module R = Ring.Solver F
... | Piece.rp2Piece | Piece.partition rp1 rp2 tail | induction
  rewrite induction =
  R.solve 4
    (λ head low high tailValue →
      (head R.⊕ (low R.⊕ (high R.⊕ tailValue)))
      R.⊜
      (low R.⊕ ((head R.⊕ high) R.⊕ tailValue)))
    refl
    (contribution pair)
    (complexPairSum rp1 contribution)
    (complexPairSum rp2 contribution)
    (complexPairSum tail contribution)
  where module R = Ring.Solver F
... | Piece.hardTailPiece | Piece.partition rp1 rp2 tail | induction
  rewrite induction =
  R.solve 4
    (λ head low high tailValue →
      (head R.⊕ (low R.⊕ (high R.⊕ tailValue)))
      R.⊜
      (low R.⊕ (high R.⊕ (head R.⊕ tailValue))))
    refl
    (contribution pair)
    (complexPairSum rp1 contribution)
    (complexPairSum rp2 contribution)
    (complexPairSum tail contribution)
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
    {system : Complex.FiniteComplexCharacterSystem F} →
  FiniteLiteralIncrementKernel F system →
  Pair → C3.Complex F
literalPairContribution {system = system} data pair =
  Tensor.finiteComplexIncrementTensorPairCoefficient
    system
    (leftCoefficient data)
    (rightCoefficient data)
    (leftMode data pair)
    (rightMode data pair)

multiplierPairContribution :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F} →
  FiniteLiteralIncrementKernel F system →
  Pair → C3.Complex F
multiplierPairContribution {system = system} data pair =
  Tensor.finiteComplexMultiplierTensorPairCoefficient
    system
    (leftCoefficient data)
    (rightCoefficient data)
    (leftMode data pair)
    (rightMode data pair)

literalPairCoefficientIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system)
    (pair : Pair data) →
  literalPairContribution data pair
  ≡ multiplierPairContribution data pair
literalPairCoefficientIdentification {system = system} data pair =
  Tensor.finiteComplexTranslationTensorConvolutionIdentity
    system
    (leftCoefficient data)
    (rightCoefficient data)
    (leftMode data pair)
    (rightMode data pair)

literalWholeFoldIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system)
    (selectedPairs : List (Pair data)) →
  complexPairSum selectedPairs (literalPairContribution data)
  ≡ complexPairSum selectedPairs (multiplierPairContribution data)
literalWholeFoldIdentification data selectedPairs =
  complexPairSumCongruent
    selectedPairs
    (literalPairContribution data)
    (multiplierPairContribution data)
    (literalPairCoefficientIdentification data)

partitionAt :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F} →
  FiniteLiteralIncrementKernel F system →
  Piece.ThreeWayPartition Pair
partitionAt data = Piece.partitionPairs (classify data) (pairs data)

rp1SelectedPairs :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  List (Pair data)
rp1SelectedPairs data = Piece.rp1Pairs (partitionAt data)

rp2SelectedPairs :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  List (Pair data)
rp2SelectedPairs data = Piece.rp2Pairs (partitionAt data)

hardTailSelectedPairs :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  List (Pair data)
hardTailSelectedPairs data = Piece.hardTailPairs (partitionAt data)

RP1Owned :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  Pair data → Set
RP1Owned data pair = classify data pair ≡ Piece.rp1Piece

RP2Owned :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  Pair data → Set
RP2Owned data pair = classify data pair ≡ Piece.rp2Piece

HardTailOwned :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  Pair data → Set
HardTailOwned data pair = classify data pair ≡ Piece.hardTailPiece

data PairOwnership
    {r : Level}
    {F : C3.RealField r}
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
    (pair : Pair data) →
  PairOwnership data pair
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
      (complexPairSum
        (rp1SelectedPairs data)
        (literalPairContribution data))
      (C3.complexAdd
        (complexPairSum
          (rp2SelectedPairs data)
          (literalPairContribution data))
        (complexPairSum
          (hardTailSelectedPairs data)
          (literalPairContribution data)))
literalThreePieceReconstruction data =
  complexThreeWayPartitionReconstructsFold
    (classify data)
    (literalPairContribution data)
    (pairs data)

rp1WholeFoldIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  complexPairSum
    (rp1SelectedPairs data)
    (literalPairContribution data)
  ≡ complexPairSum
      (rp1SelectedPairs data)
      (multiplierPairContribution data)
rp1WholeFoldIdentification data =
  literalWholeFoldIdentification data (rp1SelectedPairs data)

rp2WholeFoldIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  complexPairSum
    (rp2SelectedPairs data)
    (literalPairContribution data)
  ≡ complexPairSum
      (rp2SelectedPairs data)
      (multiplierPairContribution data)
rp2WholeFoldIdentification data =
  literalWholeFoldIdentification data (rp2SelectedPairs data)

tailWholeFoldIdentification :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  complexPairSum
    (hardTailSelectedPairs data)
    (literalPairContribution data)
  ≡ complexPairSum
      (hardTailSelectedPairs data)
      (multiplierPairContribution data)
tailWholeFoldIdentification data =
  literalWholeFoldIdentification data (hardTailSelectedPairs data)

literalIncrementKernelThreePieceMultiplierIdentity :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    (data : FiniteLiteralIncrementKernel F system) →
  complexPairSum (pairs data) (literalPairContribution data)
  ≡ C3.complexAdd
      (complexPairSum
        (rp1SelectedPairs data)
        (multiplierPairContribution data))
      (C3.complexAdd
        (complexPairSum
          (rp2SelectedPairs data)
          (multiplierPairContribution data))
        (complexPairSum
          (hardTailSelectedPairs data)
          (multiplierPairContribution data)))
literalIncrementKernelThreePieceMultiplierIdentity data =
  begin
    complexPairSum (pairs data) (literalPairContribution data)
  ≡⟨ literalThreePieceReconstruction data ⟩
    C3.complexAdd
      (complexPairSum
        (rp1SelectedPairs data)
        (literalPairContribution data))
      (C3.complexAdd
        (complexPairSum
          (rp2SelectedPairs data)
          (literalPairContribution data))
        (complexPairSum
          (hardTailSelectedPairs data)
          (literalPairContribution data)))
  ≡⟨ cong₂ C3.complexAdd
       (rp1WholeFoldIdentification data)
       (cong₂ C3.complexAdd
         (rp2WholeFoldIdentification data)
         (tailWholeFoldIdentification data)) ⟩
    C3.complexAdd
      (complexPairSum
        (rp1SelectedPairs data)
        (multiplierPairContribution data))
      (C3.complexAdd
        (complexPairSum
          (rp2SelectedPairs data)
          (multiplierPairContribution data))
        (complexPairSum
          (hardTailSelectedPairs data)
          (multiplierPairContribution data)))
  ∎
