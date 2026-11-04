module DASHI.Physics.YangMills.YMClayFiniteNativeAdjacentWordInverseExact where

------------------------------------------------------------------------
-- R443/R445: CONSTRUCTIVE ORIGINAL LinkPermutation WORD+INVERSE ALGEBRA.
--
-- Existing YMClayFiniteProductHaarPermutationExact supplies the
-- ORIGINAL adjacent-swap word language and its N-link Fubini
-- invariance. The existing 1024 original-bond reference already
-- has a verified 41,792 adjacent-swap program numerically.
--
-- This module implements typed adjacent swap at any Fin index, typed
-- execution of a finite adjacent-swap word, its interpretation as
-- the ORIGINAL Product.LinkPermutation (not an unrelated permutation
-- carrier), and the inverse of EVERY original permutation program.
--
-- Both composite inverse laws are proved on arbitrary Vec Link n,
-- without function extensionality or a new group/measure construction.
-- Thus when the pending 1024 original native swap list is realized
-- as a typed word, its inverse and exact decoder transport will not
-- need new permutation assumptions. The still-unpaid finite source
-- gate is constructing that exact closed word and proving the ONE
-- original 1024 canonical-label equality. The Python 41,792 plan
-- is not itself a typed Agda word or a kernel verification receipt.
--
-- Product.LinkPermutation imports RealAnalysisAxioms transitively;
-- therefore no postulate-free safe trust claim. SOURCE WRITTEN,
-- exact-head Agda kernel pending. No continuous Haar/Gibbs/RG/Clay.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import Agda.Builtin.List as List
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product

-- One swap position i in an original vector of length n+1, with
-- i : Fin n ensuring i+1 is always in the original vector.
originalAdjacentAt :
  ∀ {n} → Fin.Fin n → Product.LinkPermutation (suc n)
originalAdjacentAt {n = zero} ()
originalAdjacentAt {n = suc n} Fin.zero = Product.swapHead
originalAdjacentAt {n = suc n} (Fin.suc index) =
  Product.fixHead (originalAdjacentAt index)

originalApplyAdjacentWord :
  ∀ {A : Set} {n : Nat} →
  List.List (Fin.Fin n) → Vec.Vec A (suc n) → Vec.Vec A (suc n)
originalApplyAdjacentWord List.[] values = values
originalApplyAdjacentWord (List._∷_ index rest) values =
  originalApplyAdjacentWord rest
    (Product.permuteLinks (originalAdjacentAt index) values)

-- Crucial orientation: original Product.compose first second
-- applies second FIRST. Therefore the source word recursion must
-- compose the *rest* after the FIRST listed adjacent step.
originalAdjacentWordProgram :
  ∀ {n} → List.List (Fin.Fin n) → Product.LinkPermutation (suc n)
originalAdjacentWordProgram List.[] = Product.identity
originalAdjacentWordProgram (List._∷_ index rest) =
  Product.compose
    (originalAdjacentWordProgram rest)
    (originalAdjacentAt index)

originalAdjacentWordProgramActsInListedOrder :
  ∀ {A : Set} {n}
    (word : List.List (Fin.Fin n)) (values : Vec.Vec A (suc n)) →
  Product.permuteLinks
    (originalAdjacentWordProgram word) values
  ≡ originalApplyAdjacentWord word values
originalAdjacentWordProgramActsInListedOrder List.[] values = refl
originalAdjacentWordProgramActsInListedOrder
    (List._∷_ index rest) values =
  originalAdjacentWordProgramActsInListedOrder
    rest (Product.permuteLinks (originalAdjacentAt index) values)

-- Original adjacent swap and composition form a genuine finite
-- invertible program language. Inverse programs are synthesized,
-- not requested as new decoder witnesses.
originalInverseProgram :
  ∀ {n} → Product.LinkPermutation n → Product.LinkPermutation n
originalInverseProgram Product.identity = Product.identity
originalInverseProgram (Product.compose first second) =
  Product.compose
    (originalInverseProgram second)
    (originalInverseProgram first)
originalInverseProgram (Product.fixHead subprogram) =
  Product.fixHead (originalInverseProgram subprogram)
originalInverseProgram Product.swapHead = Product.swapHead

originalInverseAfterProgram :
  ∀ {A : Set} {n}
    (program : Product.LinkPermutation n)
    (values : Vec.Vec A n) →
  Product.permuteLinks
    (originalInverseProgram program)
    (Product.permuteLinks program values)
  ≡ values
originalInverseAfterProgram Product.identity values = refl
originalInverseAfterProgram (Product.compose first second) values =
  trans
    (cong
      (Product.permuteLinks (originalInverseProgram second))
      (originalInverseAfterProgram
        first (Product.permuteLinks second values)))
    (originalInverseAfterProgram second values)
originalInverseAfterProgram (Product.fixHead program)
    (Vec._∷_ head tail) =
  cong (λ chosenTail → Vec._∷_ head chosenTail)
    (originalInverseAfterProgram program tail)
originalInverseAfterProgram Product.swapHead
    (Vec._∷_ first (Vec._∷_ second tail)) = refl

originalProgramAfterInverse :
  ∀ {A : Set} {n}
    (program : Product.LinkPermutation n)
    (values : Vec.Vec A n) →
  Product.permuteLinks program
    (Product.permuteLinks (originalInverseProgram program) values)
  ≡ values
originalProgramAfterInverse Product.identity values = refl
originalProgramAfterInverse (Product.compose first second) values =
  trans
    (cong
      (Product.permuteLinks first)
      (originalProgramAfterInverse second
        (Product.permuteLinks (originalInverseProgram first) values)))
    (originalProgramAfterInverse first values)
originalProgramAfterInverse (Product.fixHead program)
    (head ∷ tail) =
  cong (λ chosenTail → Vec._∷_ head chosenTail)
    (originalProgramAfterInverse program tail)
originalProgramAfterInverse Product.swapHead
    (first ∷ second ∷ tail) = refl

-- Any closed R443 C3 program or R445 128-pair/896-spectator program
-- expressed in this original LinkPermutation language inherits both
-- original inverse laws; its exact selected canonical bond equality
-- must still be furnished and kernel-accepted as a closed certificate.
