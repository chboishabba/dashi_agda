module DASHI.NumberTheory.ThreeAdicDigitAttractor where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Algebra.BalancedTernary as BT

------------------------------------------------------------------------
-- Finite prefix theorem: adding the same leading ternary digit increases the
-- shared-prefix depth by one.  This is the checked contraction surface beneath
-- the intended 3-adic completion statement.
------------------------------------------------------------------------

Prefix : Nat → Set
Prefix depth = Vec BT.Trit depth

agreementDepth :
  ∀ {depth} →
  Prefix depth →
  Prefix depth →
  Nat
agreementDepth [] [] = zero
agreementDepth (BT.neg ∷ xs) (BT.neg ∷ ys) = suc (agreementDepth xs ys)
agreementDepth (BT.zero ∷ xs) (BT.zero ∷ ys) = suc (agreementDepth xs ys)
agreementDepth (BT.pos ∷ xs) (BT.pos ∷ ys) = suc (agreementDepth xs ys)
agreementDepth _ _ = zero

prependOne :
  ∀ {depth} →
  Prefix depth →
  Prefix (suc depth)
prependOne prefix = BT.pos ∷ prefix

prependOneIncreasesAgreement :
  ∀ {depth} (left right : Prefix depth) →
  agreementDepth (prependOne left) (prependOne right)
    ≡ suc (agreementDepth left right)
prependOneIncreasesAgreement left right = refl

allOnesPrefix : (depth : Nat) → Prefix depth
allOnesPrefix zero = []
allOnesPrefix (suc depth) = BT.pos ∷ allOnesPrefix depth

allOnesExtendsByOne :
  ∀ depth →
  allOnesPrefix (suc depth) ≡ prependOne (allOnesPrefix depth)
allOnesExtendsByOne depth = refl

allOnesSelfAgreement :
  ∀ depth →
  agreementDepth (allOnesPrefix depth) (allOnesPrefix depth) ≡ depth
allOnesSelfAgreement zero = refl
allOnesSelfAgreement (suc depth) =
  cong suc (allOnesSelfAgreement depth)

------------------------------------------------------------------------
-- Completion authority.  A consumer claiming the Q_3 limit and rational image
-- -1/2 must supply the completion, convergence, and interpretation witnesses.
------------------------------------------------------------------------

record ThreeAdicCompletionAuthority : Set₁ where
  field
    CompletionPoint : Set
    RationalImage : Set

    embedPrefix :
      ∀ {depth} → Prefix depth → CompletionPoint

    allOnesLimit : CompletionPoint

    ConvergesAtDepth : CompletionPoint → CompletionPoint → Nat → Set

    prefixConvergesToLimit :
      (depth : Nat) →
      ConvergesAtDepth
        (embedPrefix (allOnesPrefix depth))
        allOnesLimit
        depth

    rationalImage : CompletionPoint → RationalImage
    minusHalf : RationalImage

    allOnesLimitMapsToMinusHalf :
      rationalImage allOnesLimit ≡ minusHalf

open ThreeAdicCompletionAuthority public

record ComplementedCompletion : Set₁ where
  field
    Point : Set
    complement : Point → Point
    complementInvolutive :
      ∀ point → complement (complement point) ≡ point
    centre : Point
    centreFixed : complement centre ≡ centre

open ComplementedCompletion public

record ThreeAdicAuthorityBoundary : Set where
  constructor threeAdicAuthorityBoundary
  field
    finitePrefixContractionClosed : Bool
    q3CompletionInstantiatedHere : Bool
    q3CompletionInstantiatedHereIsFalse :
      q3CompletionInstantiatedHere ≡ false
    rationalMinusHalfDerivedWithoutAuthority : Bool
    rationalMinusHalfDerivedWithoutAuthorityIsFalse :
      rationalMinusHalfDerivedWithoutAuthority ≡ false

canonicalThreeAdicAuthorityBoundary : ThreeAdicAuthorityBoundary
canonicalThreeAdicAuthorityBoundary =
  threeAdicAuthorityBoundary true false refl false refl
