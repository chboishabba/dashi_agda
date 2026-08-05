module DASHI.Physics.YangMills.BalabanClayTransferGapDefectTelescopingExact where

------------------------------------------------------------------------
-- SOURCE AUDIT
--
-- Mir Faizal and Arshid Shabir,
-- "Reflection-positive renormalization and the persistence of the mass gap
-- in lattice SU(N) Yang-Mills: Part (2)", International Journal of Geometric
-- Methods in Modern Physics 23 (2026).
-- DOI: 10.1142/S0219887826501136.
--
-- DASHI CONTRIBUTION
--
-- Interlacing inequalities telescope additively.  Summability of defects is
-- not by itself enough to leave a positive gap: the total defect must be
-- strictly smaller than the initial gap.  This module proves the finite
-- telescope in an arbitrary ordered commutative additive monoid and gives a
-- closed one-step counterexample to the weaker inference.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data Empty : Set where

record OrderedCommutativeAdditiveMonoid : Set₁ where
  field
    Carrier : Set
    zeroValue : Carrier
    addValue : Carrier → Carrier → Carrier
    LessEqual : Carrier → Carrier → Set

    lessEqualReflexive : ∀ value → LessEqual value value
    lessEqualTransitive : ∀ {a b c} →
      LessEqual a b → LessEqual b c → LessEqual a c
    addMonotoneRight : ∀ {a b} right →
      LessEqual a b → LessEqual (addValue a right) (addValue b right)

    addIdentityRight : ∀ value → addValue value zeroValue ≡ value
    addAssociative : ∀ first second third →
      addValue (addValue first second) third
      ≡ addValue first (addValue second third)

open OrderedCommutativeAdditiveMonoid public

sumDefects :
  (algebra : OrderedCommutativeAdditiveMonoid) →
  List (Carrier algebra) → Carrier algebra
sumDefects algebra [] = zeroValue algebra
sumDefects algebra (error ∷ errors) =
  addValue algebra (sumDefects algebra errors) error

data DefectChain
    (algebra : OrderedCommutativeAdditiveMonoid) :
    Carrier algebra → List (Carrier algebra) → Carrier algebra → Set where
  stop : ∀ {gap} → DefectChain algebra gap [] gap
  step : ∀ {initial next final error errors} →
    LessEqual algebra initial (addValue algebra next error) →
    DefectChain algebra next errors final →
    DefectChain algebra initial (error ∷ errors) final

finiteDefectChainTelescopes :
  ∀ {algebra initial errors final} →
  DefectChain algebra initial errors final →
  LessEqual algebra initial
    (addValue algebra final (sumDefects algebra errors))
finiteDefectChainTelescopes {algebra} stop =
  subst
    (λ upper → LessEqual algebra _ upper)
    (sym (addIdentityRight algebra _))
    (lessEqualReflexive algebra _)
finiteDefectChainTelescopes {algebra} (step firstStep tail) =
  let
    tailBound = finiteDefectChainTelescopes tail
    liftedTail = addMonotoneRight algebra _ tailBound
    associated = addAssociative algebra _ _ _
  in
  lessEqualTransitive algebra firstStep
    (subst
      (λ upper → LessEqual algebra _ upper)
      associated
      liftedTail)

------------------------------------------------------------------------
-- A finite, completely explicit failure of "summable implies positive".
------------------------------------------------------------------------

infixl 6 _+ᴺ_
_+ᴺ_ : Nat → Nat → Nat
zero +ᴺ right = right
suc left +ᴺ right = suc (left +ᴺ right)

infix 4 _≤ᴺ_
data _≤ᴺ_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤ᴺ n
  suc≤suc : ∀ {m n} → m ≤ᴺ n → suc m ≤ᴺ suc n

one : Nat
one = suc zero

oneStepInterlacingWithTotalLoss :
  one ≤ᴺ (zero +ᴺ one)
oneStepInterlacingWithTotalLoss = suc≤suc zero≤

zeroIsNotPositive : one ≤ᴺ zero → Empty
zeroIsNotPositive ()

record SummableDefectCanExhaustGap : Set where
  field
    initialGap finalGap totalDefect : Nat
    interlacingAfterSumming : initialGap ≤ᴺ (finalGap +ᴺ totalDefect)
    finalGapNotPositive : one ≤ᴺ finalGap → Empty

summabilityWithoutStrictBudgetCounterexample : SummableDefectCanExhaustGap
summabilityWithoutStrictBudgetCounterexample = record
  { initialGap = one
  ; finalGap = zero
  ; totalDefect = one
  ; interlacingAfterSumming = oneStepInterlacingWithTotalLoss
  ; finalGapNotPositive = zeroIsNotPositive
  }

finiteInterlacingTelescopeLevel : ProofLevel
finiteInterlacingTelescopeLevel = machineChecked

strictDefectBudgetNecessityLevel : ProofLevel
strictDefectBudgetNecessityLevel = machineChecked
