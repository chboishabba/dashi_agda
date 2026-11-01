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
-- telescope in an arbitrary ordered commutative additive monoid, proves the
-- strict-budget positivity theorem for natural gaps, and gives a closed
-- one-step counterexample to the weaker inference.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

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
finiteDefectChainTelescopes
    {algebra} {initial = gap} stop =
  subst
    (λ upper → LessEqual algebra gap upper)
    (sym (addIdentityRight algebra gap))
    (lessEqualReflexive algebra gap)
finiteDefectChainTelescopes
    {algebra}
    (step {next = next} {final = final}
      {error = error} {errors = errors} firstStep tail) =
  let
    tailBound = finiteDefectChainTelescopes tail
    liftedTail = addMonotoneRight algebra error tailBound
    associated = addAssociative algebra
      final (sumDefects algebra errors) error
  in
  lessEqualTransitive algebra firstStep
    (subst
      (λ upper →
        LessEqual algebra (addValue algebra next error) upper)
      associated
      liftedTail)

------------------------------------------------------------------------
-- Natural-number strict budget theorem and counterexample.
------------------------------------------------------------------------

infixl 6 _+ᴺ_
_+ᴺ_ : Nat → Nat → Nat
left +ᴺ zero = left
left +ᴺ suc right = suc (left +ᴺ right)

infix 4 _≤ᴺ_
data _≤ᴺ_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤ᴺ n
  suc≤suc : ∀ {m n} → m ≤ᴺ n → suc m ≤ᴺ suc n

≤ᴺ-transitive : ∀ {a b c} → a ≤ᴺ b → b ≤ᴺ c → a ≤ᴺ c
≤ᴺ-transitive zero≤ second = zero≤
≤ᴺ-transitive (suc≤suc first) (suc≤suc second) =
  suc≤suc (≤ᴺ-transitive first second)

cancelCommonRightSummand : ∀ left right common →
  (left +ᴺ common) ≤ᴺ (right +ᴺ common) → left ≤ᴺ right
cancelCommonRightSummand left right zero proof = proof
cancelCommonRightSummand left right (suc common) (suc≤suc proof) =
  cancelCommonRightSummand left right common proof

one : Nat
one = suc zero

strictTotalDefectBudgetForcesPositiveFinalGap :
  ∀ initialGap finalGap totalDefect →
  (one +ᴺ totalDefect) ≤ᴺ initialGap →
  initialGap ≤ᴺ (finalGap +ᴺ totalDefect) →
  one ≤ᴺ finalGap
strictTotalDefectBudgetForcesPositiveFinalGap
    initialGap finalGap totalDefect strictBudget telescoped =
  cancelCommonRightSummand one finalGap totalDefect
    (≤ᴺ-transitive strictBudget telescoped)

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

strictDefectBudgetPositivityLevel : ProofLevel
strictDefectBudgetPositivityLevel = machineChecked

strictDefectBudgetNecessityLevel : ProofLevel
strictDefectBudgetNecessityLevel = machineChecked
