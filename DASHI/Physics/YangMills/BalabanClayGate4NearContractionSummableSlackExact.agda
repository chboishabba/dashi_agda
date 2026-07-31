module DASHI.Physics.YangMills.BalabanClayGate4NearContractionSummableSlackExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Near contraction with a summable multiplicative correction.
--
-- Hans Koch and Peter Wittwer,
-- "On the Renormalization Group Transformation for Scalar Hierarchical
-- Models", Communications in Mathematical Physics 138 (1991), 537--568.
-- DOI: 10.1007/BF02102041.
--
-- The cited paper is methodological precedent, not authority for a Yang--Mills
-- Q-star constant.  The finite algebra below is independent: a recurrence with
-- factors rho(1+delta_k) is iterated exactly, and a bounded partial sum of the
-- nonnegative scaled slacks controls their product by exp(totalSlack).
------------------------------------------------------------------------

record OrderedExponentialProduct (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar
    exponential : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    Nonnegative : Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (multiply left right) (multiply lower upper)

    exponentialMonotone : ∀ {left right} →
      LessEqual left right →
      LessEqual (exponential left) (exponential right)

    multiplyAssociative : ∀ left middle right →
      multiply (multiply left middle) right
      ≡ multiply left (multiply middle right)

    oneLeft : ∀ value → multiply one value ≡ value

    exponentialZero : exponential zero ≡ one
    exponentialAdd : ∀ left right →
      exponential (add left right)
      ≡ multiply (exponential left) (exponential right)

    onePlusBelowExponential : ∀ value →
      Nonnegative value →
      LessEqual (add one value) (exponential value)

open OrderedExponentialProduct public

partialSum :
  ∀ {Scalar} → OrderedExponentialProduct Scalar →
  (Nat → Scalar) → Nat → Scalar
partialSum algebra values zero = zero algebra
partialSum algebra values (suc count) =
  add algebra (values count) (partialSum algebra values count)

correctionProduct :
  ∀ {Scalar} → OrderedExponentialProduct Scalar →
  (Nat → Scalar) → Nat → Scalar
correctionProduct algebra slack zero = one algebra
correctionProduct algebra slack (suc count) =
  multiply algebra
    (add algebra (one algebra) (slack count))
    (correctionProduct algebra slack count)

correctionProductBelowExponentialPartialSum :
  ∀ {Scalar}
    (algebra : OrderedExponentialProduct Scalar)
    (slack : Nat → Scalar) →
  (∀ count → Nonnegative algebra (slack count)) →
  ∀ count →
  LessEqual algebra
    (correctionProduct algebra slack count)
    (exponential algebra (partialSum algebra slack count))
correctionProductBelowExponentialPartialSum algebra slack slackNonnegative zero =
  subst
    (λ upper → LessEqual algebra (one algebra) upper)
    (sym (exponentialZero algebra))
    (reflexive algebra (one algebra))
correctionProductBelowExponentialPartialSum algebra slack slackNonnegative
    (suc count) =
  subst
    (λ upper → LessEqual algebra
      (correctionProduct algebra slack (suc count)) upper)
    (sym (exponentialAdd algebra
      (slack count) (partialSum algebra slack count)))
    (multiplyMonotone algebra
      (onePlusBelowExponential algebra
        (slack count) (slackNonnegative count))
      (correctionProductBelowExponentialPartialSum
        algebra slack slackNonnegative count))

correctionProductBelowTotalSlack :
  ∀ {Scalar}
    (algebra : OrderedExponentialProduct Scalar)
    (slack : Nat → Scalar) →
  (∀ count → Nonnegative algebra (slack count)) →
  (totalSlack : Scalar) →
  (∀ count → LessEqual algebra
    (partialSum algebra slack count) totalSlack) →
  ∀ count →
  LessEqual algebra
    (correctionProduct algebra slack count)
    (exponential algebra totalSlack)
correctionProductBelowTotalSlack algebra slack slackNonnegative totalSlack
    partialSumsBounded count =
  transitive algebra
    (correctionProductBelowExponentialPartialSum
      algebra slack slackNonnegative count)
    (exponentialMonotone algebra (partialSumsBounded count))

record NearContractionRecursion (Scalar : Set) : Set₁ where
  field
    algebra : OrderedExponentialProduct Scalar
    state factor : Nat → Scalar

    stepBound : ∀ count →
      LessEqual algebra
        (state (suc count))
        (multiply algebra (factor count) (state count))

open NearContractionRecursion public

factorProduct :
  ∀ {Scalar} → NearContractionRecursion Scalar → Nat → Scalar
factorProduct dataSet zero = one (algebra dataSet)
factorProduct dataSet (suc count) =
  multiply (algebra dataSet)
    (factor dataSet count)
    (factorProduct dataSet count)

iterateNearContraction :
  ∀ {Scalar}
    (dataSet : NearContractionRecursion Scalar)
    count →
  LessEqual (algebra dataSet)
    (state dataSet count)
    (multiply (algebra dataSet)
      (factorProduct dataSet count)
      (state dataSet zero))
iterateNearContraction dataSet zero =
  subst
    (λ upper → LessEqual (algebra dataSet)
      (state dataSet zero) upper)
    (sym (oneLeft (algebra dataSet) (state dataSet zero)))
    (reflexive (algebra dataSet) (state dataSet zero))
iterateNearContraction dataSet (suc count) =
  transitive (algebra dataSet)
    (stepBound dataSet count)
    (subst
      (λ upper → LessEqual (algebra dataSet)
        (multiply (algebra dataSet)
          (factor dataSet count) (state dataSet count))
        upper)
      (sym (multiplyAssociative (algebra dataSet)
        (factor dataSet count)
        (factorProduct dataSet count)
        (state dataSet zero)))
      (multiplyMonotone (algebra dataSet)
        (reflexive (algebra dataSet) (factor dataSet count))
        (iterateNearContraction dataSet count)))

record SummableSlackFactorization
    {Scalar : Set}
    (recursion : NearContractionRecursion Scalar) : Set₁ where
  field
    scaledSlack : Nat → Scalar
    scaledSlackNonnegative : ∀ count →
      Nonnegative (algebra recursion) (scaledSlack count)

    rhoPower : Nat → Scalar
    totalSlack : Scalar

    partialScaledSlackBounded : ∀ count →
      LessEqual (algebra recursion)
        (partialSum (algebra recursion) scaledSlack count)
        totalSlack

    factorProductMeaning : ∀ count →
      factorProduct recursion count
      ≡ multiply (algebra recursion)
          (rhoPower count)
          (correctionProduct
            (algebra recursion) scaledSlack count)

open SummableSlackFactorization public

factorProductBelowSummableSlackEnvelope :
  ∀ {Scalar}
    {recursion : NearContractionRecursion Scalar}
    (factorization : SummableSlackFactorization recursion)
    count →
  LessEqual (algebra recursion)
    (factorProduct recursion count)
    (multiply (algebra recursion)
      (rhoPower factorization count)
      (exponential (algebra recursion) (totalSlack factorization)))
factorProductBelowSummableSlackEnvelope {recursion = recursion}
    factorization count =
  subst
    (λ lower → LessEqual (algebra recursion) lower
      (multiply (algebra recursion)
        (rhoPower factorization count)
        (exponential (algebra recursion) (totalSlack factorization))))
    (sym (factorProductMeaning factorization count))
    (multiplyMonotone (algebra recursion)
      (reflexive (algebra recursion) (rhoPower factorization count))
      (correctionProductBelowTotalSlack
        (algebra recursion)
        (scaledSlack factorization)
        (scaledSlackNonnegative factorization)
        (totalSlack factorization)
        (partialScaledSlackBounded factorization)
        count))

stateBelowSummableSlackEnvelope :
  ∀ {Scalar}
    {recursion : NearContractionRecursion Scalar}
    (factorization : SummableSlackFactorization recursion)
    count →
  LessEqual (algebra recursion)
    (state recursion count)
    (multiply (algebra recursion)
      (multiply (algebra recursion)
        (rhoPower factorization count)
        (exponential (algebra recursion) (totalSlack factorization)))
      (state recursion zero))
stateBelowSummableSlackEnvelope {recursion = recursion}
    factorization count =
  transitive (algebra recursion)
    (iterateNearContraction recursion count)
    (multiplyMonotone (algebra recursion)
      (factorProductBelowSummableSlackEnvelope factorization count)
      (reflexive (algebra recursion) (state recursion zero)))

finiteNearContractionIterationLevel : ProofLevel
finiteNearContractionIterationLevel = machineChecked

summableSlackExponentialProductLevel : ProofLevel
summableSlackExponentialProductLevel = machineChecked

nearContractionSummableSlackEnvelopeLevel : ProofLevel
nearContractionSummableSlackEnvelopeLevel = machineChecked

kochWittwerMethodologicalProvenanceLevel : ProofLevel
kochWittwerMethodologicalProvenanceLevel = standardImported

physicalQstarFactorizationInputsLevel : ProofLevel
physicalQstarFactorizationInputsLevel = conditional

physicalQstarScaledSlackSummabilityInputsLevel : ProofLevel
physicalQstarScaledSlackSummabilityInputsLevel = conditional

physicalQstarNearContractionStepInputsLevel : ProofLevel
physicalQstarNearContractionStepInputsLevel = conditional
