module DASHI.Physics.YangMills.BalabanClayDyadicCutoffTailExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models", Communications in
-- Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- DASHI CONTRIBUTION
--
-- Close the scalar cutoff telescope for a dyadic irrelevant tail.  If the
-- scale-k change of a renormalized observable is bounded by C 2^-k, then
-- finite metric telescoping gives
--
--   d(F_n,F_(n+m)) <= C sum_(j=n)^(n+m-1) 2^-j
--                    <= 2 C 2^-n.
--
-- Both the geometric tail and the endpoint-index transport are proved by
-- finite induction.  The physical adjacent-scale estimate remains the only
-- analytic producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Data.Nat.Properties as ℕP
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

half two : ℚ
half = + 1 / 2
two = + 2 / 1

dyadic : Nat → ℚ
dyadic zero = + 1 / 1
dyadic (suc n) = half * dyadic n

dyadicNonnegative : ∀ n → 0ℚ ≤ dyadic n
dyadicNonnegative zero = ℚP.nonNegative⁻¹ (+ 1 / 1)
dyadicNonnegative (suc n) =
  let
    instance
      halfNN : NonNegative half
      halfNN = ℚ.nonNegative (ℚP.nonNegative⁻¹ half)
      tailNN : NonNegative (dyadic n)
      tailNN = ℚ.nonNegative (dyadicNonnegative n)
  in ℚP.nonNegative⁻¹ (half * dyadic n)

twoDyadicNonnegative : ∀ n → 0ℚ ≤ two * dyadic n
twoDyadicNonnegative n =
  let
    instance
      twoNN : NonNegative two
      twoNN = ℚ.nonNegative (ℚP.nonNegative⁻¹ two)
      dyadicNN : NonNegative (dyadic n)
      dyadicNN = ℚ.nonNegative (dyadicNonnegative n)
  in ℚP.nonNegative⁻¹ (two * dyadic n)

twoNextDyadicIsCurrent : ∀ n →
  two * dyadic (suc n) ≡ dyadic n
twoNextDyadicIsCurrent n = ℚRing.solve-∀ (dyadic n)

finiteDyadicTail : Nat → Nat → ℚ
finiteDyadicTail start zero = 0ℚ
finiteDyadicTail start (suc count) =
  dyadic start + finiteDyadicTail (suc start) count

dyadicPlusDoubleNextIsDoubleCurrent : ∀ start →
  dyadic start + two * dyadic (suc start)
  ≡ two * dyadic start
dyadicPlusDoubleNextIsDoubleCurrent start
  rewrite twoNextDyadicIsCurrent start =
  ℚRing.solve-∀ (dyadic start)

finiteDyadicTailBelowDoubleStart : ∀ start count →
  finiteDyadicTail start count ≤ two * dyadic start
finiteDyadicTailBelowDoubleStart start zero =
  twoDyadicNonnegative start
finiteDyadicTailBelowDoubleStart start (suc count) =
  ℚP.≤-trans
    (ℚP.+-mono-≤
      ℚP.≤-refl
      (finiteDyadicTailBelowDoubleStart (suc start) count))
    (subst
      (λ upper →
        dyadic start + two * dyadic (suc start) ≤ upper)
      (dyadicPlusDoubleNextIsDoubleCurrent start)
      ℚP.≤-refl)

startPlusZero : ∀ start → start + zero ≡ start
startPlusZero = ℕP.+-identityʳ

startSuccessorCount : ∀ start count →
  start + suc count ≡ suc start + count
startSuccessorCount = ℕP.+-suc

record DyadicIncrementSequence
    (State : Set) : Set₁ where
  field
    stateAt : Nat → State
    Distance : State → State → ℚ
    coefficient : ℚ

    coefficientNonnegative : 0ℚ ≤ coefficient
    distanceReflexiveZero : ∀ state → Distance state state ≡ 0ℚ
    distanceTriangle : ∀ left middle right →
      Distance left right
      ≤ Distance left middle + Distance middle right

    adjacentIncrement : ∀ scale →
      Distance (stateAt scale) (stateAt (suc scale))
      ≤ coefficient * dyadic scale

open DyadicIncrementSequence public

finiteSequenceDistance :
  ∀ {State} →
  DyadicIncrementSequence State → Nat → Nat → ℚ
finiteSequenceDistance dataSet start count =
  Distance dataSet
    (stateAt dataSet start)
    (stateAt dataSet (start + count))

coefficientDistributesTailStep : ∀ coefficient first rest →
  coefficient * first + coefficient * rest
  ≡ coefficient * (first + rest)
coefficientDistributesTailStep = ℚRing.solve-∀

finiteDistanceAtZeroIsZero :
  ∀ {State}
    (dataSet : DyadicIncrementSequence State)
    start →
  finiteSequenceDistance dataSet start zero ≡ 0ℚ
finiteDistanceAtZeroIsZero dataSet start =
  subst
    (λ endpoint →
      Distance dataSet
        (stateAt dataSet start)
        (stateAt dataSet endpoint)
      ≡ 0ℚ)
    (sym (startPlusZero start))
    (distanceReflexiveZero dataSet (stateAt dataSet start))

finiteDistanceBelowDyadicTail :
  ∀ {State}
    (dataSet : DyadicIncrementSequence State)
    start count →
  finiteSequenceDistance dataSet start count
  ≤ coefficient dataSet * finiteDyadicTail start count
finiteDistanceBelowDyadicTail dataSet start zero =
  subst
    (λ left → left ≤ coefficient dataSet * 0ℚ)
    (sym (finiteDistanceAtZeroIsZero dataSet start))
    (subst
      (λ right → 0ℚ ≤ right)
      (sym (ℚP.*-zeroʳ (coefficient dataSet)))
      ℚP.≤-refl)
finiteDistanceBelowDyadicTail dataSet start (suc count) =
  let
    indexEquality = startSuccessorCount start count
    recursive = finiteDistanceBelowDyadicTail dataSet (suc start) count
    recursiveAtTarget =
      subst
        (λ targetIndex →
          Distance dataSet
            (stateAt dataSet (suc start))
            (stateAt dataSet targetIndex)
          ≤ coefficient dataSet
              * finiteDyadicTail (suc start) count)
        (sym indexEquality)
        recursive
  in
  ℚP.≤-trans
    (distanceTriangle dataSet
      (stateAt dataSet start)
      (stateAt dataSet (suc start))
      (stateAt dataSet (start + suc count)))
    (ℚP.≤-trans
      (ℚP.+-mono-≤
        (adjacentIncrement dataSet start)
        recursiveAtTarget)
      (subst
        (λ upper →
          coefficient dataSet * dyadic start
          + coefficient dataSet
              * finiteDyadicTail (suc start) count
          ≤ upper)
        (coefficientDistributesTailStep
          (coefficient dataSet)
          (dyadic start)
          (finiteDyadicTail (suc start) count))
        ℚP.≤-refl))

finiteDistanceBelowDoubleDyadic :
  ∀ {State}
    (dataSet : DyadicIncrementSequence State)
    start count →
  finiteSequenceDistance dataSet start count
  ≤ coefficient dataSet * (two * dyadic start)
finiteDistanceBelowDoubleDyadic dataSet start count =
  ℚP.≤-trans
    (finiteDistanceBelowDyadicTail dataSet start count)
    (let
      instance
        coefficientNN : NonNegative (coefficient dataSet)
        coefficientNN = ℚ.nonNegative
          (coefficientNonnegative dataSet)
     in ℚP.*-monoˡ-≤-nonNeg
          (coefficient dataSet)
          (finiteDyadicTailBelowDoubleStart start count))

dyadicTailInductionLevel : ProofLevel
dyadicTailInductionLevel = machineChecked

dyadicCutoffCauchyMajorantLevel : ProofLevel
dyadicCutoffCauchyMajorantLevel = machineChecked

physicalAdjacentCutoffIncrementLevel : ProofLevel
physicalAdjacentCutoffIncrementLevel = conditional
