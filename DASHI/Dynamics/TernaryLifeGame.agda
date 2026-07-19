module DASHI.Dynamics.TernaryLifeGame where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import DASHI.Algebra.BalancedTernary using (Trit; neg; zero; pos)

------------------------------------------------------------------------
-- Local observations
------------------------------------------------------------------------

record Observation : Set where
  constructor observe
  field
    center : Trit
    positiveNeighbours : Nat
    negativeNeighbours : Nat

open Observation public

activeNeighbours : Observation → Nat
activeNeighbours o = positiveNeighbours o + negativeNeighbours o

------------------------------------------------------------------------
-- Decidable count windows
------------------------------------------------------------------------

isThree : Nat → Bool
isThree (suc (suc (suc zero))) = true
isThree _ = false

isFour : Nat → Bool
isFour (suc (suc (suc (suc zero)))) = true
isFour _ = false

isTwoThree : Nat → Bool
isTwoThree (suc (suc zero)) = true
isTwoThree (suc (suc (suc zero))) = true
isTwoThree _ = false

isTwoThreeFour : Nat → Bool
isTwoThreeFour (suc (suc zero)) = true
isTwoThreeFour (suc (suc (suc zero))) = true
isTwoThreeFour (suc (suc (suc (suc zero)))) = true
isTwoThreeFour _ = false

_or_ : Bool → Bool → Bool
true or _ = true
false or b = b

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else _ = x
if false then _ else y = y

------------------------------------------------------------------------
-- Polarity competition
------------------------------------------------------------------------

-- Cancelling one positive and one negative neighbour exposes the local
-- majority.  Equal populations return the rule's explicit tie strategy.
majorityWith : Trit → Nat → Nat → Trit
majorityWith tie zero zero = tie
majorityWith tie (suc p) zero = pos
majorityWith tie zero (suc n) = neg
majorityWith tie (suc p) (suc n) = majorityWith tie p n

------------------------------------------------------------------------
-- A local three-strategy game rule
------------------------------------------------------------------------

record Rule : Set₁ where
  constructor rule
  field
    birthWindow : Nat → Bool
    survivalWindow : Nat → Bool
    tieStrategy : Trit

open Rule public

-- Exact ternary lift of Conway B3/S23.  Because three is odd, a genuine
-- positive/negative tie cannot occur at birth; zero remains the neutral
-- total definition for malformed or abstract observations.
classicRule : Rule
classicRule = rule isThree isTwoThree zero

-- A deliberately richer B34/S234 regime.  Birth at four admits a 2/2
-- strategic tie, so HOLD or a symmetry-breaking tie policy becomes active.
evolvingRule : Trit → Rule
evolvingRule tie = rule (λ n → isThree n or isFour n) isTwoThreeFour tie

transitionWith : Rule → Observation → Trit
transitionWith r o with center o
... | zero =
  if birthWindow r (activeNeighbours o)
  then majorityWith (tieStrategy r)
                    (positiveNeighbours o)
                    (negativeNeighbours o)
  else zero
... | pos =
  if survivalWindow r (activeNeighbours o)
  then pos
  else zero
... | neg =
  if survivalWindow r (activeNeighbours o)
  then neg
  else zero

classicTransition : Observation → Trit
classicTransition = transitionWith classicRule

------------------------------------------------------------------------
-- Game-theoretic reading
------------------------------------------------------------------------

Strategy : Set
Strategy = Trit

data Outcome : Set where
  loss hold win : Outcome

same : Trit → Trit → Bool
same neg neg = true
same zero zero = true
same pos pos = true
same _ _ = false

-- The local rule publishes the strategy selected by neighbourhood pressure.
-- Matching it is a local best response; abstaining against another selected
-- strategy receives HOLD rather than LOSS.
localPayoff : Rule → Observation → Strategy → Outcome
localPayoff r o chosen with same chosen (transitionWith r o)
... | true = win
... | false with chosen
...   | zero = hold
...   | _ = loss

bestResponse : Rule → Observation → Strategy
bestResponse = transitionWith

selfPayoff : (r : Rule) (o : Observation) →
  localPayoff r o (bestResponse r o) ≡ win
selfPayoff r o with transitionWith r o
... | neg = refl
... | zero = refl
... | pos = refl

------------------------------------------------------------------------
-- Focused executable witnesses
------------------------------------------------------------------------

classicPositiveBirth :
  classicTransition (observe zero (suc (suc zero)) (suc zero)) ≡ pos
classicPositiveBirth = refl

classicNegativeBirth :
  classicTransition (observe zero (suc zero) (suc (suc zero))) ≡ neg
classicNegativeBirth = refl

classicUnderpopulationDies :
  classicTransition (observe pos (suc zero) zero) ≡ zero
classicUnderpopulationDies = refl

holdResolvesEvenTie :
  transitionWith (evolvingRule zero)
    (observe zero (suc (suc zero)) (suc (suc zero))) ≡ zero
holdResolvesEvenTie = refl

positiveTieBreakEnters :
  transitionWith (evolvingRule pos)
    (observe zero (suc (suc zero)) (suc (suc zero))) ≡ pos
positiveTieBreakEnters = refl
