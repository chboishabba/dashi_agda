module DASHI.Computation.SSSPConsumerInvariantSymmetryQuotientExact where

-- Generic finite-state theorem shape behind the sorting-barrier BIDI lane:
-- if a consumer is invariant under an action, then action-related states are
-- observationally quotient-equivalent for that consumer.  This owner is
-- deliberately representation-agnostic; no group cardinality or Base369
-- carrier identification is assumed.

open import Agda.Builtin.Equality using (_≡_; refl; cong; trans; sym)
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Biology.FiniteSymmetryStabiliserExact as Sym
import DASHI.Computation.SSSPThreeFrontierLinearExtensionQuotientBidiExact as F3

------------------------------------------------------------------------
-- 1. Generic consumer-invariant action package.
------------------------------------------------------------------------

record ConsumerInvariantAction : Set₁ where
  constructor consumerInvariantAction
  field
    State Symmetry Output : Set
    identity : Symmetry
    compose : Symmetry → Symmetry → Symmetry
    act : Symmetry → State → State
    observe : State → Output

    identityActs :
      (x : State) → act identity x ≡ x

    actionComposes :
      (g h : Symmetry) (x : State) →
      act (compose g h) x ≡ act g (act h x)

    observerInvariant :
      (g : Symmetry) (x : State) →
      observe (act g x) ≡ observe x

open ConsumerInvariantAction public

record SameActionOrbit
  (Q : ConsumerInvariantAction)
  (x y : State Q) : Set where
  constructor sameActionOrbit
  field
    symmetryWitness : Symmetry Q
    actionWitness : act Q symmetryWitness x ≡ y

open SameActionOrbit public

orbitRelatedStatesAreConsumerEquivalent :
  (Q : ConsumerInvariantAction) →
  (x y : State Q) →
  SameActionOrbit Q x y →
  observe Q x ≡ observe Q y
orbitRelatedStatesAreConsumerEquivalent Q x y orbit =
  trans
    (sym (observerInvariant Q (symmetryWitness orbit) x))
    (cong (observe Q) (actionWitness orbit))

------------------------------------------------------------------------
-- 2. Instantiate with the three-frontier tail-swap symmetry.
--
-- The full relation sheet changes under b<->c, but the symmetric consumer
-- "is a before both b and c?" is invariant on all six linear extensions.
------------------------------------------------------------------------

aIsFirst : F3.LinearOrder3 → Bool
aIsFirst F3.abc = true
aIsFirst F3.acb = true
aIsFirst F3.bac = false
aIsFirst F3.bca = false
aIsFirst F3.cab = false
aIsFirst F3.cba = false

actTailReflection : Sym.Reflection2 → F3.LinearOrder3 → F3.LinearOrder3
actTailReflection Sym.identityReflection o = o
actTailReflection Sym.swapReflection o = F3.swapBC o

tailReflectionIdentity :
  (o : F3.LinearOrder3) →
  actTailReflection Sym.identityReflection o ≡ o
tailReflectionIdentity o = refl

tailReflectionComposition :
  (g h : Sym.Reflection2) (o : F3.LinearOrder3) →
  actTailReflection (Sym.composeReflection g h) o ≡
  actTailReflection g (actTailReflection h o)
tailReflectionComposition Sym.identityReflection Sym.identityReflection o = refl
tailReflectionComposition Sym.identityReflection Sym.swapReflection o = refl
tailReflectionComposition Sym.swapReflection Sym.identityReflection o = refl
tailReflectionComposition Sym.swapReflection Sym.swapReflection o =
  F3.swapBC-involutive o

aIsFirstTailInvariant :
  (g : Sym.Reflection2) (o : F3.LinearOrder3) →
  aIsFirst (actTailReflection g o) ≡ aIsFirst o
aIsFirstTailInvariant Sym.identityReflection o = refl
aIsFirstTailInvariant Sym.swapReflection F3.abc = refl
aIsFirstTailInvariant Sym.swapReflection F3.acb = refl
aIsFirstTailInvariant Sym.swapReflection F3.bac = refl
aIsFirstTailInvariant Sym.swapReflection F3.bca = refl
aIsFirstTailInvariant Sym.swapReflection F3.cab = refl
aIsFirstTailInvariant Sym.swapReflection F3.cba = refl

threeFrontierAFirstQuotient : ConsumerInvariantAction
threeFrontierAFirstQuotient =
  consumerInvariantAction
    F3.LinearOrder3
    Sym.Reflection2
    Bool
    Sym.identityReflection
    Sym.composeReflection
    actTailReflection
    aIsFirst
    tailReflectionIdentity
    tailReflectionComposition
    aIsFirstTailInvariant

abcAcbSameOrbit :
  SameActionOrbit threeFrontierAFirstQuotient F3.abc F3.acb
abcAcbSameOrbit =
  sameActionOrbit Sym.swapReflection refl

abcAcbConsumerEquivalentFromSymmetry :
  aIsFirst F3.abc ≡ aIsFirst F3.acb
abcAcbConsumerEquivalentFromSymmetry =
  orbitRelatedStatesAreConsumerEquivalent
    threeFrontierAFirstQuotient F3.abc F3.acb abcAcbSameOrbit

------------------------------------------------------------------------
-- 3. Fundamental-domain reading.
--
-- The existing finite-symmetry owner proves that a symmetry stabiliser can
-- reduce independent data needed to reconstruct an invariant object.  Here the
-- consumer quotient similarly stores one orbit-level observation instead of a
-- separately totalised answer for every action-related representative.
-- This is a proof-shape reuse only: SSSP linear orders are not crystal states.
------------------------------------------------------------------------

record SortingBarrierSymmetryBoundary : Set where
  constructor sortingBarrierSymmetryBoundary
  field
    consumerInvariantOrbitCanShareObservation : Bool
    consumerInvariantOrbitCanShareObservationIsTrue :
      consumerInvariantOrbitCanShareObservation ≡ true
    symmetryImpliesFullStateEquality : Bool
    symmetryImpliesFullStateEqualityIsFalse :
      symmetryImpliesFullStateEquality ≡ false
    symmetryImpliesCyclicC6Identification : Bool
    symmetryImpliesCyclicC6IdentificationIsFalse :
      symmetryImpliesCyclicC6Identification ≡ false

canonicalSortingBarrierSymmetryBoundary : SortingBarrierSymmetryBoundary
canonicalSortingBarrierSymmetryBoundary =
  sortingBarrierSymmetryBoundary true refl false refl false refl
