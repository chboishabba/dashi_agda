module DASHI.Analysis.SetoidFiniteSumDerivativeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine

------------------------------------------------------------------------
-- SETOID FINITE-SUM DERIVATIVE COMPILER
--
-- The analytic derivative notion is application-selected.  Once it supplies
-- derivative rules for the zero function and pointwise addition, derivative of
-- every finite partial sum is an induction theorem rather than a new calculus
-- hypothesis.
------------------------------------------------------------------------

record SetoidDerivativeAdditiveSemantics : Set₁ where
  field
    R : Spine.SetoidOrderedCompleteReal
    Domain : Set

    DerivativeAt :
      (Domain → Spine.Carrier R) →
      Domain → Spine.Carrier R → Set

    zeroDerivative : ∀ point →
      DerivativeAt (λ _ → Spine.zero R) point (Spine.zero R)

    addDerivative :
      ∀ {f g df dg point} →
      DerivativeAt f point df →
      DerivativeAt g point dg →
      DerivativeAt
        (λ x → Spine._+_ R (f x) (g x))
        point
        (Spine._+_ R df dg)

    reading : String

open SetoidDerivativeAdditiveSemantics public

finitePartialSum :
  (S : SetoidDerivativeAdditiveSemantics) →
  (Nat → Domain S → Spine.Carrier (R S)) →
  Nat → Domain S → Spine.Carrier (R S)
finitePartialSum S term zero point = Spine.zero (R S)
finitePartialSum S term (suc count) point =
  Spine._+_ (R S)
    (finitePartialSum S term count point)
    (term count point)

finitePartialDerivativeSum :
  (S : SetoidDerivativeAdditiveSemantics) →
  (Nat → Domain S → Spine.Carrier (R S)) →
  Nat → Domain S → Spine.Carrier (R S)
finitePartialDerivativeSum S derivativeTerm zero point = Spine.zero (R S)
finitePartialDerivativeSum S derivativeTerm (suc count) point =
  Spine._+_ (R S)
    (finitePartialDerivativeSum S derivativeTerm count point)
    (derivativeTerm count point)

finiteSumDerivative :
  (S : SetoidDerivativeAdditiveSemantics) →
  {term derivativeTerm : Nat → Domain S → Spine.Carrier (R S)} →
  (termDerivative : ∀ index point →
    DerivativeAt S (term index) point (derivativeTerm index point)) →
  ∀ count point →
  DerivativeAt S
    (finitePartialSum S term count)
    point
    (finitePartialDerivativeSum S derivativeTerm count point)
finiteSumDerivative S termDerivative zero point = zeroDerivative S point
finiteSumDerivative S termDerivative (suc count) point =
  addDerivative S
    (finiteSumDerivative S termDerivative count point)
    (termDerivative count point)

------------------------------------------------------------------------
-- Consumer-side representation weld.
------------------------------------------------------------------------

record FiniteSeriesRepresentationWeld
    (S : SetoidDerivativeAdditiveSemantics)
    (term derivativeTerm : Nat → Domain S → Spine.Carrier (R S)) : Set₁ where
  field
    ConsumerPartialSum : Nat → Domain S → Spine.Carrier (R S)
    ConsumerDerivativePartialSum : Nat → Domain S → Spine.Carrier (R S)

    consumerSumMatchesGeneric : ∀ count point →
      Spine._≈_ (R S)
        (ConsumerPartialSum count point)
        (finitePartialSum S term count point)

    consumerDerivativeSumMatchesGeneric : ∀ count point →
      Spine._≈_ (R S)
        (ConsumerDerivativePartialSum count point)
        (finitePartialDerivativeSum S derivativeTerm count point)

    derivativeRespectsFunctionAndValueEquality :
      ∀ {f g df dg point} →
      (∀ x → Spine._≈_ (R S) (f x) (g x)) →
      Spine._≈_ (R S) df dg →
      DerivativeAt S g point dg →
      DerivativeAt S f point df

    reading : String

open FiniteSeriesRepresentationWeld public

compileConsumerFiniteSumDerivative :
  (S : SetoidDerivativeAdditiveSemantics) →
  {term derivativeTerm : Nat → Domain S → Spine.Carrier (R S)} →
  (termDerivative : ∀ index point →
    DerivativeAt S (term index) point (derivativeTerm index point)) →
  (W : FiniteSeriesRepresentationWeld S term derivativeTerm) →
  ∀ count point →
  DerivativeAt S
    (ConsumerPartialSum W count)
    point
    (ConsumerDerivativePartialSum W count point)
compileConsumerFiniteSumDerivative S termDerivative W count point =
  derivativeRespectsFunctionAndValueEquality W
    (λ x → Spine.≈-sym (R S) (consumerSumMatchesGeneric W count x))
    (Spine.≈-sym (R S) (consumerDerivativeSumMatchesGeneric W count point))
    (finiteSumDerivative S termDerivative count point)

record ReverseFiniteSumDerivativeObligations : Set where
  field
    zeroDerivativeRule : Set
    additionDerivativeRule : Set
    consumerFiniteSumRepresentationWeld : Set
    derivativeCongruenceUnderSetoidEquality : Set

open ReverseFiniteSumDerivativeObligations public

data TermwiseDerivativesAutomaticallyGiveFiniteSumDerivativeWithoutAddRule : Set where

termwiseNeedsAdditiveDerivativeSemantics :
  TermwiseDerivativesAutomaticallyGiveFiniteSumDerivativeWithoutAddRule → ⊥
termwiseNeedsAdditiveDerivativeSemantics ()

record Status : Set where
  field
    finiteSumInductionCompilerOwned : Bool
    representationWeldSurfaceOwned : Bool
    concreteDerivativeAddRuleClosed : Bool

    finiteSumInductionCompilerOwnedIsTrue : finiteSumInductionCompilerOwned ≡ true
    representationWeldSurfaceOwnedIsTrue : representationWeldSurfaceOwned ≡ true
    concreteDerivativeAddRuleClosedIsFalse : concreteDerivativeAddRuleClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { finiteSumInductionCompilerOwned = true
  ; representationWeldSurfaceOwned = true
  ; concreteDerivativeAddRuleClosed = false
  ; finiteSumInductionCompilerOwnedIsTrue = refl
  ; representationWeldSurfaceOwnedIsTrue = refl
  ; concreteDerivativeAddRuleClosedIsFalse = refl
  }
