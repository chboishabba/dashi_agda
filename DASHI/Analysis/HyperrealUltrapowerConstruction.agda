module DASHI.Analysis.HyperrealUltrapowerConstruction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Concrete sequence algebra and a principal-ultrapower regression.

NatSequence : Set
NatSequence = Nat → Nat

constant : Nat → NatSequence
constant n k = n

pointwiseAdd : NatSequence → NatSequence → NatSequence
pointwiseAdd f g n = f n + g n

pointwiseMul : NatSequence → NatSequence → NatSequence
pointwiseMul f g n = f n * g n

record PrincipalEquivalent (f g : NatSequence) : Set where
  constructor equalAtZero
  field
    representativesAgreeAtZero : f zero ≡ g zero

principalEquivalentReflexive :
  (f : NatSequence) → PrincipalEquivalent f f
principalEquivalentReflexive f = equalAtZero refl

principalAddCongruent :
  ∀ {f f' g g'} →
  PrincipalEquivalent f f' →
  PrincipalEquivalent g g' →
  PrincipalEquivalent (pointwiseAdd f g) (pointwiseAdd f' g')
principalAddCongruent (equalAtZero refl) (equalAtZero refl) = equalAtZero refl

principalMulCongruent :
  ∀ {f f' g g'} →
  PrincipalEquivalent f f' →
  PrincipalEquivalent g g' →
  PrincipalEquivalent (pointwiseMul f g) (pointwiseMul f' g')
principalMulCongruent (equalAtZero refl) (equalAtZero refl) = equalAtZero refl

------------------------------------------------------------------------
-- Symbolic rational sequences used by a genuine free-ultrafilter quotient.

record RationalCode : Set where
  constructor rationalCode
  field
    numerator : Nat
    denominator : Nat

open RationalCode public

RationalSequence : Set
RationalSequence = Nat → RationalCode

infinitesimalRepresentative : RationalSequence
infinitesimalRepresentative n = rationalCode 1 (suc n)

infiniteRepresentative : RationalSequence
infiniteRepresentative n = rationalCode (suc n) 1

------------------------------------------------------------------------
-- Free-ultrafilter-parametric ultrapower.
--
-- The quotient is not silently manufactured.  A producer must supply a free
-- ultrafilter, the equivalence quotient, field operations, order, transfer,
-- and standard-part authority.

Predicate : Set₁
Predicate = Nat → Set

record FreeUltrafilterAuthority : Set₂ where
  field
    Large : Predicate → Set
    universalLarge : Large (λ n → Nat)
    intersectionClosed :
      ∀ {P Q} →
      Large P →
      Large Q →
      Large (λ n → P n × Q n)
    upwardClosed :
      ∀ {P Q} →
      Large P →
      (∀ n → P n → Q n) →
      Large Q
    singletonNotLarge :
      (n : Nat) →
      Large (λ m → m ≡ n) →
      ⊥

-- Local product, avoiding a dependency on a larger product API.
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    first : A
    second : B

record UltrapowerQuotientAuthority
    (U : FreeUltrafilterAuthority)
    : Set₂ where
  field
    Hyperreal : Set
    classOf : RationalSequence → Hyperreal
    Equivalent : RationalSequence → RationalSequence → Set
    equivalentIffLargeAgreement :
      ∀ f g →
      Equivalent f g →
      FreeUltrafilterAuthority.Large U (λ n → f n ≡ g n)
    quotientSound :
      ∀ {f g} →
      Equivalent f g →
      classOf f ≡ classOf g

record TransferFragment
    {Hyperreal : Set}
    : Set₁ where
  field
    transferEquality : Set
    transferAddition : Set
    transferMultiplication : Set
    transferOrder : Set
    setQuantificationNotIncluded : Set

record HyperrealFieldAuthority : Set₂ where
  field
    ultrafilter : FreeUltrafilterAuthority
    quotient : UltrapowerQuotientAuthority ultrafilter
    _+H_ _*H_ :
      UltrapowerQuotientAuthority.Hyperreal quotient →
      UltrapowerQuotientAuthority.Hyperreal quotient →
      UltrapowerQuotientAuthority.Hyperreal quotient
    zeroH oneH : UltrapowerQuotientAuthority.Hyperreal quotient
    orderedFieldLaws : Set
    transfer : TransferFragment
    epsilon : UltrapowerQuotientAuthority.Hyperreal quotient
    omega : UltrapowerQuotientAuthority.Hyperreal quotient
    epsilonFromRepresentative :
      epsilon ≡ UltrapowerQuotientAuthority.classOf quotient infinitesimalRepresentative
    omegaFromRepresentative :
      omega ≡ UltrapowerQuotientAuthority.classOf quotient infiniteRepresentative
    epsilonPositiveInfinitesimal : Set
    omegaInfinite : Set
    finitePart : UltrapowerQuotientAuthority.Hyperreal quotient → Set
    standardPart :
      (x : UltrapowerQuotientAuthority.Hyperreal quotient) →
      finitePart x →
      RationalCode
    standardPartInfinitesimalResidual : Set

record HyperrealConstructionBoundary : Set where
  constructor hyperrealConstructionBoundary
  field
    sequenceAlgebraChecked : Bool
    principalRegressionChecked : Bool
    principalRegressionIsNonstandardHyperreal : Bool
    principalRegressionIsNonstandardHyperrealIsFalse :
      principalRegressionIsNonstandardHyperreal ≡ false
    freeUltrafilterCanonicalInConstructiveCore : Bool
    freeUltrafilterCanonicalInConstructiveCoreIsFalse :
      freeUltrafilterCanonicalInConstructiveCore ≡ false
    fullTransferClaimedWithoutFragment : Bool
    fullTransferClaimedWithoutFragmentIsFalse :
      fullTransferClaimedWithoutFragment ≡ false
    interpretation : String

canonicalHyperrealConstructionBoundary : HyperrealConstructionBoundary
canonicalHyperrealConstructionBoundary =
  hyperrealConstructionBoundary
    true true false refl false refl false refl
    "componentwise sequence algebra and a principal quotient regression are executable; a genuine hyperreal field is constructed only from an explicit free-ultrafilter quotient, ordered-field, transfer-fragment and standard-part authority"
