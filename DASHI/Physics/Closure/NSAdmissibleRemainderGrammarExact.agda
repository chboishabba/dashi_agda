module DASHI.Physics.Closure.NSAdmissibleRemainderGrammarExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. Thomas Beale; Tosio Kato; Andrew Majda,
-- "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations", Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01212349.
--
-- James Serrin,
-- "On the Interior Regularity of Weak Solutions of the Navier--Stokes
-- Equations", Archive for Rational Mechanics and Analysis 9 (1962),
-- 187--195. DOI: 10.1007/BF00253344.
--
-- DASHI CONTRIBUTION
--
-- Make the anti-circularity condition structural.  A remainder leaf is not an
-- unrestricted rational wearing a label.  It contains a source term and the
-- proof appropriate to its class: initial-data boundedness, known-integral
-- finiteness, lower-order control, or dissipation absorption.  The source
-- authority also proves that each such certificate excludes dependence on the
-- target critical supremum, an uncontrolled BKM integral, and an uncontrolled
-- Serrin norm.  The fold can therefore consume only proof-carrying leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (ℚ; _+_)

data ForbiddenCircularDependency : Set where
  targetCriticalSupremum : ForbiddenCircularDependency
  uncontrolledBKMIntegral : ForbiddenCircularDependency
  uncontrolledSerrinNorm : ForbiddenCircularDependency

record RemainderSourceAuthority : Set₁ where
  field
    Source : Set
    value : Source → ℚ

    DependsOn : Source → ForbiddenCircularDependency → Set

    InitialDataBounded : Source → Set
    KnownTimeIntegralFinite : Source → Set
    LowerOrderControlled : Source → Set
    DissipationAbsorbable : Source → Set

    initialDataExcludesCircularity :
      ∀ source → InitialDataBounded source →
      ∀ dependency → DependsOn source dependency → ⊥

    knownIntegralExcludesCircularity :
      ∀ source → KnownTimeIntegralFinite source →
      ∀ dependency → DependsOn source dependency → ⊥

    lowerOrderExcludesCircularity :
      ∀ source → LowerOrderControlled source →
      ∀ dependency → DependsOn source dependency → ⊥

    dissipationExcludesCircularity :
      ∀ source → DissipationAbsorbable source →
      ∀ dependency → DependsOn source dependency → ⊥
open RemainderSourceAuthority public

NoForbiddenDependency :
  (authority : RemainderSourceAuthority) →
  Source authority → Set
NoForbiddenDependency authority source =
  ∀ dependency → DependsOn authority source dependency → ⊥

initialDataNoForbiddenDependency :
  ∀ authority source →
  InitialDataBounded authority source →
  NoForbiddenDependency authority source
initialDataNoForbiddenDependency authority source proof =
  initialDataExcludesCircularity authority source proof

knownIntegralNoForbiddenDependency :
  ∀ authority source →
  KnownTimeIntegralFinite authority source →
  NoForbiddenDependency authority source
knownIntegralNoForbiddenDependency authority source proof =
  knownIntegralExcludesCircularity authority source proof

lowerOrderNoForbiddenDependency :
  ∀ authority source →
  LowerOrderControlled authority source →
  NoForbiddenDependency authority source
lowerOrderNoForbiddenDependency authority source proof =
  lowerOrderExcludesCircularity authority source proof

dissipationNoForbiddenDependency :
  ∀ authority source →
  DissipationAbsorbable authority source →
  NoForbiddenDependency authority source
dissipationNoForbiddenDependency authority source proof =
  dissipationExcludesCircularity authority source proof

data AdmissibleRemainder
    (authority : RemainderSourceAuthority) : Set where
  initialDataConstant :
    (source : Source authority) →
    InitialDataBounded authority source →
    AdmissibleRemainder authority

  knownTimeIntegral :
    (source : Source authority) →
    KnownTimeIntegralFinite authority source →
    AdmissibleRemainder authority

  lowerOrderControlled :
    (source : Source authority) →
    LowerOrderControlled authority source →
    AdmissibleRemainder authority

  absorbedDissipation :
    (source : Source authority) →
    DissipationAbsorbable authority source →
    AdmissibleRemainder authority

  _⊕_ :
    AdmissibleRemainder authority →
    AdmissibleRemainder authority →
    AdmissibleRemainder authority

infixr 6 _⊕_

evaluateRemainder :
  ∀ {authority} → AdmissibleRemainder authority → ℚ
evaluateRemainder {authority} (initialDataConstant source _) =
  value authority source
evaluateRemainder {authority} (knownTimeIntegral source _) =
  value authority source
evaluateRemainder {authority} (lowerOrderControlled source _) =
  value authority source
evaluateRemainder {authority} (absorbedDissipation source _) =
  value authority source
evaluateRemainder (left ⊕ right) =
  evaluateRemainder left + evaluateRemainder right

foldAdmissibleRemainder :
  ∀ {authority} {A : Set} →
  (initialHandler :
    ∀ source → InitialDataBounded authority source → A) →
  (knownIntegralHandler :
    ∀ source → KnownTimeIntegralFinite authority source → A) →
  (lowerOrderHandler :
    ∀ source → LowerOrderControlled authority source → A) →
  (dissipationHandler :
    ∀ source → DissipationAbsorbable authority source → A) →
  (combine : A → A → A) →
  AdmissibleRemainder authority → A
foldAdmissibleRemainder initialHandler knownIntegralHandler
    lowerOrderHandler dissipationHandler combine
    (initialDataConstant source proof) =
  initialHandler source proof
foldAdmissibleRemainder initialHandler knownIntegralHandler
    lowerOrderHandler dissipationHandler combine
    (knownTimeIntegral source proof) =
  knownIntegralHandler source proof
foldAdmissibleRemainder initialHandler knownIntegralHandler
    lowerOrderHandler dissipationHandler combine
    (lowerOrderControlled source proof) =
  lowerOrderHandler source proof
foldAdmissibleRemainder initialHandler knownIntegralHandler
    lowerOrderHandler dissipationHandler combine
    (absorbedDissipation source proof) =
  dissipationHandler source proof
foldAdmissibleRemainder initialHandler knownIntegralHandler
    lowerOrderHandler dissipationHandler combine (left ⊕ right) =
  combine
    (foldAdmissibleRemainder initialHandler knownIntegralHandler
      lowerOrderHandler dissipationHandler combine left)
    (foldAdmissibleRemainder initialHandler knownIntegralHandler
      lowerOrderHandler dissipationHandler combine right)

admissibleRemainderEvaluationIsCanonical :
  ∀ {authority} (remainder : AdmissibleRemainder authority) →
  foldAdmissibleRemainder
    (λ source _ → value authority source)
    (λ source _ → value authority source)
    (λ source _ → value authority source)
    (λ source _ → value authority source)
    _+_ remainder
  ≡ evaluateRemainder remainder
admissibleRemainderEvaluationIsCanonical
    (initialDataConstant source proof) = refl
admissibleRemainderEvaluationIsCanonical
    (knownTimeIntegral source proof) = refl
admissibleRemainderEvaluationIsCanonical
    (lowerOrderControlled source proof) = refl
admissibleRemainderEvaluationIsCanonical
    (absorbedDissipation source proof) = refl
admissibleRemainderEvaluationIsCanonical (left ⊕ right)
  rewrite admissibleRemainderEvaluationIsCanonical left
        | admissibleRemainderEvaluationIsCanonical right =
  refl
