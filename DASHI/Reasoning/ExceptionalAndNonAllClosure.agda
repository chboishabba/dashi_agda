module DASHI.Reasoning.ExceptionalAndNonAllClosure where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.CantorDiagonalCore as Cantor

------------------------------------------------------------------------
-- Two distinct closure forms.
--
-- ExceptionalClosure scopes a law to a lawful subdomain and carries an
-- explicitly outside witness.  NonAllClosure keeps pointwise/local coverage
-- separate from the existence of a global totalisation witness.
--
-- This avoids encoding Lacan's formulae of sexuation as two inconsistent
-- conjunctions in ordinary first-order logic over one undifferentiated domain.
------------------------------------------------------------------------

record ExceptionalClosure
  (A : Set)
  (Lawful GoverningPredicate : A → Set) : Set₁ where
  field
    exception : A
    lawfulCoverage :
      ∀ x → Lawful x → GoverningPredicate x
    exceptionOutsideLawfulDomain :
      ¬ Lawful exception
    closureDependsOnNamedException : Bool
    exceptionIsEmpiricalPersonClaimed : Bool

record GlobalTotalisation
  (A Code : Set)
  (LocalPredicate : A → Set) : Set₁ where
  field
    code : Code
    representsLocal : Code → A → Set
    codeCoversEveryLocal :
      ∀ x → LocalPredicate x → representsLocal code x
    noResidualOutsideCodeClaimed : Bool

record NonAllClosure
  (A Code : Set)
  (LocalPredicate : A → Set) : Set₁ where
  field
    localCoverage : ∀ x → LocalPredicate x
    noCertifiedGlobalTotalisation :
      ¬ GlobalTotalisation A Code LocalPredicate
    exceptionRequiredForLocalCoverage : Bool
    openFieldTemporallyLaterThanExceptionClosureClaimed : Bool

------------------------------------------------------------------------
-- Cantorian non-all: an A-indexed family of predicates omits its diagonal.
------------------------------------------------------------------------

CantorianNonAll : Set → Set₁
CantorianNonAll A =
  ∀ enumeration →
  Σ (Cantor.Pred A) λ predicate →
    Cantor.NotInImage enumeration predicate

cantorianNonAll : ∀ A → CantorianNonAll A
cantorianNonAll A enumeration =
  Cantor.Diagonal enumeration ,
  Cantor.diagonalNotInImage enumeration

record PredicateCompactification (A : Set) : Set₁ where
  field
    openGround : Cantor.Pred A
    closedPresentation : Cantor.Pred A
    compactify : Cantor.Pred A → Cantor.Pred A
    presentationProducedByCompactification :
      closedPresentation ≈ₚ compactify openGround
    distinguishedExceptionLabel : String
    groundLogicallyPrior : Bool
    compactificationCreatesGroundClaimed : Bool
  where
  infix 4 _≈ₚ_
  _≈ₚ_ = Cantor._≈ₚ_

record ClosureAuthorityBoundary : Set where
  field
    exceptionalAndNonAllDistinguished : Bool
    localCoverageImpliesGlobalCode : Bool
    cantorWitnessesOneNonAllPattern : Bool
    everyNonAllFieldIsPowerSetClaimed : Bool
    nonAllGroundCanBeLogicallyPrior : Bool
    sexuationEmpiricallyClassifiesPersons : Bool
    interpretiveNote : String

canonicalClosureAuthorityBoundary : ClosureAuthorityBoundary
canonicalClosureAuthorityBoundary = record
  { exceptionalAndNonAllDistinguished = true
  ; localCoverageImpliesGlobalCode = false
  ; cantorWitnessesOneNonAllPattern = true
  ; everyNonAllFieldIsPowerSetClaimed = false
  ; nonAllGroundCanBeLogicallyPrior = true
  ; sexuationEmpiricallyClassifiesPersons = false
  ; interpretiveNote =
      "The all-with-exception and non-all are represented as distinct closure structures; Cantor supplies only a specific checked no-totalisation witness."
  }
