module DASHI.Foundations.OdrzywolekGeneratedUnitObstruction where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Foundations.TernaryElementaryOperatorCandidate
open import DASHI.Foundations.TernaryEMLDecision

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- A genuine obstruction for the proposed ternary formula.
--
-- Its first argument occurs below `log`.  Hence a domain which requires that
-- denominator to be nonzero cannot accept the diagonally generated unit once
-- `log 1 = 0`.  This does not refute every possible ternary representation,
-- but it proves that the naive "generate 1, then reuse it in every slot" route
-- is unavailable on the ordinary logarithmic domain.

record OdrzywolekFirstArgumentAuthority
  (M : ExpLogDivisionModel) : Set₁ where
  field
    zeroS : Scalar M
    CandidateDomain : Scalar M → Set

    diagonalIsOne :
      ∀ a →
      CandidateDomain a →
      odrzywolekTernary M a a a ≡ oneS M

    logOneIsZero :
      logS M (oneS M) ≡ zeroS

open OdrzywolekFirstArgumentAuthority public

validOdrzywolekFirstArgument :
  ∀ {M : ExpLogDivisionModel} →
  OdrzywolekFirstArgumentAuthority M →
  Scalar M →
  Set
validOdrzywolekFirstArgument {M} A x = logS M x ≢ zeroS A

generatedUnitInvalidInFirstArgument :
  ∀ {M : ExpLogDivisionModel} →
  (A : OdrzywolekFirstArgumentAuthority M) →
  ∀ a →
  CandidateDomain A a →
  validOdrzywolekFirstArgument A (odrzywolekTernary M a a a) →
  ⊥
generatedUnitInvalidInFirstArgument {M} A a admissible firstOK =
  firstOK logGeneratedIsZero
  where
    logGeneratedIsZero :
      logS M (odrzywolekTernary M a a a) ≡ zeroS A
    logGeneratedIsZero
      rewrite diagonalIsOne A a admissible =
      logOneIsZero A

odrzywolekGeneratedUnitDomainObstruction :
  ∀ {M : ExpLogDivisionModel} →
  OdrzywolekFirstArgumentAuthority M →
  TernaryDomainObstruction
odrzywolekGeneratedUnitDomainObstruction {M} A =
  record
    { Value = Scalar M
    ; CandidateDomain = CandidateDomain A
    ; generatedUnit = λ a → odrzywolekTernary M a a a
    ; unitValue = oneS M
    ; validFirstArgument = validOdrzywolekFirstArgument A
    ; diagonalGeneratesUnit = diagonalIsOne A
    ; generatedUnitCannotBeFirstArgument =
        generatedUnitInvalidInFirstArgument A
    }
