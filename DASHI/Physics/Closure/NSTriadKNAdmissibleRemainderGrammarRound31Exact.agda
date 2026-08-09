module DASHI.Physics.Closure.NSTriadKNAdmissibleRemainderGrammarRound31Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: James Serrin.
-- Title: "On the Interior Regularity of Weak Solutions of the
-- Navier-Stokes Equations".
-- DOI: 10.1007/BF02392477.
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- DOI: 10.1002/cpa.3160370205.
--
-- DASHI CONTRIBUTION
--
-- Make the anti-circularity restriction on owner remainders structural.
-- A physical owner proof may use only:
--
--   * an initial/data-controlled constant;
--   * a known integrable critical coefficient;
--   * a lower-order controlled quantity;
--   * a declared fraction of dissipation;
--   * finite sums of those terms.
--
-- There is no constructor for an uncontrolled BKM integral, Serrin norm, or
-- target critical supremum.  Every grammar term is compiled exactly to the
-- existing owner language
--
--   eta D + A + B integralCritical.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; trans)

import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner

record ControlledRemainderEnvironment : Set where
  constructor controlled-remainder-environment
  field
    taxEnvironment : Owner.TaxEnvironment
    initialDataBudget : ℚ
    lowerOrderBudget : ℚ

open ControlledRemainderEnvironment public

data AdmissibleRemainder : Set where
  initialDataConstant : ℚ → AdmissibleRemainder
  knownCriticalIntegral : ℚ → AdmissibleRemainder
  lowerOrderControlled : ℚ → AdmissibleRemainder
  absorbedDissipation : ℚ → AdmissibleRemainder
  _⊕_ : AdmissibleRemainder → AdmissibleRemainder → AdmissibleRemainder

infixr 5 _⊕_

remainderEta : AdmissibleRemainder → ℚ
remainderEta (initialDataConstant coefficient) = 0ℚ
remainderEta (knownCriticalIntegral coefficient) = 0ℚ
remainderEta (lowerOrderControlled coefficient) = 0ℚ
remainderEta (absorbedDissipation coefficient) = coefficient
remainderEta (left ⊕ right) =
  remainderEta left + remainderEta right

remainderData :
  ControlledRemainderEnvironment → AdmissibleRemainder → ℚ
remainderData environment (initialDataConstant coefficient) =
  coefficient * initialDataBudget environment
remainderData environment (knownCriticalIntegral coefficient) = 0ℚ
remainderData environment (lowerOrderControlled coefficient) =
  coefficient * lowerOrderBudget environment
remainderData environment (absorbedDissipation coefficient) = 0ℚ
remainderData environment (left ⊕ right) =
  remainderData environment left + remainderData environment right

remainderCriticalCoefficient : AdmissibleRemainder → ℚ
remainderCriticalCoefficient (initialDataConstant coefficient) = 0ℚ
remainderCriticalCoefficient (knownCriticalIntegral coefficient) = coefficient
remainderCriticalCoefficient (lowerOrderControlled coefficient) = 0ℚ
remainderCriticalCoefficient (absorbedDissipation coefficient) = 0ℚ
remainderCriticalCoefficient (left ⊕ right) =
  remainderCriticalCoefficient left + remainderCriticalCoefficient right

evaluateRemainder :
  ControlledRemainderEnvironment → AdmissibleRemainder → ℚ
evaluateRemainder environment (initialDataConstant coefficient) =
  coefficient * initialDataBudget environment
evaluateRemainder environment (knownCriticalIntegral coefficient) =
  coefficient
  * Owner.integralCritical (taxEnvironment environment)
evaluateRemainder environment (lowerOrderControlled coefficient) =
  coefficient * lowerOrderBudget environment
evaluateRemainder environment (absorbedDissipation coefficient) =
  coefficient
  * Owner.dissipation (taxEnvironment environment)
evaluateRemainder environment (left ⊕ right) =
  evaluateRemainder environment left
  + evaluateRemainder environment right

remainderNormalForm :
  ∀ environment remainder →
  evaluateRemainder environment remainder
  ≡
  remainderEta remainder
    * Owner.dissipation (taxEnvironment environment)
  + remainderData environment remainder
  + remainderCriticalCoefficient remainder
    * Owner.integralCritical (taxEnvironment environment)
remainderNormalForm environment (initialDataConstant coefficient) =
  solve
    ( coefficient
    ∷ initialDataBudget environment
    ∷ Owner.dissipation (taxEnvironment environment)
    ∷ Owner.integralCritical (taxEnvironment environment)
    ∷ [])
remainderNormalForm environment (knownCriticalIntegral coefficient) =
  solve
    ( coefficient
    ∷ initialDataBudget environment
    ∷ lowerOrderBudget environment
    ∷ Owner.dissipation (taxEnvironment environment)
    ∷ Owner.integralCritical (taxEnvironment environment)
    ∷ [])
remainderNormalForm environment (lowerOrderControlled coefficient) =
  solve
    ( coefficient
    ∷ lowerOrderBudget environment
    ∷ Owner.dissipation (taxEnvironment environment)
    ∷ Owner.integralCritical (taxEnvironment environment)
    ∷ [])
remainderNormalForm environment (absorbedDissipation coefficient) =
  solve
    ( coefficient
    ∷ Owner.dissipation (taxEnvironment environment)
    ∷ Owner.integralCritical (taxEnvironment environment)
    ∷ [])
remainderNormalForm environment (left ⊕ right) =
  trans
    (cong₂ _+_
      (remainderNormalForm environment left)
      (remainderNormalForm environment right))
    (solve
      ( remainderEta left
      ∷ remainderEta right
      ∷ remainderData environment left
      ∷ remainderData environment right
      ∷ remainderCriticalCoefficient left
      ∷ remainderCriticalCoefficient right
      ∷ Owner.dissipation (taxEnvironment environment)
      ∷ Owner.integralCritical (taxEnvironment environment)
      ∷ []))

record GrammarOwnerBound
    (environment : ControlledRemainderEnvironment)
    (owner : Tax.TaxOwner)
    (production : ℚ)
    (remainder : AdmissibleRemainder) : Set where
  constructor grammar-owner-bound
  field
    productionBound :
      production ≤ evaluateRemainder environment remainder

open GrammarOwnerBound public

compileGrammarOwnerEstimate :
  ∀ {environment owner production remainder} →
  GrammarOwnerBound environment owner production remainder →
  Owner.AdmissibleOwnerEstimate (taxEnvironment environment)
compileGrammarOwnerEstimate
    {environment} {owner} {production} {remainder} bound =
  Owner.admissible-owner-estimate
    owner
    production
    (remainderEta remainder)
    (remainderData environment remainder)
    (remainderCriticalCoefficient remainder)
    (subst
      (λ upper → production ≤ upper)
      (remainderNormalForm environment remainder)
      (productionBound bound))

admissibleRemainderGrammarClosed : Bool
admissibleRemainderGrammarClosed = true

grammarCompilesToOwnerLanguage : Bool
grammarCompilesToOwnerLanguage = true

admissibleRemainderGrammarClosedIsTrue :
  admissibleRemainderGrammarClosed ≡ true
admissibleRemainderGrammarClosedIsTrue = refl

grammarCompilesToOwnerLanguageIsTrue :
  grammarCompilesToOwnerLanguage ≡ true
grammarCompilesToOwnerLanguageIsTrue = refl
