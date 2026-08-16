module DASHI.Physics.Closure.NSTriadKNComSelfMassNormalizationNoGoRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Historical 1955 conference source; no DOI assigned.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 62 FALSIFICATION RESULT
--
-- The concrete odd-P/Q pass exposed a normalization error before it reached
-- the physical B theorem.  If a same-cutoff Gram correlation is normalized by
-- the product of ITS OWN two fibre masses, then a unit one-dimensional fibre
-- self-normalizes to 1.  But the actual same-shell B coefficient is required
-- to obey
--
--     rowCoefficient <= 17/64 < 1.
--
-- Therefore the mass-product-normalized correlation cannot be the Round49
-- physical row-mass / squared-norm coefficient.  This is not a numerical
-- inconvenience: the two objects have different semantics.
--
-- The correct B target remains the literal Schur statement
--
--     ||oddPQ input||^2 <= rowMass * integralCritical,
--
-- whose same/adjacent row contributions are bounded by 17/64 and 65/512.
-- The concrete cross-Gram quantity introduced in Round62 is retained only as a
-- correlation diagnostic/falsifier; it must not be cited as the physical B
-- normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 1ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Active

sameShellTargetStrictlyBelowOne : Active.sameShellTarget < 1ℚ
sameShellTargetStrictlyBelowOne =
  toWitness {a? = Active.sameShellTarget <? 1ℚ} _

record SelfMassProductNormalizedCandidate : Set where
  field
    normalizedSelfValue : ℚ
    selfNormalizesToOne : normalizedSelfValue ≡ 1ℚ

open SelfMassProductNormalizedCandidate public

unitSelfCorrelationCandidate : SelfMassProductNormalizedCandidate
unitSelfCorrelationCandidate = record
  { normalizedSelfValue = 1ℚ
  ; selfNormalizesToOne = refl
  }

selfMassNormalizationCannotMeetSameShellTarget :
  (candidate : SelfMassProductNormalizedCandidate) →
  normalizedSelfValue candidate ≤ Active.sameShellTarget →
  ⊥
selfMassNormalizationCannotMeetSameShellTarget candidate candidateBound =
  ℚP.<-irrefl refl
    (ℚP.<-≤-trans
      sameShellTargetStrictlyBelowOne
      (subst
        (λ value → value ≤ Active.sameShellTarget)
        (selfNormalizesToOne candidate)
        candidateBound))

unitSelfCorrelationViolatesSameShellTarget :
  ¬ (normalizedSelfValue unitSelfCorrelationCandidate
      ≤ Active.sameShellTarget)
unitSelfCorrelationViolatesSameShellTarget =
  selfMassNormalizationCannotMeetSameShellTarget
    unitSelfCorrelationCandidate

selfMassProductNormalizationRejectedForPhysicalB : Bool
selfMassProductNormalizationRejectedForPhysicalB = true

crossGramRetainedOnlyAsDiagnostic : Bool
crossGramRetainedOnlyAsDiagnostic = true

selfMassProductNormalizationRejectedForPhysicalBIsTrue :
  selfMassProductNormalizationRejectedForPhysicalB ≡ true
selfMassProductNormalizationRejectedForPhysicalBIsTrue = refl

crossGramRetainedOnlyAsDiagnosticIsTrue :
  crossGramRetainedOnlyAsDiagnostic ≡ true
crossGramRetainedOnlyAsDiagnosticIsTrue = refl
