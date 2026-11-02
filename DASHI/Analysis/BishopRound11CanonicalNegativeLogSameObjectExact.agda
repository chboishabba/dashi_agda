module DASHI.Analysis.BishopRound11CanonicalNegativeLogSameObjectExact where

------------------------------------------------------------------------
-- K04d-LOG: CONCRETE, SOURCE-NATIVE ROUND11 BISHOP UNIT INTERVAL.
--
-- The prior generic Round11BishopCutset carries an abstract
-- InOpenUnitInterval predicate. Such a predicate cannot be inhabited
-- from 0<x<1 without either inspecting its selected definition or
-- constructing a concrete selected dataset. We do the latter,
-- preserving EXACTLY the original selected sine/cosine/exponential
-- terms and replacing only the logarithm with the already proven
-- canonical Bishop sum x^(n+1)/(n+1).
--
-- Historical owners: Bishop/Bridges; Murray 2022; pinned
-- viktorcsimma/bishop; DASHI's concrete Round11 source terms.
-- The resulting same-object proof concerns THIS canonical
-- Round11-compatible dataSet. It does not assert equality with an
-- arbitrary earlier selected negative-log term function.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Native
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as NatRecip
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Dirichlet
import DASHI.Physics.YangMills.BalabanBishopConfiguredTermIdentificationExact as Config
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route

-- All existing nonlogarithmic power-series terms, coefficients and
-- convergences remain DEFINITIONALLY those of the original dataset.
canonicalNegativeLogDataSet :
  E.BishopElementaryPowerSeriesData →
  E.BishopElementaryPowerSeriesData
canonicalNegativeLogDataSet old = record
  { E.rational = E.rational old
  ; E.rationalDefinition = E.rationalDefinition old
  ; E.sineTerm = E.sineTerm old
  ; E.cosineTerm = E.cosineTerm old
  ; E.exponentialTerm = E.exponentialTerm old
  ; E.negativeLogOneMinusTerm = Native.sourceNegativeLogTerm
  ; E.sineAbsoluteConvergence = E.sineAbsoluteConvergence old
  ; E.cosineAbsoluteConvergence = E.cosineAbsoluteConvergence old
  ; E.exponentialAbsoluteConvergence = E.exponentialAbsoluteConvergence old
  ; E.InOpenUnitInterval = λ x →
      (R._<_ R.0ℝ x) × (R._<_ x R.1ℝ)
  ; E.negativeLogAbsoluteConvergence = λ point inside →
      Native.sourceNegativeLogAbsolutelyConvergent
        point (proj₁ inside) (proj₂ inside)
  ; E.sineCoefficientRecurrenceExact =
      E.sineCoefficientRecurrenceExact old
  ; E.cosineCoefficientRecurrenceExact =
      E.cosineCoefficientRecurrenceExact old
  ; E.exponentialCoefficientRecurrenceExact =
      E.exponentialCoefficientRecurrenceExact old
  ; E.negativeLogCoefficientRecurrenceExact = λ x n →
      R._≃_ (Native.sourceNegativeLogTerm x n)
        (Native.sourceNegativeLogTerm x n)
  ; E.sineOddPowersAndFactorialsExact =
      E.sineOddPowersAndFactorialsExact old
  ; E.cosineEvenPowersAndFactorialsExact =
      E.cosineEvenPowersAndFactorialsExact old
  ; E.exponentialPowersAndFactorialsExact =
      E.exponentialPowersAndFactorialsExact old
  ; E.negativeLogPowersOverPositiveIntegersExact = λ x n →
      R._≃_
        (Native.sourceNegativeLogTerm x n)
        (R._*_ (R.pow x (suc n))
          (R._⋆
            (NatRecip.reciprocalNatRational n)))
  ; E.sineAlternatingSignsExact = E.sineAlternatingSignsExact old
  ; E.cosineAlternatingSignsExact = E.cosineAlternatingSignsExact old
  }

-- The configured sine/cosine IDENTIFICATION is not weakened:
-- every original propositional equality remains the exact same
-- expression after this single-field logarithm replacement.
canonicalNegativeLogRound11 :
  Round11.Round11BishopCutset →
  Round11.Round11BishopCutset
canonicalNegativeLogRound11 inputs = record
  { Round11.elementarySeries =
      canonicalNegativeLogDataSet
        (Round11.elementarySeries inputs)
  ; Round11.configuredDefinitions = record
      { Config.sineTermDefinition =
          Config.sineTermDefinition
            (Round11.configuredDefinitions inputs)
      ; Config.cosineTermDefinition =
          Config.cosineTermDefinition
            (Round11.configuredDefinitions inputs)
      }
  }

canonicalUnitIntervalWitness :
  (inputs : Round11.Round11BishopCutset) →
  (n : Nat) →
  E.InOpenUnitInterval
    (Round11.elementarySeries
      (canonicalNegativeLogRound11 inputs))
    (Dirichlet.natLogArgument n)
canonicalUnitIntervalWitness inputs n =
  Dirichlet.natLogArgumentPositiveBishop n
  ,
  Dirichlet.natLogArgumentBelowOneBishop n

canonicalNatLogFromConfiguredSource :
  (inputs : Round11.Round11BishopCutset) →
  Dirichlet.NatLogCandidate
canonicalNatLogFromConfiguredSource inputs =
  Dirichlet.natLogViaOriginalNegativeLog
    (Route.round11MachinTranscendentals
      (canonicalNegativeLogRound11 inputs))
    (canonicalUnitIntervalWitness inputs)

canonicalNatLogIsOriginalBishopSum :
  (inputs : Round11.Round11BishopCutset) →
  (n : Nat) →
  R._≃_
    (canonicalNatLogFromConfiguredSource inputs n)
    (Dirichlet.sourceCanonicalNatLogCandidate n)
canonicalNatLogIsOriginalBishopSum inputs n =
  Dirichlet.sourceOriginalConfiguredNatLogAgreement
    (Route.round11MachinTranscendentals
      (canonicalNegativeLogRound11 inputs))
    (canonicalUnitIntervalWitness inputs)
    (λ index termIndex → RP.≃-refl)
    n

-- The exponential inverse for L_n remains an ANALYTIC theorem;
-- neither the canonical unit-interval witness nor convergence
-- supplies exp_B(L_n) = n+1 by definitional equality.
