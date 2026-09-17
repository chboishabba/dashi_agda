module DASHI.Crypto.ShorContinuedFractionCandidateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _==_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat using (_/_; _%_)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Crypto.RSAArithmeticCore as RSA
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as PowModWeld

------------------------------------------------------------------------
-- PRIMARY SOURCE / ATTRIBUTION
--
-- Peter W. Shor,
-- "Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms
--  on a Quantum Computer",
-- SIAM Journal on Computing 26(5), 1484-1509 (1997).
-- DOI: 10.1137/S0097539795293172
--
-- DASHI CONTRIBUTION
--
-- Provide one concrete fail-closed producer for the existing
-- FourierSample -> candidate-order seam:
--
--   exact sample numerator/denominator
--     -> finite Euclidean continued-fraction coefficients
--     -> convergent denominators
--     -> first positive denominator satisfying a^q mod N = 1.
--
-- The producer is intentionally NOT an order certificate.  In particular,
-- satisfying the period equation does not prove minimality.  The existing
-- `ExactOrderCertificate` verifier remains the only route by which a produced
-- candidate becomes a successful Shor recovery in this repository.
--
-- The Euclidean recursion is fuelled explicitly, so termination does not rely
-- on an imported analytic or well-founded theorem.  For the canonical Fourier
-- sample k/Q the chosen fuel is suc Q.
------------------------------------------------------------------------

record ShorContinuedFractionSourceReceipt : Set where
  constructor shorContinuedFractionSourceReceipt
  field
    author : String
    title : String
    publication : String
    doi : String
    sourceRole : String

open ShorContinuedFractionSourceReceipt public

canonicalShorContinuedFractionSourceReceipt :
  ShorContinuedFractionSourceReceipt
canonicalShorContinuedFractionSourceReceipt =
  shorContinuedFractionSourceReceipt
    "Peter W. Shor"
    "Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer"
    "SIAM Journal on Computing 26(5), 1484-1509 (1997)"
    "10.1137/S0097539795293172"
    "algorithmic source/context; DASHI owns the concrete producer and verifier separation"

------------------------------------------------------------------------
-- Finite Euclidean continued-fraction coefficients.
------------------------------------------------------------------------

continuedFractionCoefficientsFuel :
  Nat → Nat → Nat → List Nat
continuedFractionCoefficientsFuel zero numerator denominator = []
continuedFractionCoefficientsFuel (suc fuel) numerator zero = []
continuedFractionCoefficientsFuel (suc fuel) numerator (suc denominator) =
  (numerator / suc denominator)
  ∷ continuedFractionCoefficientsFuel
      fuel
      (suc denominator)
      (numerator % suc denominator)

continuedFractionCoefficients :
  QFT.FourierSample → List Nat
continuedFractionCoefficients sample =
  continuedFractionCoefficientsFuel
    (suc (QFT.denominator sample))
    (QFT.numerator sample)
    (QFT.denominator sample)

------------------------------------------------------------------------
-- Canonical convergent recurrence.
------------------------------------------------------------------------

record ConvergentState : Set where
  constructor convergentState
  field
    pPreviousPrevious : Nat
    pPrevious : Nat
    qPreviousPrevious : Nat
    qPrevious : Nat

open ConvergentState public

initialConvergentState : ConvergentState
initialConvergentState =
  convergentState 0 1 1 0

convergentStep :
  Nat → ConvergentState → ConvergentState
convergentStep coefficient state =
  convergentState
    (pPrevious state)
    (coefficient * pPrevious state + pPreviousPrevious state)
    (qPrevious state)
    (coefficient * qPrevious state + qPreviousPrevious state)

convergentDenominators :
  List Nat → ConvergentState → List Nat
convergentDenominators [] state = []
convergentDenominators (coefficient ∷ coefficients) state =
  qPrevious next
  ∷ convergentDenominators coefficients next
  where
    next : ConvergentState
    next = convergentStep coefficient state

sampleConvergentDenominators :
  QFT.FourierSample → List Nat
sampleConvergentDenominators sample =
  convergentDenominators
    (continuedFractionCoefficients sample)
    initialConvergentState

------------------------------------------------------------------------
-- Candidate screening by the modular period equation.
------------------------------------------------------------------------

periodEquationHolds :
  (N a : Nat) →
  B369.NonZero N →
  Nat → Bool
periodEquationHolds N a nNonZero zero = false
periodEquationHolds N a nNonZero (suc q) =
  RSA.powMod a (suc q) N {{nNonZero}} == 1

firstPeriodEquationCandidate :
  (N a : Nat) →
  B369.NonZero N →
  List Nat → Nat
firstPeriodEquationCandidate N a nNonZero [] = 0
firstPeriodEquationCandidate N a nNonZero (candidate ∷ candidates)
  with periodEquationHolds N a nNonZero candidate
... | true = candidate
... | false = firstPeriodEquationCandidate N a nNonZero candidates

continuedFractionPeriodCandidate :
  ∀ {N a r} →
  Order.ModularOrderProblem N a r →
  QFT.FourierSample → Nat
continuedFractionPeriodCandidate {N} {a} P sample =
  firstPeriodEquationCandidate
    N a
    (PowModWeld.orderModulusNonZero P)
    (sampleConvergentDenominators sample)

------------------------------------------------------------------------
-- Boundary / WrongType firewalls.
------------------------------------------------------------------------

data PeriodEquationCandidateCreatesExactOrderCertificate : Set where

data ConcreteExtractorCreatesSuccessProbability : Set where

periodEquationCandidateDoesNotCreateExactOrderCertificate :
  PeriodEquationCandidateCreatesExactOrderCertificate → ⊥
periodEquationCandidateDoesNotCreateExactOrderCertificate ()

concreteExtractorDoesNotCreateSuccessProbability :
  ConcreteExtractorCreatesSuccessProbability → ⊥
concreteExtractorDoesNotCreateSuccessProbability ()

record ShorContinuedFractionCandidateBoundary : Set where
  constructor shorContinuedFractionCandidateBoundary
  field
    exactFourierRationalConsumed : Bool
    euclideanCoefficientProducerConstructed : Bool
    convergentRecurrenceConstructed : Bool
    positivePeriodEquationScreenConstructed : Bool
    exactOrderMinimalityProvedHere : Bool
    candidateAlwaysRecoversOrderProvedHere : Bool
    continuedFractionSuccessProbabilityProvedHere : Bool
    quantumSamplingProbabilityProvedHere : Bool

canonicalShorContinuedFractionCandidateBoundary :
  ShorContinuedFractionCandidateBoundary
canonicalShorContinuedFractionCandidateBoundary =
  shorContinuedFractionCandidateBoundary
    true true true true false false false false
