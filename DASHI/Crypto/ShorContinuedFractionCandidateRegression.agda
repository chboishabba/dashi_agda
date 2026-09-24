module DASHI.Crypto.ShorContinuedFractionCandidateRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorContinuedFractionCandidateExact as Candidate

------------------------------------------------------------------------
-- RED regression.
--
-- The preferred Shor candidate producer must concretely derive continued-
-- fraction coefficients from the exact Fourier rational and scan the resulting
-- convergent denominators.  Success remains verifier-gated elsewhere.
------------------------------------------------------------------------

halfCoefficients :
  Candidate.continuedFractionCoefficientsFuel 3 1 2
  ≡ 0 ∷ 2 ∷ []
halfCoefficients = refl

halfConvergentDenominators :
  Candidate.convergentDenominators
    (0 ∷ 2 ∷ [])
    Candidate.initialConvergentState
  ≡ 1 ∷ 2 ∷ []
halfConvergentDenominators = refl

candidateExtractorExists :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  QFT.FourierSample → Nat
candidateExtractorExists = Candidate.continuedFractionPeriodCandidate
