module DASHI.Cognition.PNF.FiniteExpectedDecisionPotentialExact where

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.GenericExpectedFibreRateExact as FibreRate

------------------------------------------------------------------------
-- FINITE EXPECTED POTENTIAL OVER A FIBRE LAW
--
-- Active-inference / expected-free-energy calibration:
--   Karl Friston, "The free-energy principle: a unified brain theory?"
--   Nature Reviews Neuroscience 11 (2010), DOI 10.1038/nrn2787.
--
-- This module reuses the existing exact finite probability-mass carrier from
-- GenericExpectedFibreRateExact.  It proves the algebraic expectation
-- decomposition needed by the decision fibre without pretending that rational
-- local costs are already logarithmic surprisal, KL divergence, or the full
-- active-inference calculus.
------------------------------------------------------------------------

record PotentialTerm : Set where
  constructor potentialTerm
  field
    probability : FibreRate.ProbabilityAtom
    epistemicCost : ℚ
    pragmaticCost : ℚ

open PotentialTerm public

termMass : PotentialTerm → ℚ
termMass term = FibreRate.probabilityMass (probability term)

termEpistemic : PotentialTerm → ℚ
termEpistemic term = termMass term * epistemicCost term

termPragmatic : PotentialTerm → ℚ
termPragmatic term = termMass term * pragmaticCost term

termExpectedPotential : PotentialTerm → ℚ
termExpectedPotential term =
  termMass term * (epistemicCost term + pragmaticCost term)

expectedEpistemic : List PotentialTerm → ℚ
expectedEpistemic [] = 0ℚ
expectedEpistemic (term ∷ terms) =
  termEpistemic term + expectedEpistemic terms

expectedPragmatic : List PotentialTerm → ℚ
expectedPragmatic [] = 0ℚ
expectedPragmatic (term ∷ terms) =
  termPragmatic term + expectedPragmatic terms

expectedPotential : List PotentialTerm → ℚ
expectedPotential [] = 0ℚ
expectedPotential (term ∷ terms) =
  termExpectedPotential term + expectedPotential terms

expectedPotentialDecomposes : (terms : List PotentialTerm) →
  expectedPotential terms
  ≡ expectedEpistemic terms + expectedPragmatic terms
expectedPotentialDecomposes [] = solve-∀
expectedPotentialDecomposes (term ∷ terms)
  rewrite expectedPotentialDecomposes terms = solve-∀

totalProbability : List PotentialTerm → ℚ
totalProbability [] = 0ℚ
totalProbability (term ∷ terms) = termMass term + totalProbability terms

record NormalizedFinitePotentialLaw : Set where
  constructor normalizedFinitePotentialLaw
  field
    terms : List PotentialTerm
    normalized : totalProbability terms ≡ 1ℚ

open NormalizedFinitePotentialLaw public

normalizedExpectedPotentialStillDecomposes :
  (law : NormalizedFinitePotentialLaw) →
  expectedPotential (terms law)
  ≡ expectedEpistemic (terms law) + expectedPragmatic (terms law)
normalizedExpectedPotentialStillDecomposes law =
  expectedPotentialDecomposes (terms law)

------------------------------------------------------------------------
-- Link to the pre-existing finite expected-rate owner.  Each component is
-- already of the generic form "probability mass times local fibre cost".
------------------------------------------------------------------------

componentAsExpectedRate :
  (p e g : ℚ) → p * (e + g) ≡ p * e + p * g
componentAsExpectedRate p e g = solve-∀

------------------------------------------------------------------------
-- Boundary.  The exact theorem here is finite weighted expectation algebra.
-- A logarithm/KL/coding theorem requires an additional analytic realization.
------------------------------------------------------------------------

record FiniteExpectedPotentialBoundary : Set where
  constructor finiteExpectedPotentialBoundary
  field
    finiteExpectationExact : Bool
    epistemicPragmaticDecompositionExact : Bool
    logarithmicSurprisalImplementedHere : Bool
    KLDivergenceImplementedHere : Bool
    expectedPotentialDefinesSemanticIdentity : Bool

canonicalFiniteExpectedPotentialBoundary : FiniteExpectedPotentialBoundary
canonicalFiniteExpectedPotentialBoundary =
  finiteExpectedPotentialBoundary true true false false false
