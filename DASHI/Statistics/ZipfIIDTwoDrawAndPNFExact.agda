module DASHI.Statistics.ZipfIIDTwoDrawAndPNFExact where

-- FINITE ZIPF / OCCUPANCY / PROVENANCE MAX-CUT, 2026-10-27.
--
-- Classical collision/occupancy and finite expectation identities retain
-- original mathematical ownership. This source-written DAG adapter is
-- credited to Johl Brown with OpenAI ChatGPT assistance.
--
-- Assumptions: explicitly supplied normalized rational law; two draws are
-- IID with replacement. This is NOT an empirical law, a general stochastic
-- process, entropy-scaling proof, RH result or fluid-regularity theorem.
-- Source-written only: Agda kernel has NOT verified this new module.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; 2ℚ; _+_; _*_; _≤_)
open import Data.Rational.Properties as ℚP using (+-identityʳ; *-identityʳ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Cognition.PNF.GenericExpectedFibreRateExact as Expected
import DASHI.Statistics.ZipfFamilyFiniteExact as Zipf

------------------------------------------------------------------------
-- Consumer of the OWNED normalized finite probability carrier.
-- This does not construct automatic weights from finite Hurwitz terms.
-- Mass positivity and normalization are supplied as explicit obligations.
------------------------------------------------------------------------

record FiniteRankProbabilityAdapter : Set where
  constructor finite-rank-probability-adapter
  field
    supportSize shift exponent : Nat
    atoms : List Expected.ProbabilityAtom
    normalized : Expected.probabilityTotal atoms ≡ 1ℚ
    rankModelReference : String
    sourceRootReference : String
    finiteZipfWeightIdentificationPaid : Bool

open FiniteRankProbabilityAdapter public

finiteRankConstantExpectation :
  (law : FiniteRankProbabilityAdapter) (rate : ℚ) →
  Expected.constantRateExpectation rate (atoms law) ≡ rate
finiteRankConstantExpectation law rate =
  Expected.normalizedConstantRateIsRate
    rate (atoms law) (normalized law)

------------------------------------------------------------------------
-- Two-symbol law as a physically meaningful two-draw IID finite cut.
-- q=1-p is a NORMALISATION PROOF, not an automatic statistical inference.
------------------------------------------------------------------------

record TwoRankIIDLaw : Set where
  constructor two-rank-iid-law
  field
    p q : ℚ
    nonnegativeP : 0ℚ ≤ p
    nonnegativeQ : 0ℚ ≤ q
    normalizedPQ : p + q ≡ 1ℚ
    samplingReference : String

open TwoRankIIDLaw public

canonicalProbabilityAtoms : TwoRankIIDLaw → List Expected.ProbabilityAtom
canonicalProbabilityAtoms law =
  Expected.probabilityAtom (p law) (nonnegativeP law) ∷
  Expected.probabilityAtom (q law) (nonnegativeQ law) ∷ []

atomsNormalize :
  (law : TwoRankIIDLaw) →
  Expected.probabilityTotal (canonicalProbabilityAtoms law) ≡ 1ℚ
atomsNormalize law =
  trans
    (cong (p law +_) (ℚP.+-identityʳ (q law)))
    (normalizedPQ law)

twoRankConstantExpectation :
  (law : TwoRankIIDLaw) (rate : ℚ) →
  Expected.constantRateExpectation rate (canonicalProbabilityAtoms law)
    ≡ rate
twoRankConstantExpectation law rate =
  Expected.normalizedConstantRateIsRate
    rate (canonicalProbabilityAtoms law) (atomsNormalize law)

iidTwoDrawCollision : TwoRankIIDLaw → ℚ
iidTwoDrawCollision law = p law * p law + q law * q law

iidTwoDrawMeanDistinct : TwoRankIIDLaw → ℚ
iidTwoDrawMeanDistinct law =
    (p law * p law) * 1ℚ
  + (p law * q law) * 2ℚ
  + (q law * p law) * 2ℚ
  + (q law * q law) * 1ℚ

-- Exactly four ordered outcomes: 00, 01, 10, 11.
-- Their probabilities factor because IID is part of the model.
iidTwoDrawMeanPlusCollisionIsTwo :
  (law : TwoRankIIDLaw) →
  iidTwoDrawMeanDistinct law + iidTwoDrawCollision law ≡ 2ℚ
iidTwoDrawMeanPlusCollisionIsTwo law =
  trans
    (solve (p law ∷ q law ∷ []))
    (trans
      (cong (λ total → 2ℚ * (total * total)) (normalizedPQ law))
      (trans
        (cong (2ℚ *_) (ℚP.*-identityʳ 1ℚ))
        (ℚP.*-identityʳ 2ℚ)))

------------------------------------------------------------------------
-- No false promotion of an explicitly supplied mass law to a universal
-- statement about observed textual corpora or Hilberg entropy exponents.
------------------------------------------------------------------------

record ZipfOccupancyBoundary : Set where
  constructor zipf-occupancy-boundary
  field
    canonicalPNFExpectedRateReused : Bool
    iidSamplingAssumptionExplicit : Bool
    finiteZipfNormalizerAutomaticallyKernelProved : Bool
    empiricalHeapsLawProved : Bool
    twoRankCollisionIdentityConstructed : Bool
    historicalAndOriginalAuthorRootsRetained : Bool

canonicalZipfOccupancyBoundary : ZipfOccupancyBoundary
canonicalZipfOccupancyBoundary =
  zipf-occupancy-boundary true true false false true true

originalAuthorityStillTyped :
  Zipf.authority Zipf.hilberg ≡ Zipf.unverifiedHypothesis
originalAuthorityStillTyped = refl
