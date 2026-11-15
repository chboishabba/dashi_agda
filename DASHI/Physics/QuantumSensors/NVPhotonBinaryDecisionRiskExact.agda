module DASHI.Physics.QuantumSensors.NVPhotonBinaryDecisionRiskExact where

-- Exact single-shot decision-risk algebra for the actual NV photon response
-- type owned by Diamond MCG #1238. No new probability ontology.
-- Equal priors and one photon/no-photon trial, not a calibrated
-- multi-shot Poisson or physical quantum-gate experiment.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Physics.QuantumSensors.NVPhotonBinaryLikelihoodExact as Photon
import DASHI.Physics.QuantumSensors.NVPhotonObserverRefinementExact as Observer

-- Two prepared spin levels, positive = c0, negative = c2.
-- Decision rule: photon -> c0; noPhoton -> c2.
record OneShotBinaryTest : Set₁ where
  constructor one-shot-test
  field
    model : Observer.ConditionalPhotonModel
open OneShotBinaryTest public

plusResponse minusResponse : OneShotBinaryTest → Photon.BinaryPhotonLikelihood
plusResponse t = Observer.response (model t) C3.c0
minusResponse t = Observer.response (model t) C3.c2

-- With equal prior weights, these are TWICE the corresponding
-- success/error probabilities, with complementary Bernoulli fractions
-- calculated as 1-p from the existing normalized source likelihood.
twiceSuccess : OneShotBinaryTest → ℚ
twiceSuccess t =
  Photon.photon (plusResponse t) +
  (1ℚ - Photon.photon (minusResponse t))

twiceError : OneShotBinaryTest → ℚ
twiceError t =
  (1ℚ - Photon.photon (plusResponse t)) +
  Photon.photon (minusResponse t)

-- Exact normalization of the two conditional probability kernels.
totalTwice :
  (t : OneShotBinaryTest) →
  twiceSuccess t + twiceError t ≡ 1ℚ + 1ℚ
totalTwice t =
  solve (Photon.photon (plusResponse t) ∷
         Photon.photon (minusResponse t) ∷ [])

-- Signed contrast is the excess of twiceSuccess over one.
-- Positive contrast favours photon->plus; reversed contrast demands
-- reversed decisions. No positivity or ordering asserted in this lemma.
signedContrast : OneShotBinaryTest → ℚ
signedContrast t =
  Photon.photon (plusResponse t) -
  Photon.photon (minusResponse t)

successContrastIdentity :
  (t : OneShotBinaryTest) →
  twiceSuccess t ≡ 1ℚ + signedContrast t
successContrastIdentity t =
  solve (Photon.photon (plusResponse t) ∷
         Photon.photon (minusResponse t) ∷ [])

errorContrastIdentity :
  (t : OneShotBinaryTest) →
  twiceError t ≡ 1ℚ - signedContrast t
errorContrastIdentity t =
  solve (Photon.photon (plusResponse t) ∷
         Photon.photon (minusResponse t) ∷ [])

-- The empirical test direction and hypothesis are distinct:
-- a statistical reject/fail-to-reject decision does not certify
-- a particular prepared state, as in the pre-existing statistics core.
-- For n i.i.d. repetitions, source-proved product kernels and
-- calibration of independence must be supplied before binomial tails.
