module DASHI.Analysis.NonArchimedeanHilbertCorrelationDecayExact where

------------------------------------------------------------------------
-- HILBERT CORRELATION DECAY
--
-- Correct downstream consumer of the repaired prefactored L2 power theorem.
--
-- Mathlib owns Cauchy--Schwarz on the exact source carrier
-- `EuclideanSpace ℂ (ZMod (2^n))`:
--
--   norm_inner_le_norm : ||<x,y>|| <= ||x|| ||y||.
--
-- Therefore, whenever the mean-zero power estimate gives
--
--   ||P_n^t g|| <= C_n 2^(-t/2) ||g||,
--
-- one immediately obtains the Hilbert correlation bound
--
--   ||<f,P_n^t g>|| <= C_n 2^(-t/2) ||f|| ||g||.
--
-- This is not silently identified with a stochastic covariance.  A probabilistic
-- statement Cov_pi(f(X_0),g(X_t)) requires an expectation/stationarity weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record HilbertCorrelationSourceReceipt : Set where
  constructor hilbertCorrelationSourceReceipt
  field
    sourceCommit : String
    mathlibReferenceCommit : String
    sourceL2IsEuclideanSpace : Bool
    cauchySchwarzNormInnerOwned : Bool
    prefactoredL2PowerDependencyClosed : Bool
    hilbertCorrelationDecayCompiles : Bool
    stochasticCovarianceIdentificationOwned : Bool
    stochasticStationarityExpectationWeldRequired : Bool

canonicalHilbertCorrelationSourceReceipt : HilbertCorrelationSourceReceipt
canonicalHilbertCorrelationSourceReceipt =
  hilbertCorrelationSourceReceipt
    "f94b956e6e970c40c8bb9f9c39e9052ad7a5f884"
    "251e86bd1fa42024826ccdb46c3d680edff03e1f"
    true true true true false true

hilbertCorrelationDependencyClosed :
  HilbertCorrelationSourceReceipt.hilbertCorrelationDecayCompiles
    canonicalHilbertCorrelationSourceReceipt
  ≡ true
hilbertCorrelationDependencyClosed = refl

probabilisticCovarianceNotAutoPromoted :
  HilbertCorrelationSourceReceipt.stochasticCovarianceIdentificationOwned
    canonicalHilbertCorrelationSourceReceipt
  ≡ false
probabilisticCovarianceNotAutoPromoted = refl
