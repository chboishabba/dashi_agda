{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Resist.BinomialMomentSkeletonExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Exact finite count/moment skeleton for later stochastic absorption models.
-- We avoid claiming a probability law before an absorption probability producer
-- exists.  The records merely encode finite trial count and event count.

record TrialCount : Set where
  constructor trialCount
  field
    trials : Nat
    absorbed : Nat
    missed : Nat
    accounting : absorbed + missed ≡ trials

open TrialCount public

sample100 : TrialCount
sample100 = trialCount 100 60 40 refl

-- Synthetic scaled mean witness: if p is represented as numerator/denominator,
-- the binomial expectation relation is E[K] * denominator = trials * numerator.
record MeanWitness (x : TrialCount) : Set where
  constructor meanWitness
  field
    pNumerator : Nat
    pDenominator : Nat
    expectedCount : Nat
    meanEquation : expectedCount * pDenominator ≡ trials x * pNumerator

open MeanWitness public

sampleMean : MeanWitness sample100
sampleMean = meanWitness 3 5 60 refl

-- A second moment/variance law is intentionally left as a residual because it
-- needs subtraction or an ordered ring to express n p (1-p) cleanly.
data StatisticalResidual : Set where
  AbsorptionProbabilityProducer : StatisticalResidual
  BinomialLawReceipt : StatisticalResidual
  PoissonLimitReceipt : StatisticalResidual
  VarianceProducer : StatisticalResidual
  SpatialCorrelationProducer : StatisticalResidual
  DoseNonuniformityProducer : StatisticalResidual

-- Firewall: a finite outcome and an expectation witness do not prove that the
-- physical process is binomial, independent, homogeneous, or Poisson.
