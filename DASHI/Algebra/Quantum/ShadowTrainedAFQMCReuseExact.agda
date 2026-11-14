module DASHI.Algebra.Quantum.ShadowTrainedAFQMCReuseExact where

open import DASHI.Core.Prelude
import DASHI.Algebra.Quantum.DASHIStructuredStateCompression as Compression

------------------------------------------------------------------------
-- IonQ shadow-trained neural trial states: finite reuse and error cut.
--
-- External attribution: J. Provazza, O. Knitter et al.,
-- "Shadow-trained neural quantum states", arXiv:2611.08129 (2026).
-- Independent source background: arXiv:2506.22408 and 2610.03103.
--
-- This module transports existing DASHI compression proofs onto a
-- finite shadow/AFQMC walker interface. It does NOT assert that generic
-- Metropolis sampling implements phaseless auxiliary-field QMC, or that
-- Shor's Born ratios form an experimental chemistry shadow dataset.
------------------------------------------------------------------------

record ShadowTrialInterface (M : Compression.CompressionModel) : Set₁ where
  field
    ShadowDatum : Set
    Walker : Set
    Measurements : Set
    learnedDescription : Measurements → Compression.Description M
    idealState : Measurements → Compression.QuantumState M

    -- A measurement datum and an electronic walker are distinct types.
    measuredDatum : Measurements → ShadowDatum
    idealOverlap : Walker → Compression.QuantumState M → Nat
    surrogateOverlap : Walker → Compression.Description M → Nat
    overlapDiscrepancy : Nat → Nat → Nat
    overlapBudget : Nat

    -- The empirical fitting and noise-correction obligation.
    fitCertificate :
      (d : Measurements) (w : Walker) →
      overlapDiscrepancy
        (idealOverlap w (idealState d))
        (surrogateOverlap w (learnedDescription d))
      ≤ overlapBudget

open ShadowTrialInterface public

-- A second, independently sourced assumption is indispensable:
-- accurate trial overlaps alone do not guarantee a stable phaseless
-- AFQMC energy estimator.
record EnergyTransport
    {M : Compression.CompressionModel}
    (S : ShadowTrialInterface M) : Set₁ where
  field
    idealLocalEnergy : Measurements S → Walker S → Nat
    learnedLocalEnergy : Measurements S → Walker S → Nat
    energyDiscrepancy : Nat → Nat → Nat
    energyBudget : Nat
    stabilityCertificate :
      (d : Measurements S) (w : Walker S) →
      energyDiscrepancy
        (idealLocalEnergy d w)
        (learnedLocalEnergy d w)
      ≤ energyBudget

open EnergyTransport public

-- Source-written finite propagation, rather than an unproved assertion
-- about the distribution of statistically sampled walkers.
record FiniteWalkerRun
    {M : Compression.CompressionModel}
    (S : ShadowTrialInterface M) : Set₁ where
  field
    initial : Walker S
    advance : Walker S → Walker S

open FiniteWalkerRun public

walk :
  ∀ {M : Compression.CompressionModel}
    {S : ShadowTrialInterface M} →
  FiniteWalkerRun S → Nat → Walker S
walk R zero = initial R
walk R (suc n) = advance R (walk R n)

-- The same trained surrogate is reused on every generated walker,
-- without processing the original measurements a second time.
overlapBoundOnRun :
  ∀ {M : Compression.CompressionModel}
    {S : ShadowTrialInterface M} →
  (R : FiniteWalkerRun S) →
  (d : Measurements S) →
  (n : Nat) →
  overlapDiscrepancy S
    (idealOverlap S (walk R n) (idealState S d))
    (surrogateOverlap S (walk R n) (learnedDescription S d))
  ≤ overlapBudget S
overlapBoundOnRun {S = S} R d n =
  fitCertificate S d (walk R n)

energyBoundOnRun :
  ∀ {M : Compression.CompressionModel}
    {S : ShadowTrialInterface M} →
  (E : EnergyTransport S) →
  (R : FiniteWalkerRun S) →
  (d : Measurements S) →
  (n : Nat) →
  energyDiscrepancy E
    (idealLocalEnergy E d (walk R n))
    (learnedLocalEnergy E d (walk R n))
  ≤ energyBudget E
energyBoundOnRun E R d n =
  stabilityCertificate E d (walk R n)

-- Quantitative claims are deliberately not promoted from the unrelated
-- Shor or protein Monte Carlo modules. Those upstream owners remain
-- independent; see the source audit in docs/shadow_trained_afqmc_reuse.md.
