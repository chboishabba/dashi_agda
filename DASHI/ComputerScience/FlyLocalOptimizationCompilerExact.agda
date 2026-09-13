module DASHI.ComputerScience.FlyLocalOptimizationCompilerExact where

-- Fly instantiations of the generic least-privilege optimization compiler.
--
-- Runtime counterpart:
--   dashiBRAIN/dashi/analysis/local_optimization_compiler.py
--   dashiBRAIN/dashi/analysis/fly_streaming_optimization_certificates.py
--
-- Scientific carriers remain distinct from optimization tactics. This module
-- does not claim that NumPy/Arrow are proofs, nor that an empirical RSS number
-- proves a semantic theorem.

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.ComputerScience.LocalOptimizationCompilerExact as Opt

private
  variable
    ℓs ℓo ℓx ℓq ℓr : Level

------------------------------------------------------------------------
-- JRC2018 painted-domain stream.
------------------------------------------------------------------------

jrcPaintedDomainCount : Nat
jrcPaintedDomainCount = 46

record JRC2018PaintedDomainStreamingPayment
  {ℓr : Level}
  (SpecState : Set ℓs)
  (OptState : Set ℓo)
  (Domain : Set ℓx)
  (ConsumerObservation : Set ℓq)
  : Set (ℓs ⊔ ℓo ⊔ ℓx ⊔ ℓq ⊔ ℓr) where
  field
    semanticCompiler :
      Opt.LocalSemanticCompiler {ℓr = ℓr}
        SpecState OptState Domain ConsumerObservation
    initialSpec : SpecState
    initialOpt  : OptState
    initialRelated :
      Opt.Related semanticCompiler initialSpec initialOpt

open JRC2018PaintedDomainStreamingPayment public

jrcWholeCompilationPreserved :
  ∀ {ℓs ℓo ℓx ℓq ℓr}
    {SpecState : Set ℓs} {OptState : Set ℓo}
    {Domain : Set ℓx} {ConsumerObservation : Set ℓq}
    (P : JRC2018PaintedDomainStreamingPayment
      {ℓr = ℓr} SpecState OptState Domain ConsumerObservation) →
    (domains : List Domain) →
    Opt.observeSpec (semanticCompiler P)
      (Opt.fold (Opt.specStep (semanticCompiler P)) (initialSpec P) domains)
      ≡
    Opt.observeOpt (semanticCompiler P)
      (Opt.fold (Opt.optStep (semanticCompiler P)) (initialOpt P) domains)
jrcWholeCompilationPreserved P domains =
  Opt.wholeFoldObservationPreserved
    (semanticCompiler P)
    (initialRelated P)
    domains

jrcStreamingResidency :
  (selectedLabelBytes oneDomainBytes scoreStateBytes scratchBytes overheadBytes : Nat) →
  Opt.StreamingResidencyCertificate
jrcStreamingResidency selectedLabelBytes oneDomainBytes scoreStateBytes scratchBytes overheadBytes =
  Opt.streaming-residency
    (Opt.streaming-work jrcPaintedDomainCount 1)
    (Opt.residency-bound
      (selectedLabelBytes + scoreStateBytes)
      oneDomainBytes
      scratchBytes
      overheadBytes)
    refl

------------------------------------------------------------------------
-- MaleCNS synapse-partner stream.
------------------------------------------------------------------------

maleCNSCurrentFunctionalRegionCount : Nat
maleCNSCurrentFunctionalRegionCount = 13

maleCNSGraphNeuronCount : Nat
maleCNSGraphNeuronCount = 164740

-- The persistent counter carrier used by the bounded runtime producer:
-- region×neuron counters plus one total-incidence counter per neuron.
maleCNSPersistentCounterCells : Nat
maleCNSPersistentCounterCells =
  maleCNSCurrentFunctionalRegionCount * maleCNSGraphNeuronCount
  + maleCNSGraphNeuronCount

record MaleCNSSynapseMembershipStreamingPayment
  {ℓr : Level}
  (SpecState : Set ℓs)
  (OptState : Set ℓo)
  (PartnerRow : Set ℓx)
  (ConsumerObservation : Set ℓq)
  : Set (ℓs ⊔ ℓo ⊔ ℓx ⊔ ℓq ⊔ ℓr) where
  field
    semanticCompiler :
      Opt.LocalSemanticCompiler {ℓr = ℓr}
        SpecState OptState PartnerRow ConsumerObservation
    initialSpec : SpecState
    initialOpt  : OptState
    initialRelated :
      Opt.Related semanticCompiler initialSpec initialOpt

open MaleCNSSynapseMembershipStreamingPayment public

maleCNSWholeMembershipObservationPreserved :
  ∀ {ℓs ℓo ℓx ℓq ℓr}
    {SpecState : Set ℓs} {OptState : Set ℓo}
    {PartnerRow : Set ℓx} {ConsumerObservation : Set ℓq}
    (P : MaleCNSSynapseMembershipStreamingPayment
      {ℓr = ℓr} SpecState OptState PartnerRow ConsumerObservation) →
    (rows : List PartnerRow) →
    Opt.observeSpec (semanticCompiler P)
      (Opt.fold (Opt.specStep (semanticCompiler P)) (initialSpec P) rows)
      ≡
    Opt.observeOpt (semanticCompiler P)
      (Opt.fold (Opt.optStep (semanticCompiler P)) (initialOpt P) rows)
maleCNSWholeMembershipObservationPreserved P rows =
  Opt.wholeFoldObservationPreserved
    (semanticCompiler P)
    (initialRelated P)
    rows

maleCNSStreamingResidency :
  (partnerRowCount counterBytes oneBatchBytes scratchBytes overheadBytes : Nat) →
  Opt.StreamingResidencyCertificate
maleCNSStreamingResidency partnerRowCount counterBytes oneBatchBytes scratchBytes overheadBytes =
  Opt.streaming-residency
    (Opt.streaming-work partnerRowCount 1)
    (Opt.residency-bound
      (maleCNSPersistentCounterCells * counterBytes)
      oneBatchBytes
      scratchBytes
      overheadBytes)
    refl

------------------------------------------------------------------------
-- Empirical calibration is data, not theorem content.
------------------------------------------------------------------------

record FlyOptimizationExecutionCalibration : Set where
  constructor fly-calibration
  field
    oldCompilationOOMObserved : Bool
    oldPeakRSSMiBObserved : Nat
    streamedCompletedObserved : Bool
    streamedPeakRSSMiBObserved : Nat
    regressionSuiteGreenObserved : Bool
    regressionTestCountObserved : Nat

-- Observed on the JRC2018 painted-domain compiler run supplied by the runtime
-- executor. These values calibrate the resource model only; none appears in
-- jrcWholeCompilationPreserved or maleCNSWholeMembershipObservationPreserved.
currentJRCExecutionCalibration : FlyOptimizationExecutionCalibration
currentJRCExecutionCalibration =
  fly-calibration true 11277 true 2334 true 135

------------------------------------------------------------------------
-- Explicit non-collapse of error coordinates.
------------------------------------------------------------------------

record FlyOptimizationBoundary : Set where
  constructor fly-optimization-boundary
  field
    semanticCorrectnessSeparateFromResidency : Bool
    residencyBoundSeparateFromExecutionRSS : Bool
    resourceExhaustionNotSemanticPayment : Bool
    implementationTacticNotPrimitivePayment : Bool

canonicalFlyOptimizationBoundary : FlyOptimizationBoundary
canonicalFlyOptimizationBoundary =
  fly-optimization-boundary true true true true
