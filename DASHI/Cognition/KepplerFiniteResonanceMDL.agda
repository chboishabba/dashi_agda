module DASHI.Cognition.KepplerFiniteResonanceMDL where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

import DASHI.Cognition.KepplerGlutamateZPFMDLTest as Prior

------------------------------------------------------------------------
-- Literal finite spectra.  The resonance functional is not a free knob:
-- it is computed from frequency-labelled glutamate susceptibility samples
-- and frequency-labelled field-mode-density samples.
------------------------------------------------------------------------

record BandSample : Set where
  constructor bandSample
  field
    frequencyBin : Nat
    amplitude    : Nat

open BandSample public

eqNat : Nat → Nat → Bool
eqNat zero zero = true
eqNat zero (suc _) = false
eqNat (suc _) zero = false
eqNat (suc m) (suc n) = eqNat m n

sampleOverlap : BandSample → BandSample → Nat
sampleOverlap left right with eqNat (frequencyBin left) (frequencyBin right)
... | true = amplitude left * amplitude right
... | false = 0

overlapAgainst : BandSample → List BandSample → Nat
overlapAgainst sample [] = 0
overlapAgainst sample (mode ∷ modes) =
  sampleOverlap sample mode + overlapAgainst sample modes

resonanceScore : List BandSample → List BandSample → Nat
resonanceScore [] fieldSpectrum = 0
resonanceScore (susceptibility ∷ susceptibilities) fieldSpectrum =
  overlapAgainst susceptibility fieldSpectrum
  + resonanceScore susceptibilities fieldSpectrum

record FiniteKepplerCarrier : Set where
  constructor finiteKepplerCarrier
  field
    candidate : Prior.KepplerCouplingCandidate
    glutamateSpectrum : List BandSample
    fieldModeDensity  : List BandSample
    collectiveThreshold : Nat

open FiniteKepplerCarrier public

couplingDrive : FiniteKepplerCarrier → Nat
couplingDrive carrier =
  Prior.CorticalMicrocolumn.columnCount
    (Prior.KepplerCouplingCandidate.microcolumn (candidate carrier))
  * Prior.GlutamatePool.populationCount
    (Prior.KepplerCouplingCandidate.glutamate (candidate carrier))
  * resonanceScore (glutamateSpectrum carrier) (fieldModeDensity carrier)

atLeast : Nat → Nat → Bool
atLeast zero zero = true
atLeast zero (suc _) = false
atLeast (suc _) zero = true
atLeast (suc actual) (suc required) = atLeast actual required

data CollectivePhase : Set where
  incoherentPhase : CollectivePhase
  coherentDomainPhase : CollectivePhase

collectivePhase : FiniteKepplerCarrier → CollectivePhase
collectivePhase carrier with
  atLeast (couplingDrive carrier) (collectiveThreshold carrier)
... | true = coherentDomainPhase
... | false = incoherentPhase

------------------------------------------------------------------------
-- Canonical exact spectra.  The in-band score is 3 * 5 = 15; the off-band
-- score is zero because its frequency label does not match.
------------------------------------------------------------------------

canonicalMicrocolumn : Prior.CorticalMicrocolumn
canonicalMicrocolumn = Prior.corticalMicrocolumn 2 "two-column finite fixture"

canonicalGlutamatePool : Prior.GlutamatePool
canonicalGlutamatePool = Prior.glutamatePool 4 "resolved-bin-2"

canonicalMode : Prior.ZPFMode
canonicalMode = Prior.zpfMode 2 "bin-2"

canonicalResonanceWitness : Prior.ResonanceWitness
canonicalResonanceWitness =
  Prior.resonanceWitness true true true true

canonicalCandidate : Prior.KepplerCouplingCandidate
canonicalCandidate =
  Prior.kepplerCouplingCandidate
    canonicalMicrocolumn
    canonicalGlutamatePool
    canonicalMode
    canonicalResonanceWitness
    1

canonicalGlutamateSpectrum : List BandSample
canonicalGlutamateSpectrum = bandSample 2 3 ∷ []

canonicalInBandField : List BandSample
canonicalInBandField = bandSample 2 5 ∷ []

canonicalOffBandField : List BandSample
canonicalOffBandField = bandSample 3 5 ∷ []

inBandScoreIsFifteen :
  resonanceScore canonicalGlutamateSpectrum canonicalInBandField ≡ 15
inBandScoreIsFifteen = refl

offBandScoreIsZero :
  resonanceScore canonicalGlutamateSpectrum canonicalOffBandField ≡ 0
offBandScoreIsZero = refl

canonicalFiniteCarrier : FiniteKepplerCarrier
canonicalFiniteCarrier =
  finiteKepplerCarrier
    canonicalCandidate
    canonicalGlutamateSpectrum
    canonicalInBandField
    100

canonicalCouplingDriveIsOneHundredTwenty :
  couplingDrive canonicalFiniteCarrier ≡ 120
canonicalCouplingDriveIsOneHundredTwenty = refl

canonicalEnsembleCrossesThreshold :
  collectivePhase canonicalFiniteCarrier ≡ coherentDomainPhase
canonicalEnsembleCrossesThreshold = refl

------------------------------------------------------------------------
-- Exact predictive MDL comparison.
-- The extra term earns its keep only if the complete alternative code is
-- shorter on held-out data and the improvement is frequency selective.
------------------------------------------------------------------------

lessNat : Nat → Nat → Bool
lessNat zero zero = false
lessNat zero (suc _) = true
lessNat (suc _) zero = false
lessNat (suc m) (suc n) = lessNat m n

codeLess : Prior.PredictiveCode → Prior.PredictiveCode → Bool
codeLess left right =
  lessNat (Prior.totalCode left) (Prior.totalCode right)

record SpectralMDLComparison : Set where
  constructor spectralMDLComparison
  field
    nullHeldOutCode : Prior.PredictiveCode
    coupledHeldOutCode : Prior.PredictiveCode
    inBandScore : Nat
    offBandScore : Nat
    stableAcrossConditions : Bool

open SpectralMDLComparison public

frequencySelective : SpectralMDLComparison → Bool
frequencySelective comparison =
  lessNat (offBandScore comparison) (inBandScore comparison)

kepplerTermEarnsKeep : SpectralMDLComparison → Bool
kepplerTermEarnsKeep comparison with
  codeLess (coupledHeldOutCode comparison) (nullHeldOutCode comparison)
  | frequencySelective comparison
  | stableAcrossConditions comparison
... | true | true | true = true
... | _ | _ | _ = false

canonicalNullCode : Prior.PredictiveCode
canonicalNullCode = Prior.predictiveCode 10 20

canonicalCoupledCode : Prior.PredictiveCode
canonicalCoupledCode = Prior.predictiveCode 12 10

canonicalComparison : SpectralMDLComparison
canonicalComparison =
  spectralMDLComparison
    canonicalNullCode
    canonicalCoupledCode
    (resonanceScore canonicalGlutamateSpectrum canonicalInBandField)
    (resonanceScore canonicalGlutamateSpectrum canonicalOffBandField)
    true

canonicalCouplingEarnsKeepInFiniteFixture :
  kepplerTermEarnsKeep canonicalComparison ≡ true
canonicalCouplingEarnsKeepInFiniteFixture = refl

record NoImprovementComparison : Set where
  constructor noImprovementComparison
  field
    nullCode : Prior.PredictiveCode
    extraModelCost : Nat

alternativeWithoutResidualGain :
  NoImprovementComparison → Prior.PredictiveCode
alternativeWithoutResidualGain comparison =
  Prior.predictiveCode
    (Prior.PredictiveCode.modelCost (NoImprovementComparison.nullCode comparison)
      + NoImprovementComparison.extraModelCost comparison)
    (Prior.PredictiveCode.residualCost (NoImprovementComparison.nullCode comparison))

canonicalNoGainComparison : NoImprovementComparison
canonicalNoGainComparison = noImprovementComparison canonicalNullCode 2

zeroResidualGainDoesNotEarnKeep :
  codeLess
    (alternativeWithoutResidualGain canonicalNoGainComparison)
    canonicalNullCode
  ≡ false
zeroResidualGainDoesNotEarnKeep = refl

------------------------------------------------------------------------
-- Authority boundary: the finite calculation establishes what the proposed
-- model would predict.  It does not establish that the measured brain has
-- this spectrum or that such coupling causes consciousness.
------------------------------------------------------------------------

record FiniteResonanceAuthorityBoundary : Set where
  constructor finiteResonanceAuthorityBoundary
  field
    resonanceFunctionalComputed : Bool
    phaseThresholdComputed : Bool
    heldOutMDLRuleComputed : Bool
    physiologicalSpectrumMeasured : Bool
    vacuumCausalityEstablished : Bool
    consciousnessCausalityEstablished : Bool

canonicalAuthorityBoundary : FiniteResonanceAuthorityBoundary
canonicalAuthorityBoundary =
  finiteResonanceAuthorityBoundary true true true false false false

physiologicalMeasurementStillOpen :
  FiniteResonanceAuthorityBoundary.physiologicalSpectrumMeasured
    canonicalAuthorityBoundary ≡ false
physiologicalMeasurementStillOpen = refl

consciousnessCausalityStillOpen :
  FiniteResonanceAuthorityBoundary.consciousnessCausalityEstablished
    canonicalAuthorityBoundary ≡ false
consciousnessCausalityStillOpen = refl
