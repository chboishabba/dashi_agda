module DASHI.Cognition.PsychedelicNetworkDiffusion where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _-_)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.CognitiveResearchSources as Sources

------------------------------------------------------------------------
-- Empirical and modelling contact.
--
-- Functional connectivity is statistical dependence; effective connectivity
-- is directed model-based influence; structural connectivity is anatomy.  This
-- distinction follows Karl J. Friston (2011), DOI 10.1089/brain.2011.0008.
--
-- Psychedelic network sources represented here:
--   Carhart-Harris et al. (2016), DOI 10.1073/pnas.1518377113.
--   Luppi et al. (2021), DOI 10.1016/j.neuroimage.2020.117653.
--   Singleton et al. (2022), DOI 10.1038/s41467-022-33578-1.
--   Girn et al. (2026), DOI 10.1038/s41591-026-04287-9.
--
-- The 2026 mega-analysis supports stronger communication between transmodal
-- and unimodal systems across multiple classic psychedelics.  It does not say
-- that every edge becomes stronger or that fMRI functional connectivity is a
-- literal molecular diffusion coefficient.
------------------------------------------------------------------------

networkSources : List Sources.ResearchSource
networkSources =
  Sources.fristonConnectivityReview ∷
  Sources.carhartHarrisLSDNeuroimaging ∷
  Sources.luppiLSDIntegrationSegregation ∷
  Sources.singletonControlLandscape ∷
  Sources.girnMegaAnalysis ∷ []

------------------------------------------------------------------------
-- The brain does not use one wire protocol.  The formal carrier distinguishes
-- fast point-to-point and broader field/modulatory channels.
--
-- Volume-transmission references:
--   Fuxe et al. (2010), DOI 10.1016/j.pneurobio.2009.10.012.
--   Borroto-Escuela et al. (2015), DOI 10.1098/rstb.2014.0183.
-- Coherence-gated communication:
--   Pascal Fries (2005), DOI 10.1016/j.tics.2005.08.011.
------------------------------------------------------------------------

data SignalChannel : Set where
  axonalSpike : SignalChannel
  chemicalSynapse : SignalChannel
  electricalGapJunction : SignalChannel
  extracellularVolumeTransmission : SignalChannel
  oscillatoryCoherenceGate : SignalChannel
  haemodynamicObservation : SignalChannel

data ConnectivityLayer : Set where
  structuralAdjacency : ConnectivityLayer
  functionalDependence : ConnectivityLayer
  effectiveDirectedInfluence : ConnectivityLayer
  localJacobianLinearisation : ConnectivityLayer
  phaseSynchrony : ConnectivityLayer
  chemicalDiffusionKernel : ConnectivityLayer

functionalIsNotStructural : ConnectivityLayer
functionalIsNotStructural = functionalDependence

effectiveCanUseJacobian : ConnectivityLayer
effectiveCanUseJacobian = localJacobianLinearisation

------------------------------------------------------------------------
-- Exact two-system fixture.
--
-- The profile represents two within-system strengths and one symmetric
-- between-system strength.  It is intentionally small enough for literal
-- proofs while exposing the relevant directions of change.
------------------------------------------------------------------------

record TwoSystemProfile : Set where
  constructor twoSystemProfile
  field
    withinTransmodal : Nat
    withinSensory    : Nat
    crossSystem      : Nat

open TwoSystemProfile public

withinIntegrity : TwoSystemProfile → Nat
withinIntegrity profile =
  withinTransmodal profile + withinSensory profile

crossCommunication : TwoSystemProfile → Nat
crossCommunication profile = 2 * crossSystem profile

segregationMargin : TwoSystemProfile → Nat
segregationMargin profile =
  withinIntegrity profile - crossCommunication profile

baselineProfile : TwoSystemProfile
baselineProfile = twoSystemProfile 9 9 1

psychedelicProfile : TwoSystemProfile
psychedelicProfile = twoSystemProfile 6 6 4

baselineIntegrityIsEighteen : withinIntegrity baselineProfile ≡ 18
baselineIntegrityIsEighteen = refl

psychedelicIntegrityIsTwelve : withinIntegrity psychedelicProfile ≡ 12
psychedelicIntegrityIsTwelve = refl

baselineCrossCommunicationIsTwo :
  crossCommunication baselineProfile ≡ 2
baselineCrossCommunicationIsTwo = refl

psychedelicCrossCommunicationIsEight :
  crossCommunication psychedelicProfile ≡ 8
psychedelicCrossCommunicationIsEight = refl

baselineSegregationIsSixteen : segregationMargin baselineProfile ≡ 16
baselineSegregationIsSixteen = refl

psychedelicSegregationIsFour : segregationMargin psychedelicProfile ≡ 4
psychedelicSegregationIsFour = refl

------------------------------------------------------------------------
-- Difference and profile-angle diagnostics.
--
-- A Jacobian belongs to a dynamical model x' = F(x), not to integrity itself.
-- Integrity can be summarized from a connectivity matrix; deviation from a
-- baseline can use an L1/Frobenius-style norm; cosine similarity compares the
-- direction of flattened connectivity profiles.
------------------------------------------------------------------------

absDiff : Nat → Nat → Nat
absDiff m n = (m - n) + (n - m)

profileDeviationL1 : TwoSystemProfile → TwoSystemProfile → Nat
profileDeviationL1 first second =
  absDiff (withinTransmodal first) (withinTransmodal second) +
  absDiff (withinSensory first) (withinSensory second) +
  2 * absDiff (crossSystem first) (crossSystem second)

psychedelicDeviationFromBaselineIsTwelve :
  profileDeviationL1 baselineProfile psychedelicProfile ≡ 12
psychedelicDeviationFromBaselineIsTwelve = refl

profileDot : TwoSystemProfile → TwoSystemProfile → Nat
profileDot first second =
  withinTransmodal first * withinTransmodal second +
  withinSensory first * withinSensory second +
  2 * crossSystem first * crossSystem second

profileNormSquared : TwoSystemProfile → Nat
profileNormSquared profile = profileDot profile profile

record CosineData : Set where
  constructor cosineData
  field
    numerator        : Nat
    firstNormSquared : Nat
    secondNormSquared : Nat

cosineReceipt : TwoSystemProfile → TwoSystemProfile → CosineData
cosineReceipt first second = cosineData
  (profileDot first second)
  (profileNormSquared first)
  (profileNormSquared second)

record LocalJacobian2 : Set where
  constructor localJacobian2
  field
    selfTransmodalDerivative : Nat
    sensoryToTransmodalDerivative : Nat
    transmodalToSensoryDerivative : Nat
    selfSensoryDerivative : Nat

baselineJacobian : LocalJacobian2
baselineJacobian = localJacobian2 9 1 1 9

psychedelicJacobian : LocalJacobian2
psychedelicJacobian = localJacobian2 6 4 4 6

------------------------------------------------------------------------
-- Network diffusion step.  This is graph/effective transport, not a claim that
-- BOLD signals themselves diffuse chemically across cortex.
------------------------------------------------------------------------

record Activity2 : Set where
  constructor activity2
  field
    transmodalActivity : Nat
    sensoryActivity    : Nat

open Activity2 public

diffusionStep : TwoSystemProfile → Activity2 → Activity2
diffusionStep profile activity = activity2
  (withinTransmodal profile * transmodalActivity activity +
   crossSystem profile * sensoryActivity activity)
  (crossSystem profile * transmodalActivity activity +
   withinSensory profile * sensoryActivity activity)

sensorySeed : Activity2
sensorySeed = activity2 0 1

baselineSensoryTransport :
  diffusionStep baselineProfile sensorySeed ≡ activity2 1 9
baselineSensoryTransport = refl

psychedelicSensoryTransport :
  diffusionStep psychedelicProfile sensorySeed ≡ activity2 4 6
psychedelicSensoryTransport = refl

------------------------------------------------------------------------
-- Ternary commitment residence.
--
-- The measurable conjecture is not "psychedelics abolish excluded middle".
-- It is that weakened/highly variable precision increases residence near the
-- projective decision band before a positive or negative commitment.
------------------------------------------------------------------------

countProjective : List BT.Trit → Nat
countProjective [] = 0
countProjective (BT.zero ∷ rest) = suc (countProjective rest)
countProjective (_ ∷ rest) = countProjective rest

ordinaryCommitmentTrajectory : List BT.Trit
ordinaryCommitmentTrajectory = BT.pos ∷ BT.zero ∷ BT.neg ∷ []

psychedelicCommitmentTrajectory : List BT.Trit
psychedelicCommitmentTrajectory =
  BT.zero ∷ BT.zero ∷ BT.zero ∷ BT.pos ∷ []

ordinaryZeroResidenceIsOne :
  countProjective ordinaryCommitmentTrajectory ≡ 1
ordinaryZeroResidenceIsOne = refl

psychedelicZeroResidenceIsThree :
  countProjective psychedelicCommitmentTrajectory ≡ 3
psychedelicZeroResidenceIsThree = refl

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record DiffusionInterpretationBoundary : Set where
  constructor diffusionInterpretationBoundary
  field
    graphTransportModelled : Bool
    chemicalVolumeTransmissionTyped : Bool
    functionalConnectivityIsLiteralDiffusion : Bool
    psychedelicZeroResidenceMeasured : Bool

canonicalDiffusionBoundary : DiffusionInterpretationBoundary
canonicalDiffusionBoundary =
  diffusionInterpretationBoundary true true false false

functionalConnectivityNotPromotedToMolecularDiffusion :
  DiffusionInterpretationBoundary.functionalConnectivityIsLiteralDiffusion
    canonicalDiffusionBoundary ≡ false
functionalConnectivityNotPromotedToMolecularDiffusion = refl
