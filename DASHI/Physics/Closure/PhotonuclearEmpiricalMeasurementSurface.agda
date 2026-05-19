module DASHI.Physics.Closure.PhotonuclearEmpiricalMeasurementSurface where

-- Empirical-side measurement surface for the photonuclear / LHC lane.
-- This module packages:
--   * measured observables
--   * per-sample and per-measurement payloads
--   * provenance hooks
--   * explicit claim-boundary bookkeeping
--
-- It is intentionally theorem-adjacent but not proof-bearing: the values are
-- treated as empirical payloads that downstream runners may instantiate.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Physics.Closure.PhysicsClosureEmpirical as PCE

------------------------------------------------------------------------
-- Measured observables

record PhotonuclearMeasuredObservables (V : Set) : Set₁ where
  field
    defectIntensity : V
    promotedObservable : V
    densityProxy : V
    saturationProxy : V

open PhotonuclearMeasuredObservables public

------------------------------------------------------------------------
-- Provenance hooks

record PhotonuclearProvenanceHook : Set₁ where
  field
    sourceLabel : String
    sourceKind : String
    sourceRef : String
    note : String

open PhotonuclearProvenanceHook public

provenanceCount : List PhotonuclearProvenanceHook → Nat
provenanceCount [] = zero
provenanceCount (_ ∷ xs) = suc (provenanceCount xs)

------------------------------------------------------------------------
-- Sample payloads

record PhotonuclearMeasurementSample (V : Set) : Set₁ where
  field
    sampleLabel : String
    photonEnergy : V
    observables : PhotonuclearMeasuredObservables V

open PhotonuclearMeasurementSample public

record PhotonuclearMeasurementRecord (V : Set) : Set₁ where
  field
    measurementLabel : String
    sample : PhotonuclearMeasurementSample V
    provenance : PhotonuclearProvenanceHook

open PhotonuclearMeasurementRecord public

sampleCount : ∀ {V : Set} → List (PhotonuclearMeasurementSample V) → Nat
sampleCount [] = zero
sampleCount (_ ∷ xs) = suc (sampleCount xs)

measurementCount : ∀ {V : Set} → List (PhotonuclearMeasurementRecord V) → Nat
measurementCount [] = zero
measurementCount (_ ∷ xs) = suc (measurementCount xs)

------------------------------------------------------------------------
-- Claim boundary ledger

record PhotonuclearClaimBoundary : Set₁ where
  field
    inScopeClaims : List String
    outOfScopeClaims : List String

open PhotonuclearClaimBoundary public

claimCount : List String → Nat
claimCount [] = zero
claimCount (_ ∷ xs) = suc (claimCount xs)

claimBoundaryCount : PhotonuclearClaimBoundary → Nat
claimBoundaryCount b =
  claimCount (inScopeClaims b) + claimCount (outOfScopeClaims b)

canonicalPhotonuclearClaimBoundary : PhotonuclearClaimBoundary
canonicalPhotonuclearClaimBoundary =
  record
    { inScopeClaims =
        "defect-channel measurement geometry"
        ∷ "sample packaging on the near-miss channel"
        ∷ "claim-boundary bookkeeping"
        ∷ []
    ; outOfScopeClaims =
        "equivalent-photon formalism"
        ∷ "QCD charm cross-sections"
        ∷ "saturation numerics"
        ∷ "CMS result reproduction"
        ∷ []
    }

------------------------------------------------------------------------
-- Empirical measurement surface

record PhotonuclearEmpiricalMeasurementSurface (V : Set) : Set₁ where
  field
    empiricalClosure : PCE.PhysicsClosureEmpirical
    measuredObservables : PhotonuclearMeasuredObservables V
    samples : List (PhotonuclearMeasurementSample V)
    measurements : List (PhotonuclearMeasurementRecord V)
    provenanceHooks : List PhotonuclearProvenanceHook
    claimBoundary : PhotonuclearClaimBoundary

open PhotonuclearEmpiricalMeasurementSurface public

surfaceSampleCount :
  ∀ {V : Set} →
  PhotonuclearEmpiricalMeasurementSurface V →
  Nat
surfaceSampleCount s = sampleCount (samples s)

surfaceMeasurementCount :
  ∀ {V : Set} →
  PhotonuclearEmpiricalMeasurementSurface V →
  Nat
surfaceMeasurementCount s = measurementCount (measurements s)

surfaceProvenanceCount :
  ∀ {V : Set} →
  PhotonuclearEmpiricalMeasurementSurface V →
  Nat
surfaceProvenanceCount s = provenanceCount (provenanceHooks s)

surfaceClaimCount :
  ∀ {V : Set} →
  PhotonuclearEmpiricalMeasurementSurface V →
  Nat
surfaceClaimCount s = claimBoundaryCount (claimBoundary s)

mkPhotonuclearEmpiricalMeasurementSurface :
  ∀ {V : Set} →
  PCE.PhysicsClosureEmpirical →
  PhotonuclearMeasuredObservables V →
  List (PhotonuclearMeasurementSample V) →
  List (PhotonuclearMeasurementRecord V) →
  List PhotonuclearProvenanceHook →
  PhotonuclearClaimBoundary →
  PhotonuclearEmpiricalMeasurementSurface V
mkPhotonuclearEmpiricalMeasurementSurface empiricalClosure measuredObservables samples measurements provenanceHooks claimBoundary =
  record
    { empiricalClosure = empiricalClosure
    ; measuredObservables = measuredObservables
    ; samples = samples
    ; measurements = measurements
    ; provenanceHooks = provenanceHooks
    ; claimBoundary = claimBoundary
    }
