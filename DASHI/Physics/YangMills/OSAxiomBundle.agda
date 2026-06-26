module DASHI.Physics.YangMills.OSAxiomBundle where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives
open import DASHI.Physics.Closure.OSAxiomAvailability using
  ( OSAxiomAvailability
  ; OSAxiomSourceIntakeStatus
  ; DirectProofScaffoldStatus
  ; currentOSStatus
  ; currentOSSourceIntakeStatus
  ; currentDirectProofScaffold
  )

-- OSAxiomBundle: OS axiom assembly for the YM mass gap route.
--
-- v0.3 / P33-closed terminal state:
--   All five OS axioms are available in the source-intake chain.
--
--   OS0: Banach-Alaoglu temperedness     — 2602.0088 §8.1
--   OS1: O(4)/Euclidean covariance        — 2602.0092 P30 (Thm 4.2+Cor 4.3)
--   OS2: Osterwalder-Seiler refl. pos.   — 2602.0088 §8.1 (Tier 1, unconditional)
--   OS3: Bosonic/gauge-invariant symmetry — 2602.0088 §8.1
--   OS4: Cluster decomposition            — 2602.0088 Thm 7.1 via DLR-LSI (P12-P14)
--
--   allOSAxiomsSourceIntakeClosed = true
--   osComplete (source-intake level)     = true
--
-- Remaining open: direct constructive Agda proof terms for OS2/OS4
-- (CompleteMonotonicityScaffold, direct cluster decay term).
-- These are tracked separately in DirectProofScaffoldStatus.

record OSAxiomBundle : Set₁ where
  field
    -- Source-intake status: all five closed.
    sourceIntake : OSAxiomSourceIntakeStatus
    os0SIAvailable : OSAxiomSourceIntakeStatus.os0TemperednessAvailable         sourceIntake ≡ true
    os1SIAvailable : OSAxiomSourceIntakeStatus.os1EuclideanCovarianceAvailable  sourceIntake ≡ true
    os2SIAvailable : OSAxiomSourceIntakeStatus.os2ReflectionPositivityAvailable sourceIntake ≡ true
    os3SIAvailable : OSAxiomSourceIntakeStatus.os3BosonicSymmetryAvailable      sourceIntake ≡ true
    os4SIAvailable : OSAxiomSourceIntakeStatus.os4ClusterPropertyAvailable      sourceIntake ≡ true
    allSIClosedAvailable : OSAxiomSourceIntakeStatus.allOSAxiomsSourceIntakeClosed sourceIntake ≡ true

    -- Legacy availability record (backward-compat, also all true).
    availability : OSAxiomAvailability
    os0Available : OSAxiomAvailability.os0-temperedness          availability ≡ true
    os1Available : OSAxiomAvailability.os1-euclidean-covariance  availability ≡ true
    os2Available : OSAxiomAvailability.os2-reflection-positivity availability ≡ true
    os3Available : OSAxiomAvailability.os3-permutation-symmetry  availability ≡ true
    os4Available : OSAxiomAvailability.os4-cluster-decomposition availability ≡ true

    -- Source-intake complete.
    osComplete       : Bool
    osCompleteIsTrue : osComplete ≡ true

    -- Direct proof scaffold: constructive Agda terms still open.
    directScaffold : DirectProofScaffoldStatus
    cmScaffoldOpen : DirectProofScaffoldStatus.completeMonotonicityScaffoldClosed directScaffold ≡ false
    clusterProofOpen : DirectProofScaffoldStatus.directClusterDecayProofClosed    directScaffold ≡ false

    -- Fail-closed.
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalOSAxiomBundle : OSAxiomBundle
canonicalOSAxiomBundle = record
  { sourceIntake       = currentOSSourceIntakeStatus
  ; os0SIAvailable     = refl
  ; os1SIAvailable     = refl
  ; os2SIAvailable     = refl
  ; os3SIAvailable     = refl
  ; os4SIAvailable     = refl
  ; allSIClosedAvailable = refl
  ; availability       = currentOSStatus
  ; os0Available       = refl
  ; os1Available       = refl
  ; os2Available       = refl
  ; os3Available       = refl
  ; os4Available       = refl
  ; osComplete         = true
  ; osCompleteIsTrue   = refl
  ; directScaffold     = currentDirectProofScaffold
  ; cmScaffoldOpen     = refl
  ; clusterProofOpen   = refl
  ; noClayPromotion    = refl
  }
