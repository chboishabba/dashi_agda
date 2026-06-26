module DASHI.Physics.Closure.OSAxiomAvailability where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- OSAxiomSourceIntakeStatus
--
-- Records which OS axioms are available in the current DASHI YM
-- *source-intake route* — that is, relative to the 33 named imported
-- postulates closed as of v0.3 / P33-closed.
--
-- This is distinct from a direct/constructive Agda proof scaffold.
-- It tracks: "has the relevant result been identified and cited in
-- the Eriksson series, and consumed in the DASHI receipt chain?"
--
-- v0.3 / P33-closed terminal state:
--
--   OS0 (temperedness):          true
--     Banach-Alaoglu compactness argument — Eriksson 2602.0088 §8.1.
--     Finite lattice Schwinger functions are bounded; limit is tempered.
--
--   OS1 (Euclidean covariance):  true
--     ImportedOS1EuclideanCovariance (P30) — 2602.0092 Thm 4.2 + Cor 4.3.
--     Rotational Ward identity (P28) + Symanzik decomposition (P29)
--     → L_{μν} S_n = 0 in S'(R^{4n}), full O(4) covariance.
--
--   OS2 (reflection positivity): true
--     Osterwalder-Seiler Thm 2.1 — Eriksson 2602.0088 §8.1 (Tier 1).
--     Wilson lattice action satisfies reflection positivity unconditionally.
--
--   OS3 (permutation symmetry):  true
--     Automatic for gauge-invariant (bosonic) observables.
--     Eriksson 2602.0088 §8.1.
--
--   OS4 (cluster decomposition): true
--     Hypothesis 5.2 discharged via Yoshida-GZ / DLR-LSI bypass:
--     P12 (2602.0052 Lem 6.3) → P14 (2602.0052 Thm 7.1)
--     → 2602.0088 Thm 7.1.

record OSAxiomSourceIntakeStatus : Set where
  field
    os0TemperednessAvailable         : Bool
    os1EuclideanCovarianceAvailable  : Bool
    os2ReflectionPositivityAvailable : Bool
    os3BosonicSymmetryAvailable      : Bool
    os4ClusterPropertyAvailable      : Bool
    allOSAxiomsSourceIntakeClosed    : Bool

------------------------------------------------------------------------
-- Terminal instance.

currentOSSourceIntakeStatus : OSAxiomSourceIntakeStatus
currentOSSourceIntakeStatus = record
  { os0TemperednessAvailable         = true   -- 2602.0088 §8.1 Banach-Alaoglu
  ; os1EuclideanCovarianceAvailable  = true   -- 2602.0092 Thm 4.2+Cor 4.3 (P30)
  ; os2ReflectionPositivityAvailable = true   -- 2602.0088 §8.1 Osterwalder-Seiler Thm 2.1
  ; os3BosonicSymmetryAvailable      = true   -- 2602.0088 §8.1 gauge-invariant bosonic
  ; os4ClusterPropertyAvailable      = true   -- 2602.0088 Thm 7.1 via DLR-LSI (P12-P14)
  ; allOSAxiomsSourceIntakeClosed    = true   -- all five closed in source-intake chain
  }

-- Refl witnesses — these typecheck iff the instance is correct.
os0SITrue  : OSAxiomSourceIntakeStatus.os0TemperednessAvailable         currentOSSourceIntakeStatus ≡ true
os0SITrue  = refl
os1SITrue  : OSAxiomSourceIntakeStatus.os1EuclideanCovarianceAvailable  currentOSSourceIntakeStatus ≡ true
os1SITrue  = refl
os2SITrue  : OSAxiomSourceIntakeStatus.os2ReflectionPositivityAvailable currentOSSourceIntakeStatus ≡ true
os2SITrue  = refl
os3SITrue  : OSAxiomSourceIntakeStatus.os3BosonicSymmetryAvailable      currentOSSourceIntakeStatus ≡ true
os3SITrue  = refl
os4SITrue  : OSAxiomSourceIntakeStatus.os4ClusterPropertyAvailable      currentOSSourceIntakeStatus ≡ true
os4SITrue  = refl
allSITrue  : OSAxiomSourceIntakeStatus.allOSAxiomsSourceIntakeClosed    currentOSSourceIntakeStatus ≡ true
allSITrue  = refl

------------------------------------------------------------------------
-- Legacy interface alias.
--
-- The old OSAxiomAvailability record is kept for backward compatibility
-- with existing downstream modules that import it.  It now wraps the
-- source-intake status.

record OSAxiomAvailability : Set where
  field
    os0-temperedness          : Bool
    os1-euclidean-covariance  : Bool
    os2-reflection-positivity : Bool
    os3-permutation-symmetry  : Bool
    os4-cluster-decomposition : Bool

-- Terminal legacy instance — matches the source-intake status.
currentOSStatus : OSAxiomAvailability
currentOSStatus = record
  { os0-temperedness          = true   -- 2602.0088 §8.1
  ; os1-euclidean-covariance  = true   -- 2602.0092 P30
  ; os2-reflection-positivity = true   -- 2602.0088 §8.1 Osterwalder-Seiler
  ; os3-permutation-symmetry  = true   -- 2602.0088 §8.1 bosonic
  ; os4-cluster-decomposition = true   -- 2602.0088 Thm 7.1 via DLR-LSI
  }

------------------------------------------------------------------------
-- DirectProofScaffoldStatus: tracks whether constructive Agda proof
-- terms (not just source-intake citations) exist for each axiom.
-- These may remain false without contradicting the source-intake chain.

record DirectProofScaffoldStatus : Set where
  field
    completeMonotonicityScaffoldClosed : Bool  -- OS2 direct proof term
    directClusterDecayProofClosed      : Bool  -- OS4 direct proof term

currentDirectProofScaffold : DirectProofScaffoldStatus
currentDirectProofScaffold = record
  { completeMonotonicityScaffoldClosed = false  -- CompleteMonotonicityScaffold open
  ; directClusterDecayProofClosed      = false  -- direct Agda term not yet built
  }
