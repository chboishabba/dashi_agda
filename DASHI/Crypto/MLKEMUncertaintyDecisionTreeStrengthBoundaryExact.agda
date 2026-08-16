module DASHI.Crypto.MLKEMUncertaintyDecisionTreeStrengthBoundaryExact where

------------------------------------------------------------------------
-- ML-KEM: DECISION-TREE STRENGTH BOUNDARY OF THE 128 UNCERTAINTY ROUTE
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- PURPOSE
--
-- The path-level residual-touch theorem is a genuine computational resource
-- lower bound for exact materialised residual maintenance.  This file records
-- why that fact alone is still far from a cryptographic hardness theorem.
--
-- A binary decision procedure of depth d can distinguish up to 2^d leaves,
-- while the uncertainty-derived path demand contributes only 128 per primitive
-- transition.  Increasing depth by one therefore
--
--   * doubles the ideal binary leaf capacity, but
--   * adds only 128 units to the division-free path demand.
--
-- Thus support uncertainty + unconstrained binary decision coverage naturally
-- yields a lower bound linear in decision depth (hence potentially logarithmic
-- in candidate count), not an exponential recovery lower bound.
--
-- This is not a weakness in the uncertainty theorem; it identifies the next
-- missing cryptographic ingredient: a bound on how much protected-label
-- information / fibre mass one admissible verifier observation or transition
-- can eliminate, including compressed/sufficient-state representations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (Nat; zero; suc; _+_; _*_)

------------------------------------------------------------------------
-- Ideal binary decision capacity.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc depth) = 2 * pow2 depth

binaryLeafCapacity : Nat → Nat → Nat
binaryLeafCapacity depth maxCandidatesPerLeaf =
  pow2 depth * maxCandidatesPerLeaf

------------------------------------------------------------------------
-- Uncertainty path demand: one sharp 128-area obligation per transition.
------------------------------------------------------------------------

uncertaintyPathDemand : Nat → Nat
uncertaintyPathDemand zero = 0
uncertaintyPathDemand (suc depth) = 128 + uncertaintyPathDemand depth

oneMoreDecisionBitDoublesLeafCapacity :
  (depth maxCandidatesPerLeaf : Nat) →
  binaryLeafCapacity (suc depth) maxCandidatesPerLeaf ≡
  2 * binaryLeafCapacity depth maxCandidatesPerLeaf
oneMoreDecisionBitDoublesLeafCapacity depth maxCandidatesPerLeaf = refl

oneMorePrimitiveAddsOnly128Demand :
  (depth : Nat) →
  uncertaintyPathDemand (suc depth) ≡
  128 + uncertaintyPathDemand depth
oneMorePrimitiveAddsOnly128Demand depth = refl

------------------------------------------------------------------------
-- Concrete scaling regression.
------------------------------------------------------------------------

depth10LeafCapacity : binaryLeafCapacity 10 1 ≡ 1024
depth10LeafCapacity = refl

depth10UncertaintyDemand : uncertaintyPathDemand 10 ≡ 1280
depth10UncertaintyDemand = refl

depth20LeafCapacity : binaryLeafCapacity 20 1 ≡ 1048576
depth20LeafCapacity = refl

depth20UncertaintyDemand : uncertaintyPathDemand 20 ≡ 2560
depth20UncertaintyDemand = refl

------------------------------------------------------------------------
-- Coverage surface.
--
-- A concrete recovery analysis must prove candidate coverage for its admitted
-- observation language.  The record keeps that theorem separate from the
-- uncertainty resource theorem.
------------------------------------------------------------------------

record BinaryDecisionCoverage : Set where
  constructor binary-decision-coverage
  field
    candidateCount : Nat
    decisionDepth : Nat
    maxCandidatesPerLeaf : Nat
    coverage :
      candidateCount ≤
      binaryLeafCapacity decisionDepth maxCandidatesPerLeaf

open BinaryDecisionCoverage public

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- Nothing here claims that real ML-KEM recovery is a binary tree, nor that a
-- leaf contains one candidate.  The point is the opposite: even under the
-- optimistic one-candidate-per-leaf abstraction, exponential leaf capacity is
-- compatible with only linear path depth.  Therefore the 128 uncertainty law
-- cannot by itself establish exponential ML-KEM hardness.
--
-- Highest-alpha remaining producer:
--   constrain the information/partition refinement obtainable per admissible
--   exact verifier transition/observation, especially for compressed sufficient
--   states.  That theorem must connect the protected-label fibre to update and
--   readout semantics; merely counting changed Fourier residues is insufficient.
------------------------------------------------------------------------
