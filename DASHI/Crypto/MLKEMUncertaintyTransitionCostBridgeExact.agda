module DASHI.Crypto.MLKEMUncertaintyTransitionCostBridgeExact where

------------------------------------------------------------------------
-- ML-KEM: UNCERTAINTY -> TRANSITION/VERIFIER COST BRIDGE
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Finite-field uncertainty source:
-- Martino Borello; Patrick Sole,
-- "The uncertainty principle over finite fields",
-- Discrete Mathematics 345 (2022), 112670.
-- DOI: 10.1016/j.disc.2021.112670.
--
-- Defensive incomplete/noisy-NTT-information context (not a proof input):
-- Zehua Qiao, Yuejun Liu, Yongbin Zhou, Mingyao Shao, Shuo Sun,
-- "When NTT Meets SIS: Efficient Side-channel Attacks on Dilithium and Kyber",
-- IACR ePrint 2023/1866.  The ePrint record has no assigned DOI.
--
-- This citation motivates keeping surviving-support, observation quality and
-- downstream recovery work as separate coordinates.  Its attack construction
-- is not imported into this theorem.
--
-- PURPOSE
--
-- The harmonic theorem alone is not a recovery-cost lower bound.  This module
-- records the exact extra premise required to turn it into one at the level of
-- a single search transition.
--
-- For a nonzero candidate move write
--
--   s     = changed coefficient-position support,
--   o     = surviving public-output residue support,
--   sigma = singular-residue cancellation budget,
--   w     = verifier/update work charged by the search architecture.
--
-- The already-developed singular-budget geometry gives
--
--     128 <= s * (o + sigma).
--
-- If the concrete verifier implementation/search architecture must perform at
-- least one unit of work for every surviving output residue,
--
--     o <= w,
--
-- then monotonicity yields the robust per-step obstruction
--
--     128 <= s * (w + sigma).
--
-- In the full-rank case sigma=0 this becomes
--
--     128 <= s * w.
--
-- This is the precise "no simultaneous locality" bridge: a transition cannot
-- be both coefficient-local and verifier-local unless it spends singularity
-- budget.  It does NOT by itself prove a total recovery-time lower bound;
-- candidate count, path length, reconciliation, memory, and observation cost
-- remain separate coordinates of ProtectedLabelSearchGeometry.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _+_; _*_)
import Data.Nat.Properties as NatP

------------------------------------------------------------------------
-- One-step bridge from surviving-support geometry to implementation work.
------------------------------------------------------------------------

uncertaintyToTransitionWork :
  (changedSupport survivingSupport singularBudget verifierWork : Nat) →
  128 ≤ changedSupport * (survivingSupport + singularBudget) →
  survivingSupport ≤ verifierWork →
  128 ≤ changedSupport * (verifierWork + singularBudget)
uncertaintyToTransitionWork
  changedSupport survivingSupport singularBudget verifierWork
  uncertaintyBudget verifierCoversSurvivors =
  NatP.≤-trans
    uncertaintyBudget
    (NatP.*-monoʳ-≤ changedSupport
      (NatP.+-mono-≤ verifierCoversSurvivors NatP.≤-refl))

------------------------------------------------------------------------
-- Full-rank specialization: no singular-residue budget is available.
------------------------------------------------------------------------

fullRankUncertaintyToTransitionWork :
  (changedSupport survivingSupport verifierWork : Nat) →
  128 ≤ changedSupport * survivingSupport →
  survivingSupport ≤ verifierWork →
  128 ≤ changedSupport * verifierWork
fullRankUncertaintyToTransitionWork
  changedSupport survivingSupport verifierWork
  uncertainty verifierCoversSurvivors =
  NatP.≤-trans
    uncertainty
    (NatP.*-monoʳ-≤ changedSupport verifierCoversSurvivors)

------------------------------------------------------------------------
-- Bounded transition radius.
------------------------------------------------------------------------

boundedRadiusTransitionObstruction :
  (changedSupport radius verifierWork singularBudget : Nat) →
  changedSupport ≤ radius →
  128 ≤ changedSupport * (verifierWork + singularBudget) →
  128 ≤ radius * (verifierWork + singularBudget)
boundedRadiusTransitionObstruction
  changedSupport radius verifierWork singularBudget
  withinRadius uncertaintyWork =
  NatP.≤-trans
    uncertaintyWork
    (NatP.*-monoˡ-≤ (verifierWork + singularBudget) withinRadius)

------------------------------------------------------------------------
-- Certificate surface for a concrete search primitive.
------------------------------------------------------------------------

record UncertaintyPricedTransition : Set where
  constructor uncertainty-priced-transition
  field
    changedSupport : Nat
    survivingSupport : Nat
    singularBudget : Nat
    verifierWork : Nat

    singularBudgetUncertainty128 :
      128 ≤ changedSupport * (survivingSupport + singularBudget)

    verifierWorkCoversSurvivingResidues :
      survivingSupport ≤ verifierWork

open UncertaintyPricedTransition public

pricedTransitionObstruction128 :
  (step : UncertaintyPricedTransition) →
  128 ≤ changedSupport step * (verifierWork step + singularBudget step)
pricedTransitionObstruction128 step =
  uncertaintyToTransitionWork
    (changedSupport step)
    (survivingSupport step)
    (singularBudget step)
    (verifierWork step)
    (singularBudgetUncertainty128 step)
    (verifierWorkCoversSurvivingResidues step)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY / CURRENT STATUS
--
-- This module identifies the exact same-object bridge from support uncertainty
-- to charged transition work:
--
--   surviving output residues <= incremental update work.
--
-- Round 17 now contains one concrete implementation-class producer:
-- `MLKEMExactResidualTouchLowerBoundExact` proves the needed domination for an
-- explicitly materialised exact residual state, and
-- `MLKEMResidualTouchPathLowerBoundExact` sums that resource along a path.
-- Therefore the old statement that this producer was wholly missing is stale.
--
-- What remains open is broader: instantiate the support/singularity side on the
-- actual FIPS public matrices, and treat lazy/compressed/symbolic verifier states
-- through the separate sufficient-state/readout-capacity lane.  A generic total
-- attack-runtime lower bound is still intentionally not claimed.
------------------------------------------------------------------------
