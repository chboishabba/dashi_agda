module DASHI.Crypto.MLKEMResidualTouchPathLowerBoundExact where

------------------------------------------------------------------------
-- ML-KEM: PATH-SUM LOWER BOUND FROM PER-EDGE RESIDUAL TOUCH OBSTRUCTION
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- PURPOSE
--
-- Once a concrete primitive has the per-edge full-rank obstruction
--
--     128 <= radius * touchCount,
--
-- every path of such primitive transitions inherits an additive lower bound.
-- Rather than divide by radius or introduce ceilings, we keep the statement
-- exact and division-free:
--
--     128 * (# transitions) <= radius * (total touches).
--
-- The robust singular-budget version replaces touchCount by
-- touchCount + singularBudget on each edge.
--
-- This is the first path-level computational resource theorem in the current
-- uncertainty programme.  It still does not assert that recovery must traverse
-- all candidates: candidate coverage/pruning/decision-tree lower bounds remain
-- a separate producer.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat using (Nat; _≤_; _+_; _*_)
import Data.Nat.Properties as NatP

------------------------------------------------------------------------
-- Fixed-radius per-edge resource certificate.
------------------------------------------------------------------------

record RadiusPricedTouchStep (radius : Nat) : Set where
  constructor radius-priced-touch-step
  field
    touchCount : Nat
    singularBudget : Nat
    edgeObstruction128 :
      128 ≤ radius * (touchCount + singularBudget)

open RadiusPricedTouchStep public

stepResource :
  ∀ {radius} → RadiusPricedTouchStep radius → Nat
stepResource step = touchCount step + singularBudget step

totalResource :
  ∀ {radius} → List (RadiusPricedTouchStep radius) → Nat
totalResource [] = 0
totalResource (step ∷ rest) = stepResource step + totalResource rest

-- Exact additive demand: one copy of 128 per primitive transition.
pathDemand128 :
  ∀ {radius} → List (RadiusPricedTouchStep radius) → Nat
pathDemand128 [] = 0
pathDemand128 (_ ∷ rest) = 128 + pathDemand128 rest

pathResidualTouchAreaLowerBound :
  ∀ {radius} →
  (steps : List (RadiusPricedTouchStep radius)) →
  pathDemand128 steps ≤ radius * totalResource steps
pathResidualTouchAreaLowerBound [] = NatP.≤-refl
pathResidualTouchAreaLowerBound {radius} (step ∷ rest)
  rewrite NatP.*-distribˡ-+ radius (stepResource step) (totalResource rest) =
    NatP.+-mono-≤
      (edgeObstruction128 step)
      (pathResidualTouchAreaLowerBound rest)

------------------------------------------------------------------------
-- Full-rank specialization keeps only materialised touch count.
------------------------------------------------------------------------

record FullRankRadiusPricedTouchStep (radius : Nat) : Set where
  constructor full-rank-radius-priced-touch-step
  field
    touchCount : Nat
    edgeObstruction128 : 128 ≤ radius * touchCount

open FullRankRadiusPricedTouchStep public

totalFullRankTouches :
  ∀ {radius} → List (FullRankRadiusPricedTouchStep radius) → Nat
totalFullRankTouches [] = 0
totalFullRankTouches (step ∷ rest) =
  FullRankRadiusPricedTouchStep.touchCount step + totalFullRankTouches rest

fullRankPathDemand128 :
  ∀ {radius} → List (FullRankRadiusPricedTouchStep radius) → Nat
fullRankPathDemand128 [] = 0
fullRankPathDemand128 (_ ∷ rest) = 128 + fullRankPathDemand128 rest

fullRankPathResidualTouchAreaLowerBound :
  ∀ {radius} →
  (steps : List (FullRankRadiusPricedTouchStep radius)) →
  fullRankPathDemand128 steps ≤ radius * totalFullRankTouches steps
fullRankPathResidualTouchAreaLowerBound [] = NatP.≤-refl
fullRankPathResidualTouchAreaLowerBound {radius} (step ∷ rest)
  rewrite NatP.*-distribˡ-+ radius
    (FullRankRadiusPricedTouchStep.touchCount step)
    (totalFullRankTouches rest) =
      NatP.+-mono-≤
        (FullRankRadiusPricedTouchStep.edgeObstruction128 step)
        (fullRankPathResidualTouchAreaLowerBound rest)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- This theorem prices a path once every edge has already been shown to be an
-- uncertainty-priced exact residual transition at the same primitive radius.
-- It does NOT prove:
--   * that a successful recovery path has any particular number of edges;
--   * that all candidates must be visited;
--   * that a compressed verifier must materialise these residual cells;
--   * a wall-clock lower bound.
--
-- The next route-killer is candidate/decision-tree coverage: establish how many
-- distinct protected-label alternatives a successful recovery procedure must
-- distinguish after observations and reconciliation.  Only then can this path
-- resource lower bound become a recovery lower bound.
------------------------------------------------------------------------
