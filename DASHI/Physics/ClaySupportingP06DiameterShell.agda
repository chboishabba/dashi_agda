module DASHI.Physics.ClaySupportingP06DiameterShell where

------------------------------------------------------------------------
-- Elementary, fully-proved size-shell vs diameter-shell bookkeeping (YM P06).
--
-- Companion to `DASHI.Physics.ClaySupportingGraphCombinatorics`,
-- `...PolymerCounting` and `...SpanningTreeEncoding`.  Every declaration
-- here is a genuine Agda proof over concrete data: there are NO `postulate`s
-- and NO added axioms.
--
-- The plan asks P06 to *decide* which shell KP consumes -- the size shell
-- (#{|S|=n} ≤ Cⁿ) or the diameter shell (S ⊆ B(v,R)) -- and to prove the
-- conversion actually used.  This module makes both routes concrete and
-- machine-checked so the decision is quantitative rather than handwaved:
--
--   ballSizeGeometricBound   |B(v,R)| ≤ Σ_{j≤R} Δʲ  (root-ball growth)
--   diameterShellCrudeBound  the crude subset route over the ball is
--                            ≤ 2^{Σ_{j≤R} Δʲ}  -- DOUBLE exponential in R
--   sizeShellBound           the size-shell route sums per-size Cⁿ bounds to
--                            Σ_{n≤R} Cⁿ  -- SINGLE exponential (KP-summable)
--
-- Decision recorded by these bounds: the size shell (C = Δ²) yields a single
-- exponential geometric sum that KP can consume; the crude diameter-shell
-- subset count is doubly exponential and is NOT KP-summable unless size is
-- consumed.  Hence the honest P06 route is the size shell fed by the
-- walk/spanning-tree encoding, exactly as `...PolymerCounting` provides.
--
-- Honesty boundary (unchanged): this discharges no open Clay leaf.  It is
-- the counting/bookkeeping algebra that fixes which shell the argument runs
-- on; the analytic P10 decay-per-size input remains open and is not asserted.
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (≤-trans; ≤-refl)
open import Data.List.Base using (List)

open import DASHI.Physics.ClaySupportingElementaryLemmas using (pow; geomSum)
open import DASHI.Physics.ClaySupportingGraphCombinatorics
  using (BoundedDegreeBy; reachSum; RootBallGeometricGrowth)
open import DASHI.Physics.ClaySupportingPolymerCounting
  using (shellSum; shellCountBound)
open import DASHI.Physics.ClaySupportingDepthSeparation using (pow-2-mono)

------------------------------------------------------------------------
-- §1.  Root-ball (diameter-shell carrier) size bound.
--
-- The number of vertices reachable within R steps of v is bounded by the
-- geometric sum of the degree bound:  |B(v,R)| ≤ Σ_{j=0}^{R} Δʲ.  This is
-- the honest "size from diameter" bound in a bounded-degree graph; it is
-- `RootBallGeometricGrowth`, re-exported under the P06 name.

ballSizeGeometricBound :
  {V : Set} (nbrs : V → List V) (Δ : ℕ) →
  BoundedDegreeBy nbrs Δ →
  ∀ (v : V) (R : ℕ) → reachSum nbrs v R ≤ geomSum Δ R
ballSizeGeometricBound = RootBallGeometricGrowth

------------------------------------------------------------------------
-- §2.  Crude diameter-shell subset count is doubly exponential.
--
-- If one counts connected sets by enumerating subsets of the root ball, the
-- number of subsets of an m-element ball is 2^m.  With m = |B(v,R)| ≤ Σ Δʲ
-- this gives the crude bound  #subsets ≤ 2^{Σ_{j≤R} Δʲ}  -- doubly
-- exponential in R, hence NOT KP-summable.  We prove exactly that lift.

diameterShellCrudeBound :
  (Δ R numSubsets ballSize : ℕ) →
  numSubsets ≤ pow 2 ballSize →     -- crude enumeration: subsets of the ball
  ballSize ≤ geomSum Δ R →           -- root-ball growth (§1)
  numSubsets ≤ pow 2 (geomSum Δ R)
diameterShellCrudeBound Δ R numSubsets ballSize hsub hball =
  ≤-trans hsub (pow-2-mono hball)

------------------------------------------------------------------------
-- §3.  Size-shell count is singly exponential (the KP-summable route).
--
-- If the per-size skeleton counts are bounded by Cⁿ with C = Δ² (as
-- `polymerSkeletonCountBound` delivers), then summing over the size shell
-- 0..R is bounded by the finite geometric sum Σ_{n≤R} Cⁿ -- single
-- exponential, and hence the shell KP actually consumes.

sizeShellBound :
  (Δ : ℕ) (count : ℕ → ℕ) →
  (∀ n → count n ≤ pow (Δ * Δ) n) →
  ∀ R → shellSum count R ≤ geomSum (Δ * Δ) R
sizeShellBound Δ count h = shellCountBound (Δ * Δ) count h
