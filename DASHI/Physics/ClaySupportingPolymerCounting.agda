module DASHI.Physics.ClaySupportingPolymerCounting where

------------------------------------------------------------------------
-- Elementary, fully-proved polymer-counting bridge.
--
-- Companion to `DASHI.Physics.ClaySupportingGraphCombinatorics` and
-- `DASHI.Physics.ClaySupportingElementaryLemmas`.  As in those modules,
-- every declaration here is a genuine Agda proof over concrete data:
-- there are NO `postulate`s and NO added axioms.
--
-- This module supplies the finite-cardinality "beam" that turns the walk
-- counting substrate into a polymer / reduced-skeleton counting bound of
-- the form  #{skeletons} ≤ Cⁿ.  Concretely it provides:
--
--   inj⇒≤                     an injection Fin m ↣ Fin n forces m ≤ n
--                             (the finite pigeonhole cardinality bound)
--   polymerSkeletonCountBound if the size-n connected skeletons through v
--                             inject into the length-(2n) walk indices from
--                             v, then their number is ≤ (Δ²)ⁿ
--   shellCountBound           a per-size Cⁿ bound sums (over the diameter
--                             shell) to a geometric-sum bound Σ_{n≤R} Cⁿ
--
-- Honesty boundary (unchanged and deliberate): this does NOT discharge any
-- open analytic Clay leaf.  The genuinely nontrivial graph-theory content
-- -- that every connected size-n skeleton through v admits a rooted
-- spanning tree whose DFS/Euler tour is a distinct length-(2n) walk from v,
-- i.e. that the encoding `Fin #skel ↣ Fin (walkCount v (2n))` exists -- is
-- left as an explicit HYPOTHESIS of `polymerSkeletonCountBound`, not
-- asserted.  What is proved is the quantitative counting consequence: once
-- such an injective encoding is supplied, the Cⁿ bound follows rigorously.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; ≮⇒≥; +-mono-≤)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (<⇒notInjective)
open import Function.Definitions using (Injective)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Physics.ClaySupportingElementaryLemmas
  using (pow; geomSum)
open import DASHI.Physics.ClaySupportingGraphCombinatorics
  using (BoundedDegreeBy; walkCount; polymerWalkCountBound)

------------------------------------------------------------------------
-- §1.  Finite pigeonhole cardinality bound.
--
-- An injection between finite index sets cannot increase cardinality:
-- if `encode : Fin m → Fin n` is injective then `m ≤ n`.  This is the
-- contrapositive of the standard pigeonhole principle `<⇒notInjective`.

inj⇒≤ :
  {m n : ℕ} {encode : Fin m → Fin n} →
  Injective _≡_ _≡_ encode → m ≤ n
inj⇒≤ {m} {n} {encode} inj =
  ≮⇒≥ (λ (n<m : n < m) → <⇒notInjective n<m inj)

------------------------------------------------------------------------
-- §2.  Polymer / reduced-skeleton counting bound.
--
-- Model: the size-n connected skeletons through a fixed root v are indexed
-- by `Fin numSkel`.  The DFS/Euler-tour embedding assigns to each such
-- skeleton a length-(n+n) walk from v; the walks from v are in turn indexed
-- by `Fin (walkCount nbrs v (n + n))` (walkCount is exactly the number of
-- such walks).  The embedding being an injection is the graph-theory leaf,
-- supplied here as the hypothesis `encode` + `inj`.
--
-- Conclusion:  numSkel ≤ (Δ²)ⁿ,  i.e. the Cⁿ polymer-counting core.

polymerSkeletonCountBound :
  {V : Set} (nbrs : V → List V) (Δ : ℕ) →
  BoundedDegreeBy nbrs Δ →
  (v : V) (n numSkel : ℕ)
  (encode : Fin numSkel → Fin (walkCount nbrs v (n + n))) →
  Injective _≡_ _≡_ encode →
  numSkel ≤ pow (Δ * Δ) n
polymerSkeletonCountBound nbrs Δ deg v n numSkel encode inj =
  ≤-trans (inj⇒≤ {encode = encode} inj)
          (polymerWalkCountBound nbrs Δ deg v n)

------------------------------------------------------------------------
-- §3.  Diameter-shell summation.
--
-- If the per-size skeleton counts `count n` are individually bounded by the
-- powers `Cⁿ = pow C n` (as delivered by `polymerSkeletonCountBound` with
-- C = Δ²), then summing over the diameter shell 0..R is bounded by the
-- finite geometric sum Σ_{n=0}^{R} Cⁿ = geomSum C R.  This is the counting
-- content behind `currentReducedSkeletonCardinalityBound`; the geometric
-- sum's closed form is `geomSum-closed` in the graph-combinatorics module.

shellSum : (ℕ → ℕ) → ℕ → ℕ            -- Σ_{n=0}^{R} count n
shellSum count zero    = count zero
shellSum count (suc R) = count (suc R) + shellSum count R

-- Pointwise per-size domination `count n ≤ pow C n` lifts to the shell.
shellCountBound :
  (C : ℕ) (count : ℕ → ℕ) →
  (∀ n → count n ≤ pow C n) →
  ∀ R → shellSum count R ≤ geomSum C R
shellCountBound C count h zero    = h zero
shellCountBound C count h (suc R) =
  +-mono-≤ (h (suc R)) (shellCountBound C count h R)
