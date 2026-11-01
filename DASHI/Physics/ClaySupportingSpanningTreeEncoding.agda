module DASHI.Physics.ClaySupportingSpanningTreeEncoding where

------------------------------------------------------------------------
-- Elementary, fully-proved rooted-spanning-tree / DFS-encoding beams (YM P06).
--
-- Companion to `DASHI.Physics.ClaySupportingGraphCombinatorics` and
-- `DASHI.Physics.ClaySupportingPolymerCounting`.  As in those modules,
-- every declaration here is a genuine Agda proof over concrete data: there
-- are NO `postulate`s and NO added axioms.
--
-- This module supplies the P06 "encoding consequence" beams named in the
-- plan: once a connected finite skeleton is presented as a rooted spanning
-- tree, its DFS/Euler tour
--
--   * covers every vertex of the tree                (dfsWalk-covers, re-used)
--   * has length at most twice the tree size         (dfsWalk-length-≤)
--
-- and a *canonical decoder* (Option A of the plan) upgrades an encoding into
-- an injection, which the pigeonhole beam turns into the Cⁿ polymer count:
--
--   leftInverse⇒injective        a decoder dec with dec∘enc = id makes enc
--                                injective
--   canonicalEncodingCountBound  enc : Fin numSkel ↪ Fin (walkCount v (2n))
--                                with such a decoder ⇒ numSkel ≤ (Δ²)ⁿ
--
-- Honesty boundary (unchanged and deliberate): this does NOT discharge any
-- open Clay leaf.  The genuinely nontrivial graph theory -- that every
-- connected size-n skeleton through v *admits* a rooted spanning tree whose
-- Euler tour is a distinct length-2n walk from v, i.e. the existence of the
-- canonical tree and the decoder inverting the encoding -- is left as an
-- explicit hypothesis (`t`, `dec`, `decenc`), not asserted.  What is proved
-- is the counting consequence: once such a decoder is supplied, the Cⁿ bound
-- follows rigorously (Option A of the plan).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (n≤1+n; ≤-refl; ≤-trans)
open import Data.List.Base using (List; length)
open import Data.Fin.Base using (Fin)
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

open import DASHI.Physics.ClaySupportingElementaryLemmas using (pow)
open import DASHI.Physics.ClaySupportingGraphCombinatorics
  using ( RTree; node; size; dfsWalk; _∈T_; _∈L_
        ; dfsWalk-length; dfsWalk-covers
        ; BoundedDegreeBy; walkCount )
open import DASHI.Physics.ClaySupportingPolymerCounting
  using (polymerSkeletonCountBound)

------------------------------------------------------------------------
-- §1.  DFS coverage of a rooted spanning tree.
--
-- Every vertex of the tree lies on its Euler tour.  This is exactly the
-- graph-combinatorics `dfsWalk-covers`, re-exported here under the P06 name
-- to make the encoding contract explicit: the tour is a *cover* of S.

spanningTreeDFSCovers :
  {V : Set} {v : V} (t : RTree V) → v ∈T t → v ∈L dfsWalk t
spanningTreeDFSCovers = dfsWalk-covers

------------------------------------------------------------------------
-- §2.  DFS tour length ≤ 2·size.
--
-- The Euler tour traverses every edge exactly twice, so its length is
-- 2·size − 1; in particular  |dfsWalk t| ≤ size t + size t = 2·|t|.  This is
-- the |γ_S| ≤ 2|S| bound of the plan.

dfsWalk-length-≤ :
  {V : Set} (t : RTree V) → length (dfsWalk t) ≤ size t + size t
dfsWalk-length-≤ t =
  subst (length (dfsWalk t) ≤_) (dfsWalk-length t) (n≤1+n (length (dfsWalk t)))

------------------------------------------------------------------------
-- §3.  A left inverse upgrades a map to an injection.
--
-- If `dec` inverts `enc` on the left (dec (enc a) ≡ a for all a), then `enc`
-- is injective.  This is the abstract content of Option A: a canonical
-- decoder `dec = (S ↦ nodeSet (spanning tree)) ∘ (walk ↦ tree)` recovering S
-- from enc(S) makes the DFS encoding injective.

leftInverse⇒injective :
  {A B : Set} (enc : A → B) (dec : B → A) →
  (∀ a → dec (enc a) ≡ a) →
  Injective _≡_ _≡_ enc
leftInverse⇒injective enc dec decenc {x} {y} encx≡ency =
  trans (sym (decenc x)) (trans (cong dec encx≡ency) (decenc y))

------------------------------------------------------------------------
-- §4.  Canonical-encoding polymer-count bound (Option A).
--
-- Given the DFS encoding of the size-n connected skeletons through v into
-- the length-2n walks from v, together with a canonical decoder inverting
-- it, the number of skeletons is ≤ (Δ²)ⁿ.  The existence of the encoding and
-- decoder is the (open) graph-theory leaf; the count bound is proved.

canonicalEncodingCountBound :
  {V : Set} (nbrs : V → List V) (Δ : ℕ) →
  BoundedDegreeBy nbrs Δ →
  (v : V) (n numSkel : ℕ)
  (enc : Fin numSkel → Fin (walkCount nbrs v (n + n)))
  (dec : Fin (walkCount nbrs v (n + n)) → Fin numSkel) →
  (∀ s → dec (enc s) ≡ s) →
  numSkel ≤ pow (Δ * Δ) n
canonicalEncodingCountBound nbrs Δ deg v n numSkel enc dec decenc =
  polymerSkeletonCountBound nbrs Δ deg v n numSkel enc
    (leftInverse⇒injective enc dec decenc)
