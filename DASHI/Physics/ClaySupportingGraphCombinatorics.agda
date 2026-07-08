module DASHI.Physics.ClaySupportingGraphCombinatorics where

------------------------------------------------------------------------
-- Elementary, fully-proved graph / combinatorics substrate.
--
-- Companion to `DASHI.Physics.ClaySupportingElementaryLemmas`.  As there,
-- every declaration in this module is a genuine Agda proof over concrete
-- data: there are NO `postulate`s and NO added axioms.  These are the
-- ordinary finite-combinatorics "beams" that the P06 root-ball / DFS /
-- skeleton-counting stage and the YM KP / polymer-counting stage lean on.
--
-- Scope / honesty boundary (unchanged): none of this discharges an open
-- analytic Clay leaf.  It provides the reusable, machine-checked finite
-- counting facts so those leaves can be stated against a trustworthy
-- combinatorial base rather than handwaved.
--
-- Theorem chain provided here:
--   walkCount recurrence
--     -> BoundedDegreeWalkCount        (#walks of length n  <=  Δ^n)
--   RTree / dfsWalk (Euler tour)
--     -> dfsWalk-length                (|dfsWalk t| + 1 = 2·|t|)
--     -> dfsWalk-covers                (every tree node is on the walk)
--   RootBallGeometricGrowth            (Σ_{j≤R} #walks_j  <=  Σ_{j≤R} Δ^j)
--   polymerWalkCountBound              (#walks of length 2n  <=  (Δ²)^n)
--   geomSum-closed                     ((Σ_{j≤R} bʲ)·b + 1 = b^{R+1} + Σ …)
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base
  using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using ( +-assoc; +-comm; +-suc
        ; *-assoc; *-comm; *-distribʳ-+; *-identityˡ; *-identityʳ
        ; ≤-refl; ≤-trans; +-mono-≤; *-mono-≤ )
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans; subst)

open import DASHI.Physics.ClaySupportingElementaryLemmas
  using (pow; geomSum)

------------------------------------------------------------------------
-- §0.  A finite graph, given concretely by a neighbour-list function.

-- `nbrs v` lists the out-neighbours of `v`.  `BoundedDegreeBy nbrs Δ` says
-- every vertex has at most Δ of them.
BoundedDegreeBy : {V : Set} → (V → List V) → ℕ → Set
BoundedDegreeBy nbrs Δ = ∀ v → length (nbrs v) ≤ Δ

------------------------------------------------------------------------
-- §1.  Walk counting.
--
-- `walkCount nbrs v n` is the number of length-n walks starting at v; it
-- obeys the standard recurrence  W(v,0)=1,  W(v,n+1)=Σ_{u∈nbrs v} W(u,n).

sumOver : {V : Set} → List V → (V → ℕ) → ℕ
sumOver []       f = 0
sumOver (x ∷ xs) f = f x + sumOver xs f

walkCount : {V : Set} → (V → List V) → V → ℕ → ℕ
walkCount nbrs v zero    = 1
walkCount nbrs v (suc n) = sumOver (nbrs v) (λ u → walkCount nbrs u n)

-- Σ_{x∈xs} f x  ≤  |xs| · B    whenever every f x ≤ B.
sumOver-bound :
  {V : Set} (xs : List V) (f : V → ℕ) (B : ℕ) →
  (∀ x → f x ≤ B) → sumOver xs f ≤ length xs * B
sumOver-bound []       f B h = z≤n
sumOver-bound (x ∷ xs) f B h =
  +-mono-≤ (h x) (sumOver-bound xs f B h)

-- BoundedDegreeWalkCount:  #{walks of length n from v}  ≤  Δ^n.
BoundedDegreeWalkCount :
  {V : Set} (nbrs : V → List V) (Δ : ℕ) →
  BoundedDegreeBy nbrs Δ →
  ∀ (v : V) (n : ℕ) → walkCount nbrs v n ≤ pow Δ n
BoundedDegreeWalkCount nbrs Δ deg v zero    = ≤-refl
BoundedDegreeWalkCount nbrs Δ deg v (suc n) =
  ≤-trans
    (sumOver-bound (nbrs v) (λ u → walkCount nbrs u n) (pow Δ n)
       (λ u → BoundedDegreeWalkCount nbrs Δ deg u n))
    (*-mono-≤ (deg v) (≤-refl {pow Δ n}))

------------------------------------------------------------------------
-- §2.  Rooted trees and their DFS (Euler-tour) walk.

data RTree (V : Set) : Set where
  node : V → List (RTree V) → RTree V

mutual
  size : {V : Set} → RTree V → ℕ
  size (node x cs) = suc (sizeF cs)

  sizeF : {V : Set} → List (RTree V) → ℕ
  sizeF []       = 0
  sizeF (t ∷ ts) = size t + sizeF ts

-- Euler tour: enter root, recurse into each child, returning to root.
mutual
  dfsWalk : {V : Set} → RTree V → List V
  dfsWalk (node x cs) = x ∷ dfsWalkF x cs

  dfsWalkF : {V : Set} → V → List (RTree V) → List V
  dfsWalkF x []       = []
  dfsWalkF x (t ∷ ts) = dfsWalk t ++ (x ∷ dfsWalkF x ts)

private
  length-++ : {V : Set} (xs ys : List V) →
              length (xs ++ ys) ≡ length xs + length ys
  length-++ []       ys = refl
  length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

  -- (a+a)+(b+b) = (a+b)+(a+b).
  rearr : ∀ a b → (a + a) + (b + b) ≡ (a + b) + (a + b)
  rearr a b =
    trans (+-assoc a a (b + b))
      (trans (cong (a +_) (sym (+-assoc a b b)))
        (trans (cong (λ z → a + (z + b)) (+-comm a b))
          (trans (cong (a +_) (+-assoc b a b))
                 (sym (+-assoc a b (a + b))))))

-- RootedTreeDFSWalkLength:  |dfsWalk t| + 1 = size t + size t
-- (i.e. the Euler tour traverses each edge exactly twice).
mutual
  dfsWalk-length :
    {V : Set} (t : RTree V) → suc (length (dfsWalk t)) ≡ size t + size t
  dfsWalk-length (node x cs) =
    trans (cong (λ z → suc (suc z)) (dfsWalkF-length x cs))
          (sym (cong suc (+-suc (sizeF cs) (sizeF cs))))

  dfsWalkF-length :
    {V : Set} (x : V) (cs : List (RTree V)) →
    length (dfsWalkF x cs) ≡ sizeF cs + sizeF cs
  dfsWalkF-length x []       = refl
  dfsWalkF-length x (t ∷ ts) =
    trans (length-++ (dfsWalk t) (x ∷ dfsWalkF x ts))
      (trans (cong (λ z → length (dfsWalk t) + suc z) (dfsWalkF-length x ts))
        (trans (+-suc (length (dfsWalk t)) (sizeF ts + sizeF ts))
          (trans (cong (_+ (sizeF ts + sizeF ts)) (dfsWalk-length t))
                 (rearr (size t) (sizeF ts)))))

------------------------------------------------------------------------
-- §3.  DFS coverage: every vertex of the tree lies on its Euler tour.

data _∈L_ {V : Set} (v : V) : List V → Set where
  hereL  : ∀ {xs} → v ∈L (v ∷ xs)
  thereL : ∀ {y xs} → v ∈L xs → v ∈L (y ∷ xs)

∈L-++ˡ : {V : Set} {v : V} {xs : List V} (ys : List V) →
         v ∈L xs → v ∈L (xs ++ ys)
∈L-++ˡ ys hereL      = hereL
∈L-++ˡ ys (thereL p) = thereL (∈L-++ˡ ys p)

∈L-++ʳ : {V : Set} {v : V} (xs : List V) {ys : List V} →
         v ∈L ys → v ∈L (xs ++ ys)
∈L-++ʳ []       p = p
∈L-++ʳ (x ∷ xs) p = thereL (∈L-++ʳ xs p)

mutual
  data _∈T_ {V : Set} (v : V) : RTree V → Set where
    rootT : ∀ {cs} → v ∈T node v cs
    subT  : ∀ {x cs} → v ∈F cs → v ∈T node x cs

  data _∈F_ {V : Set} (v : V) : List (RTree V) → Set where
    hereF  : ∀ {t ts} → v ∈T t → v ∈F (t ∷ ts)
    thereF : ∀ {t ts} → v ∈F ts → v ∈F (t ∷ ts)

-- RootedTreeDFSWalkCovers.
mutual
  dfsWalk-covers :
    {V : Set} {v : V} (t : RTree V) → v ∈T t → v ∈L dfsWalk t
  dfsWalk-covers (node x cs) rootT    = hereL
  dfsWalk-covers (node x cs) (subT p) = thereL (dfsWalkF-covers x cs p)

  dfsWalkF-covers :
    {V : Set} {v : V} (x : V) (cs : List (RTree V)) →
    v ∈F cs → v ∈L dfsWalkF x cs
  dfsWalkF-covers x (t ∷ ts) (hereF p)  =
    ∈L-++ˡ (x ∷ dfsWalkF x ts) (dfsWalk-covers t p)
  dfsWalkF-covers x (t ∷ ts) (thereF p) =
    ∈L-++ʳ (dfsWalk t) (thereL (dfsWalkF-covers x ts p))

------------------------------------------------------------------------
-- §4.  Root-ball geometric growth.
--
-- The number of vertices reachable within R steps of v is bounded by the
-- geometric sum of the degree bound:  Σ_{j=0}^{R} #walks_j ≤ Σ_{j=0}^{R} Δ^j.

reachSum : {V : Set} → (V → List V) → V → ℕ → ℕ
reachSum nbrs v zero    = walkCount nbrs v zero
reachSum nbrs v (suc R) = walkCount nbrs v (suc R) + reachSum nbrs v R

-- RootBallGeometricGrowth.
RootBallGeometricGrowth :
  {V : Set} (nbrs : V → List V) (Δ : ℕ) →
  BoundedDegreeBy nbrs Δ →
  ∀ (v : V) (R : ℕ) → reachSum nbrs v R ≤ geomSum Δ R
RootBallGeometricGrowth nbrs Δ deg v zero    =
  BoundedDegreeWalkCount nbrs Δ deg v zero
RootBallGeometricGrowth nbrs Δ deg v (suc R) =
  +-mono-≤ (BoundedDegreeWalkCount nbrs Δ deg v (suc R))
           (RootBallGeometricGrowth nbrs Δ deg v R)

------------------------------------------------------------------------
-- §5.  Polymer / reduced-skeleton counting core.
--
-- A connected size-n polymer through v admits a spanning tree whose Euler
-- tour is a length-2n walk from v (the graph-theory embedding step is the
-- open combinatorial leaf and is deliberately NOT asserted here).  The
-- quantitative counting core of that argument is fully proved: the number
-- of length-2n walks from v is bounded by (Δ²)^n, i.e. C^n with C = Δ².

private
  pow-+ : ∀ b m k → pow b (m + k) ≡ pow b m * pow b k
  pow-+ b zero    k = sym (*-identityˡ (pow b k))
  pow-+ b (suc m) k =
    trans (cong (b *_) (pow-+ b m k))
          (sym (*-assoc b (pow b m) (pow b k)))

  sq-swap : ∀ a p → (a * p) * (a * p) ≡ (a * a) * (p * p)
  sq-swap a p =
    trans (*-assoc a p (a * p))
      (trans (cong (a *_) (sym (*-assoc p a p)))
        (trans (cong (λ z → a * (z * p)) (*-comm p a))
          (trans (cong (a *_) (*-assoc a p p))
                 (sym (*-assoc a a (p * p))))))

  pow-double : ∀ b n → pow b (n + n) ≡ pow (b * b) n
  pow-double b zero    = refl
  pow-double b (suc n) =
    trans (pow-+ b (suc n) (suc n))
      (trans (sq-swap b (pow b n))
             (cong ((b * b) *_)
                   (trans (sym (pow-+ b n n)) (pow-double b n))))

-- polymerWalkCountBound.
polymerWalkCountBound :
  {V : Set} (nbrs : V → List V) (Δ : ℕ) →
  BoundedDegreeBy nbrs Δ →
  ∀ (v : V) (n : ℕ) → walkCount nbrs v (n + n) ≤ pow (Δ * Δ) n
polymerWalkCountBound nbrs Δ deg v n =
  subst (λ z → walkCount nbrs v (n + n) ≤ z)
        (pow-double Δ n)
        (BoundedDegreeWalkCount nbrs Δ deg v (n + n))

------------------------------------------------------------------------
-- §6.  Closed form for the finite geometric sum (KP tail bookkeeping).
--
--   (Σ_{j=0}^{R} bʲ)·b + 1 = b^{R+1} + Σ_{j=0}^{R} bʲ,
-- which rearranges to the familiar (b−1)·Σ + 1 = b^{R+1}.

geomSum-closed :
  ∀ (b R : ℕ) → geomSum b R * b + 1 ≡ pow b (suc R) + geomSum b R
geomSum-closed b zero =
  cong (_+ 1) (trans (*-identityˡ b) (sym (*-identityʳ b)))
geomSum-closed b (suc R) =
  trans (cong (_+ 1) (*-distribʳ-+ b (pow b (suc R)) (geomSum b R)))
    (trans (+-assoc (pow b (suc R) * b) (geomSum b R * b) 1)
      (trans (cong (pow b (suc R) * b +_) (geomSum-closed b R))
             (cong (_+ (pow b (suc R) + geomSum b R))
                   (*-comm (pow b (suc R)) b))))
