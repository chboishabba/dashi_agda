module DASHI.Physics.LiftToFullState where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; _++_; replicate)
open import DASHI.Algebra.Trit using (Trit; zer)

open import DASHI.Physics.TailCollapseProof as TCP

------------------------------------------------------------------------
-- Invariant coarse subspace

embedCoarse : ∀ (m k : Nat) → Vec Trit m → Vec Trit (m + k)
embedCoarse m k c = c ++ replicate k zer

coarseProj : ∀ (m k : Nat) → Vec Trit (m + k) → Vec Trit m
coarseProj m k x = TCP.coarseOf m k x

coarse-invariant-R :
  ∀ (m k : Nat) (x : Vec Trit (m + k)) →
  coarseProj m k (TCP.Rᵣ {m} {k} x) ≡ coarseProj m k x
coarse-invariant-R m k x with TCP.split m k x
... | (c , t) rewrite TCP.split-++ m k c (TCP.shiftTail t) = refl

coarse-invariant-P :
  ∀ (m k : Nat) (x : Vec Trit (m + k)) →
  coarseProj m k (TCP.Pᵣ {m} {k} x) ≡ coarseProj m k x
coarse-invariant-P m k x with TCP.split m k x
... | (c , t) rewrite TCP.split-++ m k c (TCP.projTail t) = refl

coarse-invariant-T :
  ∀ (m k : Nat) (x : Vec Trit (m + k)) →
  coarseProj m k (TCP.Tᵣ {m} {k} x) ≡ coarseProj m k x
coarse-invariant-T m k x =
  trans (coarse-invariant-P m k (TCP.Rᵣ {m} {k} x))
        (coarse-invariant-R m k x)

------------------------------------------------------------------------
-- Finite-time collapse + invariant geometry, packaged

coarse-invariant-iter :
  ∀ (m k n : Nat) (x : Vec Trit (m + k)) →
  coarseProj m k (TCP.iterate n (TCP.Tᵣ {m} {k}) x) ≡ coarseProj m k x
coarse-invariant-iter m k zero x = refl
coarse-invariant-iter m k (suc n) x =
  trans
    (coarse-invariant-iter m k n (TCP.Tᵣ {m} {k} x))
    (coarse-invariant-T m k x)

finiteTimeCollapse-to-geometry :
  ∀ (m k : Nat) (x : Vec Trit (m + k)) →
  ( coarseProj m k (TCP.iterate k (TCP.Tᵣ {m} {k}) x) ≡ coarseProj m k x )
  ×
  ( TCP.tailOf m k (TCP.iterate k (TCP.Tᵣ {m} {k}) x) ≡ replicate k zer )
finiteTimeCollapse-to-geometry m k x =
  ( coarse-invariant-iter m k k x
  , TCP.tailOf-after-Tk m k x
  )

invariantCoarseSubspace :
  ∀ (m k : Nat) (c : Vec Trit m) →
  TCP.Tᵣ {m} {k} (embedCoarse m k c) ≡ embedCoarse m k c
invariantCoarseSubspace m k c
  rewrite TCP.Rᵣ-++ m k c (replicate k zer)
        | TCP.Pᵣ-++ m k c (TCP.shiftTail (replicate k zer))
        | TCP.shiftTail-replicate {k}
        | TCP.projTail-replicate {k}
  = refl
