module DASHI.Chemistry.HydrogenMolecularInventoryExact where

-- Classical reaction chemistry: water electrolysis, Sabatier methanation,
-- methane combustion. Not credited to Michael McLaren or to DASHI.
-- The natural-number polynomial solver is existing Agda standard library
-- machinery, already reused in DASHI.Algebra.BalancedTernaryRankNegationExact.
-- User-directed construction; ChatGPT-drafted source on 2026-11-09.
-- A molecular inventory pathway is a *mathematical* reachable-state model,
-- not a patent, observed rate, device design or physical-efficiency proof.

open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

record Inventory : Set where
  constructor inv
  field
    water : Nat
    hydrogenGas : Nat
    oxygenGas : Nat
    carbonDioxide : Nat
    methane : Nat

open Inventory public

carbonAtoms : Inventory → Nat
carbonAtoms x = carbonDioxide x + methane x

hydrogenAtoms : Inventory → Nat
hydrogenAtoms x = 2 * water x + 2 * hydrogenGas x + 4 * methane x

oxygenAtoms : Inventory → Nat
oxygenAtoms x = water x + 2 * oxygenGas x + 2 * carbonDioxide x

-- Every transition is guarded by construction. An electrolysis step
-- consumes 2 water molecules; a Sabatier step consumes 1 CO2 and 4 H2;
-- a combustion step consumes 1 CH4 and 2 O2.
data MolecularStep : Inventory → Inventory → Set where
  electrolyse : (w h o c m : Nat) →
    MolecularStep
      (inv (suc (suc w)) h o c m)
      (inv w (suc (suc h)) (suc o) c m)

  methanate : (w h o c m : Nat) →
    MolecularStep
      (inv w (suc (suc (suc (suc h)))) o (suc c) m)
      (inv (suc (suc w)) h o c (suc m))

  combust : (w h o c m : Nat) →
    MolecularStep
      (inv w h (suc (suc o)) c (suc m))
      (inv (suc (suc w)) h o (suc c) m)

stepConservesCarbon :
  ∀ {x y} → MolecularStep x y → carbonAtoms x ≡ carbonAtoms y
stepConservesCarbon (electrolyse w h o c m) = refl
stepConservesCarbon (methanate w h o c m) =
  solve 2
    (λ c m → ((con 1 :+ c) :+ m)
       := (c :+ (con 1 :+ m)))
    refl c m
stepConservesCarbon (combust w h o c m) =
  solve 2
    (λ c m → (c :+ (con 1 :+ m))
       := ((con 1 :+ c) :+ m))
    refl c m

stepConservesHydrogen :
  ∀ {x y} → MolecularStep x y → hydrogenAtoms x ≡ hydrogenAtoms y
stepConservesHydrogen (electrolyse w h o c m) =
  solve 3
    (λ w h m →
      (((con 2 :* (con 2 :+ w)) :+ (con 2 :* h)) :+ (con 4 :* m))
      :=
      (((con 2 :* w) :+ (con 2 :* (con 2 :+ h))) :+ (con 4 :* m)))
    refl w h m
stepConservesHydrogen (methanate w h o c m) =
  solve 3
    (λ w h m →
      (((con 2 :* w) :+ (con 2 :* (con 4 :+ h))) :+ (con 4 :* m))
      :=
      (((con 2 :* (con 2 :+ w)) :+ (con 2 :* h))
        :+ (con 4 :* (con 1 :+ m))))
    refl w h m
stepConservesHydrogen (combust w h o c m) =
  solve 3
    (λ w h m →
      (((con 2 :* w) :+ (con 2 :* h))
        :+ (con 4 :* (con 1 :+ m)))
      :=
      (((con 2 :* (con 2 :+ w)) :+ (con 2 :* h))
        :+ (con 4 :* m)))
    refl w h m

stepConservesOxygen :
  ∀ {x y} → MolecularStep x y → oxygenAtoms x ≡ oxygenAtoms y
stepConservesOxygen (electrolyse w h o c m) =
  solve 3
    (λ w o c →
      (((con 2 :+ w) :+ (con 2 :* o)) :+ (con 2 :* c))
      :=
      ((w :+ (con 2 :* (con 1 :+ o))) :+ (con 2 :* c)))
    refl w o c
stepConservesOxygen (methanate w h o c m) =
  solve 3
    (λ w o c →
      ((w :+ (con 2 :* o)) :+ (con 2 :* (con 1 :+ c)))
      :=
      (((con 2 :+ w) :+ (con 2 :* o)) :+ (con 2 :* c)))
    refl w o c
stepConservesOxygen (combust w h o c m) =
  solve 3
    (λ w o c →
      ((w :+ (con 2 :* (con 2 :+ o))) :+ (con 2 :* c))
      :=
      (((con 2 :+ w) :+ (con 2 :* o))
        :+ (con 2 :* (con 1 :+ c))))
    refl w o c

data MolecularPath : Inventory → Inventory → Set where
  empty : (x : Inventory) → MolecularPath x x
  thenStep : ∀ {x y z} →
    MolecularStep x y → MolecularPath y z → MolecularPath x z

pathConservesCarbon :
  ∀ {x y} → MolecularPath x y → carbonAtoms x ≡ carbonAtoms y
pathConservesCarbon (empty x) = refl
pathConservesCarbon (thenStep step rest) =
  trans (stepConservesCarbon step) (pathConservesCarbon rest)

pathConservesHydrogen :
  ∀ {x y} → MolecularPath x y → hydrogenAtoms x ≡ hydrogenAtoms y
pathConservesHydrogen (empty x) = refl
pathConservesHydrogen (thenStep step rest) =
  trans (stepConservesHydrogen step) (pathConservesHydrogen rest)

pathConservesOxygen :
  ∀ {x y} → MolecularPath x y → oxygenAtoms x ≡ oxygenAtoms y
pathConservesOxygen (empty x) = refl
pathConservesOxygen (thenStep step rest) =
  trans (stepConservesOxygen step) (pathConservesOxygen rest)

-- Example finite path: split 2 H2O twice, then methanate 1 CO2;
-- needs 4 H2, so begin with 4 H2O, not 2. A separate example
-- is intentionally not fabricated without proof of inventory alignment.
