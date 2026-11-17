module DASHI.Analysis.CollatzSyracuseResidualInverseLimitObstructionExact where

------------------------------------------------------------------------
-- RESIDUAL SURVIVOR INVERSE-LIMIT OBSTRUCTION
--
-- Cross-pollination: reuse the repository's generic resolution-tower /
-- inverse-limit carrier to state the literal Syracuse obstruction cleanly.
--
-- A coherent history here is NOT a p-adic completion and is NOT a Collatz
-- proof.  It is simply one literal start together with compatible proofs that
-- no strict descent has occurred by every finite horizon.
--
-- Such an infinite compatible survivor history contradicts any actual strict
-- descent witness for the same start.  Conversely, constructively proving only
-- that no inverse-limit point exists does not manufacture the finite descent
-- horizon required by LiteralStrictDescentSource.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (¬_)

import DASHI.Foundations.StratifiedResolutionTowerExact as Tower
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.Analysis.CollatzSyracuseUniversalStoppingCompilerExact as Stop

------------------------------------------------------------------------
-- Same-start survivor prefixes.
------------------------------------------------------------------------

NoStrictDescentAt : Syracuse.PositiveNat → Nat → Set
NoStrictDescentAt x m =
  ¬ (Syracuse.toNat (Syracuse.syracuseIterate m x) < Syracuse.toNat x)

record SurvivorPrefix (x : Syracuse.PositiveNat) (horizon : Nat) : Set where
  constructor survivor-prefix
  field
    survivesAt :
      (m : Nat) →
      m ≤ horizon →
      NoStrictDescentAt x m

open SurvivorPrefix public

-- Keep a finite-horizon proof valid when the admissible upper horizon grows by
-- one.  Kept local to avoid depending on stdlib lemma naming.
weakenUpper :
  {m r : Nat} →
  m ≤ r →
  m ≤ suc r
weakenUpper z≤n = z≤n
weakenUpper (s≤s proof) = s≤s (weakenUpper proof)

projectSurvivorPrefix :
  {x : Syracuse.PositiveNat} {r : Nat} →
  SurvivorPrefix x (suc r) →
  SurvivorPrefix x r
projectSurvivorPrefix prefix =
  survivor-prefix
    (λ m m≤r → survivesAt prefix m (weakenUpper m≤r))

survivorTower :
  (x : Syracuse.PositiveNat) →
  Tower.ResolutionTower
survivorTower x = record
  { Carrier = SurvivorPrefix x
  ; project = projectSurvivorPrefix
  }

------------------------------------------------------------------------
-- All-horizon survival <-> one coherent inverse-limit history.
--
-- The forward direction is constructive because the same global proof supplies
-- every finite prefix.  The reverse direction reads the horizon-m coordinate
-- at m itself.
------------------------------------------------------------------------

AllHorizonSurvivor : Syracuse.PositiveNat → Set
AllHorizonSurvivor x =
  (m : Nat) → NoStrictDescentAt x m

prefixFromAllHorizon :
  {x : Syracuse.PositiveNat} →
  AllHorizonSurvivor x →
  (horizon : Nat) →
  SurvivorPrefix x horizon
prefixFromAllHorizon global horizon =
  survivor-prefix (λ m _ → global m)

inversePointFromAllHorizon :
  {x : Syracuse.PositiveNat} →
  AllHorizonSurvivor x →
  Tower.InverseLimitPoint (survivorTower x)
inversePointFromAllHorizon global = record
  { atResolution = prefixFromAllHorizon global
  ; coherent = λ r → refl
  }

allHorizonFromInversePoint :
  {x : Syracuse.PositiveNat} →
  Tower.InverseLimitPoint (survivorTower x) →
  AllHorizonSurvivor x
allHorizonFromInversePoint point m =
  survivesAt
    (Tower.atResolution point m)
    m
    (≤-refl-local m)
  where
    ≤-refl-local : (n : Nat) → n ≤ n
    ≤-refl-local zero = z≤n
    ≤-refl-local (suc n) = s≤s (≤-refl-local n)

------------------------------------------------------------------------
-- Exact obstruction at the literal Syracuse consumer.
------------------------------------------------------------------------

infiniteSurvivorRefutesStrictDescent :
  {x : Syracuse.PositiveNat} →
  Tower.InverseLimitPoint (survivorTower x) →
  Stop.StrictDescentWithin x →
  ⊥
infiniteSurvivorRefutesStrictDescent point (m , descent) =
  allHorizonFromInversePoint point m descent

strictDescentSourceExcludesInfiniteSurvivor :
  Stop.LiteralStrictDescentSource →
  (x : Syracuse.PositiveNat) →
  1 < Syracuse.toNat x →
  Tower.InverseLimitPoint (survivorTower x) →
  ⊥
strictDescentSourceExcludesInfiniteSurvivor source x nontrivial point =
  infiniteSurvivorRefutesStrictDescent
    point
    (Stop.descend source x nontrivial)

universalStoppingExcludesInfiniteSurvivor :
  ((x : Syracuse.PositiveNat) → Stop.ReachesOne x) →
  (x : Syracuse.PositiveNat) →
  1 < Syracuse.toNat x →
  Tower.InverseLimitPoint (survivorTower x) →
  ⊥
universalStoppingExcludesInfiniteSurvivor stopping x nontrivial =
  strictDescentSourceExcludesInfiniteSurvivor
    (Stop.strictDescentFromUniversalStopping stopping)
    x nontrivial

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record ResidualInverseLimitBoundary : Set where
  constructor residualInverseLimitBoundary
  field
    residualSurvivorTowerPaid : Nat
    allHorizonToInversePointPaid : Nat
    inversePointToAllHorizonPaid : Nat
    infiniteHistoryRefutesStrictDescentPaid : Nat
    strictDescentExcludesInfiniteHistoryPaid : Nat

    noInverseLimitAutomaticallyConstructsDescent : Nat
    inverseLimitHistoryAutomaticallyProvesCollatz : Nat
    inverseLimitHistoryIdentifiedWithPadicCompletion : Nat

open ResidualInverseLimitBoundary public

canonicalResidualInverseLimitBoundary : ResidualInverseLimitBoundary
canonicalResidualInverseLimitBoundary =
  residualInverseLimitBoundary
    1 1 1 1 1
    0 0 0
