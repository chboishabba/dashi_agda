module DASHI.Moonshine.DuncanSwisherExponentObserverFactorizationExact where

------------------------------------------------------------------------
-- TOP-DOWN OBSERVER FACTORIZATION OF MONSTER EXPONENT DEPTH
--
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Duncan--Swisher give two answers to the same p>3 consumer:
--
--   v_p(|M|).
--
-- The geometric answer uses the rational/quadratic supersingular stratum and
-- the minimum supersingular automorphism order m_p.  The modular answer uses
-- the three p-adic valuation contributions
--
--   v_p(J_1-J_{p+}), v_p(J_1-J_p), v_p(J_1-J_{p^2}).
--
-- DASHI CONTRIBUTION
--
-- Put those two source-natural observers over ONE theorem state and prove that
-- both are sufficient for the SAME denominator-cleared consumer 2*v_p(|M|).
-- No identification of the observer carriers is claimed: equality is only at
-- the declared consumer output.  The coarse support observer is then exposed as
-- an explicit further projection of the geometric depth observer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; _+_; _*_)
open import Data.Nat.Primality using (Prime)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as DS
import DASHI.Moonshine.DuncanSwisherModularValuationDepthMechanismExact as Modular

------------------------------------------------------------------------
-- One state carries the exact Theorem 1.2 authority and the Theorem 1.1
-- modular valuation authority indexed by that SAME exponent authority.
------------------------------------------------------------------------

record ExponentMechanismState
    (p : Nat) (prime : Prime p) (ge5 : 5 ≤ p) : Set where
  constructor exponentMechanismState
  field
    exponentAuthority : DS.DuncanSwisherExponentAuthority p prime ge5
    modularAuthority :
      Modular.DuncanSwisherModularValuationAuthority
        p prime ge5 exponentAuthority

open ExponentMechanismState public

publishedExponentMechanismState :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  ExponentMechanismState p prime ge5
publishedExponentMechanismState p prime ge5 =
  exponentMechanismState
    (DS.publishedDuncanSwisherExponentAuthority p prime ge5)
    (Modular.publishedDuncanSwisherModularValuationAuthority p prime ge5)

------------------------------------------------------------------------
-- Geometric observer: exact Theorem 1.2 branch + m_p.
------------------------------------------------------------------------

data ExponentStratum : Set where
  singletonRationalStratum : ExponentStratum
  multipleRationalStratum : ExponentStratum
  quadraticStratum : ExponentStratum

record GeometricDepthCode : Set where
  constructor geometricDepthCode
  field
    stratum : ExponentStratum
    minimumAutOrder : Nat

open GeometricDepthCode public

geometricDepthCodeOf :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  DS.DuncanSwisherExponentAuthority p prime ge5 →
  GeometricDepthCode
geometricDepthCodeOf E with DS.theorem12 E
... | DS.singletonRational fixedOne pairedZero doubled =
  geometricDepthCode singletonRationalStratum (DS.minimumAutomorphismOrder E)
... | DS.multipleRational fixedMany pairedZero doubled =
  geometricDepthCode multipleRationalStratum (DS.minimumAutomorphismOrder E)
... | DS.quadraticPresent pairedPositive valuationZero minTwo =
  geometricDepthCode quadraticStratum (DS.minimumAutomorphismOrder E)

depthFromGeometry : GeometricDepthCode → Nat
depthFromGeometry (geometricDepthCode singletonRationalStratum m) = 3 * m
depthFromGeometry (geometricDepthCode multipleRationalStratum m) = m
depthFromGeometry (geometricDepthCode quadraticStratum m) = 0

doubledMonsterValuation :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  ExponentMechanismState p prime ge5 → Nat
doubledMonsterValuation state =
  2 * DS.monsterValuation (exponentAuthority state)

geometricObserver :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  ExponentMechanismState p prime ge5 → GeometricDepthCode
geometricObserver state = geometricDepthCodeOf (exponentAuthority state)

geometryComputesDoubledValuation :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  (state : ExponentMechanismState p prime ge5) →
  depthFromGeometry (geometricObserver state)
  ≡ doubledMonsterValuation state
geometryComputesDoubledValuation state
  with DS.theorem12 (exponentAuthority state)
... | DS.singletonRational fixedOne pairedZero doubled = sym doubled
... | DS.multipleRational fixedMany pairedZero doubled = sym doubled
... | DS.quadraticPresent pairedPositive valuationZero minTwo
  rewrite valuationZero = refl

geometricObserverSufficientForDoubledValuation :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  Observer.Refines
    (doubledMonsterValuation {p = p} {prime = prime} {ge5 = ge5})
    geometricObserver
geometricObserverSufficientForDoubledValuation left right sameGeometry =
  trans
    (sym (geometryComputesDoubledValuation left))
    (trans
      (cong depthFromGeometry sameGeometry)
      (geometryComputesDoubledValuation right))

------------------------------------------------------------------------
-- Modular-function observer: the three Theorem 1.1 contributions.
------------------------------------------------------------------------

record ModularDepthCode : Set where
  constructor modularDepthCode
  field
    frickeContribution : Nat
    primeLevelContribution : Nat
    squareLevelContribution : Nat

open ModularDepthCode public

modularObserver :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  ExponentMechanismState p prime ge5 → ModularDepthCode
modularObserver state =
  modularDepthCode
    (Modular.frickeContribution (modularAuthority state))
    (Modular.primeLevelContribution (modularAuthority state))
    (Modular.squareLevelContribution (modularAuthority state))

depthFromModular : ModularDepthCode → Nat
depthFromModular code =
  2 *
    (frickeContribution code
      + (primeLevelContribution code + squareLevelContribution code))

modularComputesDoubledValuation :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  (state : ExponentMechanismState p prime ge5) →
  depthFromModular (modularObserver state)
  ≡ doubledMonsterValuation state
modularComputesDoubledValuation state =
  sym
    (cong (λ n → 2 * n)
      (Modular.theorem11 (modularAuthority state)))

modularObserverSufficientForDoubledValuation :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  Observer.Refines
    (doubledMonsterValuation {p = p} {prime = prime} {ge5 = ge5})
    modularObserver
modularObserverSufficientForDoubledValuation left right sameModular =
  trans
    (sym (modularComputesDoubledValuation left))
    (trans
      (cong depthFromModular sameModular)
      (modularComputesDoubledValuation right))

------------------------------------------------------------------------
-- Exact commuting square at the declared consumer.  The two observers need
-- not reconstruct or factor through one another.
------------------------------------------------------------------------

geometricAndModularDepthAgree :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  (state : ExponentMechanismState p prime ge5) →
  depthFromGeometry (geometricObserver state)
  ≡ depthFromModular (modularObserver state)
geometricAndModularDepthAgree state =
  trans
    (geometryComputesDoubledValuation state)
    (sym (modularComputesDoubledValuation state))

------------------------------------------------------------------------
-- Ogg/Monster support is a further coarse projection of geometric depth.
------------------------------------------------------------------------

data ExponentSupport : Set where
  supportPresent supportAbsent : ExponentSupport

supportFromGeometry : GeometricDepthCode → ExponentSupport
supportFromGeometry (geometricDepthCode singletonRationalStratum m) = supportPresent
supportFromGeometry (geometricDepthCode multipleRationalStratum m) = supportPresent
supportFromGeometry (geometricDepthCode quadraticStratum m) = supportAbsent

supportObserver :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  ExponentMechanismState p prime ge5 → ExponentSupport
supportObserver state = supportFromGeometry (geometricObserver state)

geometryRefinesSupport :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  Observer.Refines
    (supportObserver {p = p} {prime = prime} {ge5 = ge5})
    geometricObserver
geometryRefinesSupport left right sameGeometry =
  cong supportFromGeometry sameGeometry

------------------------------------------------------------------------
-- Boundary: same consumer output is not an identification of the two observer
-- carriers, and support is deliberately a coarser public projection.
------------------------------------------------------------------------

record DuncanSwisherExponentObserverBoundary : Set where
  constructor duncanSwisherExponentObserverBoundary
  field
    geometricObserverComputesDoubledValuation : Bool
    modularObserverComputesDoubledValuation : Bool
    geometricAndModularOutputsProvedEqual : Bool
    observerCarriersIdentified : Bool
    supportFactorsThroughGeometry : Bool
    supportEqualsFullExponentDepth : Bool
    theoremExtendedToTwoOrThreeHere : Bool

canonicalDuncanSwisherExponentObserverBoundary :
  DuncanSwisherExponentObserverBoundary
canonicalDuncanSwisherExponentObserverBoundary =
  duncanSwisherExponentObserverBoundary
    true true true false true false false
