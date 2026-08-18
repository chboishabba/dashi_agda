module DASHI.Moonshine.BadPrimeFullLevel2TransportNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full level-N structures and the prime-to-level condition on Hecke transport.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
-- Hecke correspondences with auxiliary level structure.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact finite obstruction at the bad prime.
--
-- A full level-2 structure is an invertible frame on the four-element
-- 2-torsion module.  A degree-2 isogeny has a NONZERO point of E[2] in its
-- kernel.  Therefore its restriction to E[2] identifies zero with that
-- nonzero point and cannot be injective.  Consequently it cannot transport a
-- full level-2 frame by the same prime-to-level mechanism used for odd Hecke
-- correspondences.
--
-- This explains, at theorem level, why the repository's source-facing
-- P11FullLevel2DeckHeckeEquivarianceExact deliberately treats T3/T5 but excludes
-- T2.  It also prevents the internally-discovered positive five-state R2 from
-- being promoted to an X(2) self-correspondence merely because it projects to
-- the correct coarse Phi_2 / Brandt operator.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11Level44TwoAdicFixedVectorSeparationExact as F2

------------------------------------------------------------------------
-- The concrete four-element level-2 module.
------------------------------------------------------------------------

zero2 : F2.Vec2F2
zero2 = F2.vec2 F2.f0 F2.f0

kernelPoint : F2.Vec2F2
kernelPoint = F2.vec2 F2.f1 F2.f0

data Impossible : Set where

kernelPointNonzero : kernelPoint ≡ zero2 → Impossible
kernelPointNonzero ()

------------------------------------------------------------------------
-- Generic bad-prime restriction: one nonzero level point is killed.
------------------------------------------------------------------------

record TwoIsogenyLevel2Restriction (Target : Set) : Set where
  field
    restrict2 : F2.Vec2F2 → Target
    killsNonzeroKernelPoint : restrict2 kernelPoint ≡ restrict2 zero2
open TwoIsogenyLevel2Restriction public

record Injective {A B : Set} (f : A → B) : Set where
  field
    injective : {x y : A} → f x ≡ f y → x ≡ y
open Injective public

badPrimeRestrictionNotInjective :
  {Target : Set} →
  (R : TwoIsogenyLevel2Restriction Target) →
  Injective (restrict2 R) → Impossible
badPrimeRestrictionNotInjective R I =
  kernelPointNonzero (injective I (killsNonzeroKernelPoint R))

------------------------------------------------------------------------
-- A transported full frame would require an injective restriction.
------------------------------------------------------------------------

record FullLevel2TransportThrough
    {Target : Set}
    (R : TwoIsogenyLevel2Restriction Target) : Set where
  field
    restrictionInjective : Injective (restrict2 R)
open FullLevel2TransportThrough public

badPrimeCannotTransportFullLevel2Frame :
  {Target : Set} →
  (R : TwoIsogenyLevel2Restriction Target) →
  FullLevel2TransportThrough R → Impossible
badPrimeCannotTransportFullLevel2Frame R T =
  badPrimeRestrictionNotInjective R (restrictionInjective T)

------------------------------------------------------------------------
-- The obstruction can be seen on an explicit F2-linear quotient shadow.
-- Projection to the second coordinate kills kernelPoint=(1,0).
------------------------------------------------------------------------

killFirstCoordinate : F2.Vec2F2 → F2.F2
killFirstCoordinate v = F2.second v

explicitBadPrimeRestriction : TwoIsogenyLevel2Restriction F2.F2
explicitBadPrimeRestriction = record
  { restrict2 = killFirstCoordinate
  ; killsNonzeroKernelPoint = refl
  }

explicitBadPrimeRestrictionNotInjective :
  Injective killFirstCoordinate → Impossible
explicitBadPrimeRestrictionNotInjective =
  badPrimeRestrictionNotInjective explicitBadPrimeRestriction

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record BadPrimeFullLevel2TransportBoundary : Set where
  field
    nonzeroKernelPointConstructed : Bool
    kernelCollapseBlocksInjectivity : Bool
    primeToLevelTransportAppliesAtTwo : Bool
    coarseTwoIsogenyCanStillExist : Bool
    internalPositiveR2PromotedToFullLevel2HeckeByThisTheorem : Bool
    separateBadPrimeLocalCorrespondenceRequired : Bool

canonicalBadPrimeFullLevel2TransportBoundary :
  BadPrimeFullLevel2TransportBoundary
canonicalBadPrimeFullLevel2TransportBoundary = record
  { nonzeroKernelPointConstructed = true
  ; kernelCollapseBlocksInjectivity = true
  ; primeToLevelTransportAppliesAtTwo = false
  ; coarseTwoIsogenyCanStillExist = true
  ; internalPositiveR2PromotedToFullLevel2HeckeByThisTheorem = false
  ; separateBadPrimeLocalCorrespondenceRequired = true
  }
