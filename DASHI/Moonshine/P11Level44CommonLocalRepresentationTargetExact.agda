module DASHI.Moonshine.P11Level44CommonLocalRepresentationTargetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CORRECTION
--
-- Kimball Martin,
-- "The basis problem revisited",
-- Transactions of the American Mathematical Society 373 (2020), 4523--4559.
-- DOI: 10.1090/tran/8077.
--
-- Martin describes the classical Jacquet--Langlands correspondence on modular
-- form spaces as a NON-CANONICAL linear Hecke-module map and develops local and
-- global new/old-form theory to describe its image and kernel.  In particular,
-- the correspondence does not canonically identify arbitrary fixed-vector
-- spaces for two different compact-open subgroups.
--
-- Ralf Schmidt,
-- "Some remarks on local newforms for GL(2)",
-- J. Ramanujan Math. Soc. 17 (2002), 115--147.
--
-- DASHI CORRECTION
--
-- The old target "produce a canonical 3D map K(2)-fixed -> K_0(4)-fixed" was
-- too strong.  These are distinct fixed-vector subspaces of one local induced
-- representation.  The correct same-object target is COMMON REPRESENTATION,
-- not canonical equality of its different compact-open invariant subspaces.
--
-- This module constructs the finite compact ambient object explicitly:
-- six values on B(Z/4)\GL_2(Z/4).  Both three-coordinate models inject into
-- this ambient carrier.  Neither image contains the other, and their common
-- functions are exactly the two-coordinate intersection already proved in
-- P11Level44TwoAdicFixedSpaceIntersectionExact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ)

import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Principal
import DASHI.Moonshine.P11Level44TwoAdicAveragingNoGoExact as K0
import DASHI.Moonshine.P11Level44TwoAdicFixedSpaceIntersectionExact as Intersection
import DASHI.Moonshine.P11Level44TwoAdicTransverseAlignmentExact as Transverse

------------------------------------------------------------------------
-- One explicit finite compact ambient carrier.
------------------------------------------------------------------------

record CompactFunction6 : Set where
  constructor compactFunction6
  field
    at0 at1 at2 at3 at4 at5 : ℤ
open CompactFunction6 public

principalEmbed : Principal.Old3 → CompactFunction6
principalEmbed p = compactFunction6
  (Principal.x1 p)
  (Principal.x2 p)
  (Principal.x1 p)
  (Principal.x2 p)
  (Principal.x4 p)
  (Principal.x4 p)

k0Embed : K0.Bruhat3 → CompactFunction6
k0Embed k = compactFunction6
  (K0.wide k)
  (K0.wide k)
  (K0.wide k)
  (K0.wide k)
  (K0.left k)
  (K0.right k)

compactFunction6Ext :
  (u v : CompactFunction6) →
  at0 u ≡ at0 v → at1 u ≡ at1 v → at2 u ≡ at2 v →
  at3 u ≡ at3 v → at4 u ≡ at4 v → at5 u ≡ at5 v →
  u ≡ v
compactFunction6Ext
  (compactFunction6 a b c d e f)
  (compactFunction6 .a .b .c .d .e .f)
  refl refl refl refl refl refl = refl

principalEmbedInjective :
  {u v : Principal.Old3} → principalEmbed u ≡ principalEmbed v → u ≡ v
principalEmbedInjective {u} {v} eq =
  Transverse.old3Ext u v
    (cong at0 eq)
    (cong at1 eq)
    (cong at4 eq)

k0EmbedInjective :
  {u v : K0.Bruhat3} → k0Embed u ≡ k0Embed v → u ≡ v
k0EmbedInjective {u} {v} eq =
  Transverse.bruhat3Ext u v
    (cong at0 eq)
    (cong at4 eq)
    (cong at5 eq)

------------------------------------------------------------------------
-- Equality in the common ambient carrier is exactly the earlier pointwise
-- SameCompactFunction relation.
------------------------------------------------------------------------

sameCompactFromEmbedEquality :
  {p : Principal.Old3} {k : K0.Bruhat3} →
  principalEmbed p ≡ k0Embed k → Intersection.SameCompactFunction p k
sameCompactFromEmbedEquality eq = record
  { Intersection.at0 = cong at0 eq
  ; Intersection.at1 = cong at1 eq
  ; Intersection.at2 = cong at2 eq
  ; Intersection.at3 = cong at3 eq
  ; Intersection.at4 = cong at4 eq
  ; Intersection.at5 = cong at5 eq
  }

embedEqualityFromSameCompact :
  {p : Principal.Old3} {k : K0.Bruhat3} →
  Intersection.SameCompactFunction p k → principalEmbed p ≡ k0Embed k
embedEqualityFromSameCompact same =
  compactFunction6Ext _ _
    (Intersection.at0 same)
    (Intersection.at1 same)
    (Intersection.at2 same)
    (Intersection.at3 same)
    (Intersection.at4 same)
    (Intersection.at5 same)

------------------------------------------------------------------------
-- Neither fixed-space image is the other one.
------------------------------------------------------------------------

principalImageNotContainedInK0 :
  (k : K0.Bruhat3) → principalEmbed Principal.oldBasis1 ≡ k0Embed k → ⊥
principalImageNotContainedInK0 k eq =
  Intersection.principalBasis1NotK0Invariant k (sameCompactFromEmbedEquality eq)

k0ImageNotContainedInPrincipal :
  (p : Principal.Old3) → k0Embed Intersection.k0LeftBasis ≡ principalEmbed p → ⊥
k0ImageNotContainedInPrincipal p eq =
  Intersection.k0LeftBasisNotPrincipalInvariant p
    (sameCompactFromEmbedEquality (sym eq))

------------------------------------------------------------------------
-- The intersection is represented constructively by Common2.
------------------------------------------------------------------------

commonAmbient : Intersection.Common2 → CompactFunction6
commonAmbient c = principalEmbed (Intersection.principalCommon c)

commonAmbientAgreesWithK0 :
  (c : Intersection.Common2) →
  commonAmbient c ≡ k0Embed (Intersection.k0Common c)
commonAmbientAgreesWithK0 c =
  embedEqualityFromSameCompact (Intersection.commonSameCompactFunction c)

------------------------------------------------------------------------
-- Exact correction to the earlier comparison target.
------------------------------------------------------------------------

record P11Level44CommonLocalRepresentationBoundary : Set where
  field
    commonCompactAmbientConstructed : Bool
    principalFixedSpaceInjected : Bool
    k0FixedSpaceInjected : Bool
    principalImageEqualsK0Image : Bool
    intersectionCoordinates : Nat
    distinctFullAlignmentsFixingIntersectionConstructed : Bool
    canonicalFixedSpaceIsomorphismRequiredByJL : Bool
    commonRepresentationIsCorrectSameObjectTarget : Bool
    noncanonicalJLDisciplineRequired : Bool

canonicalP11Level44CommonLocalRepresentationBoundary :
  P11Level44CommonLocalRepresentationBoundary
canonicalP11Level44CommonLocalRepresentationBoundary = record
  { commonCompactAmbientConstructed = true
  ; principalFixedSpaceInjected = true
  ; k0FixedSpaceInjected = true
  ; principalImageEqualsK0Image = false
  ; intersectionCoordinates = 2
  ; distinctFullAlignmentsFixingIntersectionConstructed = true
  ; canonicalFixedSpaceIsomorphismRequiredByJL = false
  ; commonRepresentationIsCorrectSameObjectTarget = true
  ; noncanonicalJLDisciplineRequired = true
  }
