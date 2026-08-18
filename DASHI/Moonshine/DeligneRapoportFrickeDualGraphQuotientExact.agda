module DASHI.Moonshine.DeligneRapoportFrickeDualGraphQuotientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Pierre Deligne and Michael Rapoport,
-- "Les schemas de modules de courbes elliptiques",
-- Lecture Notes in Mathematics 349 (1973), 143--316.
-- DOI: 10.1007/978-3-540-37855-6_4.
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
--
-- DASHI CONTRIBUTION
--
-- Derive the resolved Fricke quotient DUAL GRAPH directly from the repository's
-- involution normal form rather than inserting its edge count independently.
--
-- Prequotient Deligne--Rapoport graph:
--   * two vertices C0,Cinf;
--   * one transverse edge for every supersingular intersection;
--   * Fricke swaps C0/Cinf and acts on edges by Frobenius.
--
-- Under the source quotient geometry:
--   * a Frobenius-fixed edge has its endpoints swapped and its singular image is
--     resolved, hence contributes NO quotient graph edge;
--   * a pair of exchanged edges contributes ONE self-loop after the two
--     component vertices are identified.
--
-- The resulting resolved quotient graph therefore has exactly one vertex and
-- Fin paired as its loop-edge carrier.  This file proves the finite orbit
-- bookkeeping and exact edge projection.  The algebraic-geometric assertion
-- that this is the actual dual graph of the quotient model remains the
-- same-object theorem supplied by Deligne--Rapoport/Ogg/Treneer geometry.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

PrequotientVertex : Set
PrequotientVertex = DR.DRComponent

prequotientVertexFricke : PrequotientVertex → PrequotientVertex
prequotientVertexFricke = DR.frickeComponent

PrequotientEdge : Nat → Nat → Set
PrequotientEdge fixed paired = Orbit.OrbitNormalFormCarrier fixed paired

prequotientEdgeFricke :
  ∀ {fixed paired} → PrequotientEdge fixed paired → PrequotientEdge fixed paired
prequotientEdgeFricke = Orbit.orbitInvolution

------------------------------------------------------------------------
-- Every prequotient supersingular edge connects the two components.
------------------------------------------------------------------------

edgeSource :
  ∀ {fixed paired} → PrequotientEdge fixed paired → PrequotientVertex
edgeSource edge = DR.component0

edgeTarget :
  ∀ {fixed paired} → PrequotientEdge fixed paired → PrequotientVertex
edgeTarget edge = DR.componentInfinity

frickeReversesEdgeEndpoints :
  ∀ {fixed paired} (edge : PrequotientEdge fixed paired) →
  prequotientVertexFricke (edgeSource edge)
    ≡ edgeTarget (prequotientEdgeFricke edge)
frickeReversesEdgeEndpoints edge = refl

frickeReversesEdgeEndpointsOther :
  ∀ {fixed paired} (edge : PrequotientEdge fixed paired) →
  prequotientVertexFricke (edgeTarget edge)
    ≡ edgeSource (prequotientEdgeFricke edge)
frickeReversesEdgeEndpointsOther edge = refl

------------------------------------------------------------------------
-- Resolved quotient graph.
------------------------------------------------------------------------

data QuotientVertex : Set where
  quotientComponent : QuotientVertex

QuotientEdge : Nat → Set
QuotientEdge paired = Fin paired

quotientEdgeSource : ∀ {paired} → QuotientEdge paired → QuotientVertex
quotientEdgeSource edge = quotientComponent

quotientEdgeTarget : ∀ {paired} → QuotientEdge paired → QuotientVertex
quotientEdgeTarget edge = quotientComponent

quotientEdgeIsLoop :
  ∀ {paired} (edge : QuotientEdge paired) →
  quotientEdgeSource edge ≡ quotientEdgeTarget edge
quotientEdgeIsLoop edge = refl

------------------------------------------------------------------------
-- Edge projection with resolution of fixed intersections.
--
-- fixed edge      -> nothing   (resolved smooth image)
-- paired edge i,b -> just i    (one loop per exchanged pair)
------------------------------------------------------------------------

resolvedQuotientEdge :
  ∀ {fixed paired} →
  PrequotientEdge fixed paired → Maybe (QuotientEdge paired)
resolvedQuotientEdge (inj₁ fixedIndex) = nothing
resolvedQuotientEdge (inj₂ (pairIndex , bit)) = just pairIndex

resolvedQuotientEdgeInvariant :
  ∀ {fixed paired} (edge : PrequotientEdge fixed paired) →
  resolvedQuotientEdge (prequotientEdgeFricke edge)
  ≡ resolvedQuotientEdge edge
resolvedQuotientEdgeInvariant (inj₁ fixedIndex) = refl
resolvedQuotientEdgeInvariant (inj₂ (pairIndex , Orbit.bit0)) = refl
resolvedQuotientEdgeInvariant (inj₂ (pairIndex , Orbit.bit1)) = refl

fixedIntersectionResolved :
  ∀ {fixed paired} (index : Fin fixed) →
  resolvedQuotientEdge {fixed} {paired} (inj₁ index) ≡ nothing
fixedIntersectionResolved index = refl

pairedIntersection0BecomesLoop :
  ∀ {fixed paired} (index : Fin paired) →
  resolvedQuotientEdge {fixed} {paired} (inj₂ (index , Orbit.bit0))
  ≡ just index
pairedIntersection0BecomesLoop index = refl

pairedIntersection1BecomesSameLoop :
  ∀ {fixed paired} (index : Fin paired) →
  resolvedQuotientEdge {fixed} {paired} (inj₂ (index , Orbit.bit1))
  ≡ just index
pairedIntersection1BecomesSameLoop index = refl

pairedIntersectionsBecomeSameLoop :
  ∀ {fixed paired} (index : Fin paired) →
  resolvedQuotientEdge {fixed} {paired} (inj₂ (index , Orbit.bit0))
  ≡ resolvedQuotientEdge {fixed} {paired} (inj₂ (index , Orbit.bit1))
pairedIntersectionsBecomeSameLoop index = refl

------------------------------------------------------------------------
-- Explicit quotient-edge section.  Every quotient loop comes from a paired
-- prequotient edge, so no target loop is invented by the graph projection.
------------------------------------------------------------------------

quotientEdgeSection :
  ∀ {fixed paired} → QuotientEdge paired → PrequotientEdge fixed paired
quotientEdgeSection index = inj₂ (index , Orbit.bit0)

resolvedAfterSection :
  ∀ {fixed paired} (index : QuotientEdge paired) →
  resolvedQuotientEdge (quotientEdgeSection {fixed} index) ≡ just index
resolvedAfterSection index = refl

------------------------------------------------------------------------
-- The target graph carrier itself records the exact quotient counts.
------------------------------------------------------------------------

resolvedQuotientVertexCount : Nat
resolvedQuotientVertexCount = 1

resolvedQuotientEdgeCount : Nat → Nat
resolvedQuotientEdgeCount paired = paired

record DeligneRapoportFrickeDualGraphQuotientBoundary : Set where
  field
    twoPrequotientComponentsConstructed : Bool
    frickeEndpointSwapConstructed : Bool
    fixedIntersectionsResolvedInProjection : Bool
    pairedIntersectionsMapToOneLoop : Bool
    quotientLoopSectionConstructed : Bool
    actualSchemeDualGraphIdentifiedHere : Bool

canonicalDeligneRapoportFrickeDualGraphQuotientBoundary :
  DeligneRapoportFrickeDualGraphQuotientBoundary
canonicalDeligneRapoportFrickeDualGraphQuotientBoundary = record
  { twoPrequotientComponentsConstructed = true
  ; frickeEndpointSwapConstructed = true
  ; fixedIntersectionsResolvedInProjection = true
  ; pairedIntersectionsMapToOneLoop = true
  ; quotientLoopSectionConstructed = true
  ; actualSchemeDualGraphIdentifiedHere = false
  }
