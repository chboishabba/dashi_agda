module DASHI.Education.DigitalESDHigherOrderFabricIncidenceExact where

------------------------------------------------------------------------
-- DIGITAL ESD: TYPED INCIDENCE OF THE ACTUAL PART/AXIS WORLD
--
-- Source owners:
-- TypedHyperfabricCore: Duta et al., "Sheaf Hypergraph Networks",
-- arXiv:2309.17116; source-derived structural precedent only.
-- Crenshaw 1991, DOI 10.2307/1229039, intersectional framing;
-- non-factorability is the separate DASHI construction.
-- All scholarly source claims remain with the cited source authors.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List)
open import Data.List.Membership.Propositional using (_∈_)

import DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact as World
import DASHI.Education.DigitalESDIntersectionalRecompositionExact as Recompose
import DASHI.Reasoning.TypedHyperfabricCore as Hyper

-- XI00: the original HigherOrderStudyRelation has List participants/axes,
-- which permits empty lists. A usable incidence requires a real part and
-- a real axis with explicit membership, not a decorative relation label.
record HigherOrderFabricIncidence
  (scope : World.StudyWorldScope)
  (Vertex Edge Scalar : Set) : Set₂ where
  constructor higher-order-fabric-incidence
  field
    projection : World.ResearchFabricProjection scope Vertex Edge
    relation : World.HigherOrderStudyRelation scope Scalar

    anchorPart : World.StudyPart scope
    anchorPartInRelation :
      anchorPart ∈ World.HigherOrderStudyRelation.participatingStudyParts relation
    anchorAxis : World.Axis scope
    anchorAxisInRelation :
      anchorAxis ∈ World.HigherOrderStudyRelation.activeAxisReferences relation

    edge : Edge
    edgeProvenanceExact :
      Hyper.edgeProvenance (World.ResearchFabricProjection.fabric projection) edge ≡
      World.HigherOrderStudyRelation.relationshipProvenance relation

    everyParticipantIsIncident :
      (part : World.StudyPart scope) →
      part ∈ World.HigherOrderStudyRelation.participatingStudyParts relation →
      Hyper.incidence
        (World.ResearchFabricProjection.fabric projection)
        (World.ResearchFabricProjection.locatePart projection part)
        edge

    axisFaithful :
      Recompose.AxisFaithfulStalk
        scope (World.ResearchFabricProjection.world projection)
        Vertex Edge
        (World.ResearchFabricProjection.fabric projection)
        (World.ResearchFabricProjection.locatePart projection)

open HigherOrderFabricIncidence public

-- XI01: the actual source-part/axis accounting is exactly retrievable at
-- the vertex incident to a claimed higher-order relation.
incidenceRetainsActualAxis :
  (scope : World.StudyWorldScope) →
  (Vertex Edge Scalar : Set) →
  (inc : HigherOrderFabricIncidence scope Vertex Edge Scalar) →
  (part : World.StudyPart scope) →
  (axis : World.Axis scope) →
  Recompose.decodePartAxes (axisFaithful inc)
    part
    (Recompose.actualPartStalk (axisFaithful inc) part)
    axis
  ≡ World.accounting (World.ResearchFabricProjection.world (projection inc))
      (World.study part) (World.part part) axis
incidenceRetainsActualAxis scope Vertex Edge Scalar inc part axis =
  Recompose.actualPartAgreesWithWorld (axisFaithful inc) part axis

-- XI02: admission to a *reviewed evidence-bearing higher-order relation*
-- requires a reviewed source-specific observation at each SELECTED
-- participant/axis address, in the exact same accounted research world.
-- Candidate or gap-pointer interactions deliberately use XI00 instead.
record ReviewedAxisInWorld
  (scope : World.StudyWorldScope)
  (world : World.AccountedStudyWorld scope)
  (part : World.StudyPart scope)
  (axis : World.Axis scope) : Set₁ where
  constructor reviewed-axis-in-world
  field
    sourceReviewed :
      World.ReviewedPartAxisEvidence scope
        (World.study part) (World.part part) axis
    worldActuallyUsesReviewedWitness :
      World.accounting world
        (World.study part) (World.part part) axis
      ≡ World.directReviewed sourceReviewed

open ReviewedAxisInWorld public

record ReviewedHigherOrderFabricIncidence
  (scope : World.StudyWorldScope)
  (Vertex Edge Scalar : Set) : Set₂ where
  constructor reviewed-higher-order-fabric-incidence
  field
    underlying : HigherOrderFabricIncidence scope Vertex Edge Scalar
    eachSelectedPartAxisReviewed :
      (part : World.StudyPart scope) →
      part ∈ World.HigherOrderStudyRelation.participatingStudyParts
        (relation underlying) →
      (axis : World.Axis scope) →
      axis ∈ World.HigherOrderStudyRelation.activeAxisReferences
        (relation underlying) →
      ReviewedAxisInWorld scope
        (World.ResearchFabricProjection.world (projection underlying))
        part axis

open ReviewedHigherOrderFabricIncidence public

-- XI03: a compatible local section is a proof about the exact edge and
-- ALL its declared incident parts. Do not claim this from a string receipt,
-- matching labels or source-genealogy counts.
record CompatibleLocalHigherEdge
  (scope : World.StudyWorldScope)
  (Vertex Edge Scalar : Set) : Set₂ where
  constructor compatible-local-higher-edge
  field
    incidenceWitness : HigherOrderFabricIncidence scope Vertex Edge Scalar
    edgeValue :
      Hyper.edgeStalk
        (World.ResearchFabricProjection.fabric (projection incidenceWitness))
        (edge incidenceWitness)
    eachIncidentRestrictionAgrees :
      (part : World.StudyPart scope) →
      (membership : part ∈
        World.HigherOrderStudyRelation.participatingStudyParts
          (relation incidenceWitness)) →
      Hyper.restrict
        (World.ResearchFabricProjection.fabric (projection incidenceWitness))
        (everyParticipantIsIncident incidenceWitness part membership)
        (Recompose.actualPartStalk (axisFaithful incidenceWitness) part)
      ≡ edgeValue

open CompatibleLocalHigherEdge public

-- XI04: the type retains the actual compatibility witness when available;
-- disagreement may instead stay an unresolved HyperfabricObstruction.
localEdgeCompatibilityAt :
  (scope : World.StudyWorldScope) →
  (Vertex Edge Scalar : Set) →
  (cert : CompatibleLocalHigherEdge scope Vertex Edge Scalar) →
  (part : World.StudyPart scope) →
  (member : part ∈ World.HigherOrderStudyRelation.participatingStudyParts
    (relation (incidenceWitness cert))) →
  Hyper.restrict
    (World.ResearchFabricProjection.fabric (projection (incidenceWitness cert)))
    (everyParticipantIsIncident (incidenceWitness cert) part member)
    (Recompose.actualPartStalk (axisFaithful (incidenceWitness cert)) part)
  ≡ edgeValue cert
localEdgeCompatibilityAt scope Vertex Edge Scalar cert part member =
  eachIncidentRestrictionAgrees cert part member
