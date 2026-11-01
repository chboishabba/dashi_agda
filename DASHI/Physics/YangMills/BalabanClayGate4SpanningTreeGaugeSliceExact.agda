module DASHI.Physics.YangMills.BalabanClayGate4SpanningTreeGaugeSliceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond

------------------------------------------------------------------------
-- Exact spanning-tree gauge slice and reconstruction.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press; open-access
-- reissue (2022). DOI: 10.1017/9781009290395.
--
-- DASHI's bond convention is
--
--   U^g(x,y) = g(x) U(x,y) g(y)^{-1}.
--
-- Therefore, when T(x) is the root-to-x tree holonomy satisfying
-- T(child) = T(parent) U(parent,child), the canonical tree gauge is g(x)=T(x)
-- (not its inverse).  Every tree edge then becomes the identity.  The module
-- proves this, proves uniqueness among rooted gauges fixing every tree edge,
-- and proves exact reconstruction of every original edge from its gauge-fixed
-- coordinate and the vertex transports.
------------------------------------------------------------------------

record RootedTreeTransport
    (Vertex Edge Group : Set)
    (group : Bond.ExactLinkGroup Group) : Set₁ where
  field
    root : Vertex
    parent child : Edge → Vertex
    edgeValue : Edge → Group

    rootToVertexTransport : Vertex → Group

    rootTransportIdentity :
      rootToVertexTransport root ≡ Bond.identity group

    childTransportExtension : ∀ edge →
      rootToVertexTransport (child edge)
      ≡ Bond.multiply group
          (rootToVertexTransport (parent edge))
          (edgeValue edge)

    TreeInduction :
      (Property : Vertex → Set) →
      Property root →
      (∀ edge → Property (parent edge) → Property (child edge)) →
      ∀ vertex → Property vertex

open RootedTreeTransport public

canonicalTreeGauge :
  ∀ {Vertex Edge Group} {group : Bond.ExactLinkGroup Group} →
  RootedTreeTransport Vertex Edge Group group →
  Vertex → Group
canonicalTreeGauge = rootToVertexTransport

gaugeTransformEdge :
  ∀ {Vertex Edge Group} {group : Bond.ExactLinkGroup Group} →
  RootedTreeTransport Vertex Edge Group group →
  (Vertex → Group) → Edge → Group
gaugeTransformEdge {group = group} tree gauge edge =
  Bond.multiply group
    (Bond.multiply group
      (gauge (parent tree edge))
      (edgeValue tree edge))
    (Bond.inverse group (gauge (child tree edge)))

canonicalGaugeFixesTreeEdge :
  ∀ {Vertex Edge Group} {group : Bond.ExactLinkGroup Group}
    (tree : RootedTreeTransport Vertex Edge Group group)
    edge →
  gaugeTransformEdge tree (canonicalTreeGauge tree) edge
  ≡ Bond.identity group
canonicalGaugeFixesTreeEdge {group = group} tree edge
  rewrite childTransportExtension tree edge =
  Bond.inverseRight group
    (Bond.multiply group
      (rootToVertexTransport tree (parent tree edge))
      (edgeValue tree edge))

canonicalGaugeAnchoredAtRoot :
  ∀ {Vertex Edge Group} {group : Bond.ExactLinkGroup Group}
    (tree : RootedTreeTransport Vertex Edge Group group) →
  canonicalTreeGauge tree (root tree) ≡ Bond.identity group
canonicalGaugeAnchoredAtRoot = rootTransportIdentity

record RootAnchoredTreeGauge
    {Vertex Edge Group : Set}
    {group : Bond.ExactLinkGroup Group}
    (tree : RootedTreeTransport Vertex Edge Group group) : Set₁ where
  field
    gauge : Vertex → Group
    rootAnchored : gauge (root tree) ≡ Bond.identity group
    fixesTreeEdge : ∀ edge →
      gaugeTransformEdge tree gauge edge ≡ Bond.identity group

open RootAnchoredTreeGauge public

fixedEdgeDeterminesChildGauge :
  ∀ {Vertex Edge Group} {group : Bond.ExactLinkGroup Group}
    {tree : RootedTreeTransport Vertex Edge Group group}
    (selected : RootAnchoredTreeGauge tree)
    edge →
  gauge selected (child tree edge)
  ≡ Bond.multiply group
      (gauge selected (parent tree edge))
      (edgeValue tree edge)
fixedEdgeDeterminesChildGauge {Vertex} {Edge} {Group} {group = group} {tree = tree}
    selected edge =
  sym
    (trans
      (sym (Bond.identityRight group edgePrefix))
      (trans
        (cong (Bond.multiply group edgePrefix)
          (sym (Bond.inverseLeft group childGauge)))
        (trans
          (sym (Bond.multiplyAssociative group
            edgePrefix
            (Bond.inverse group childGauge)
            childGauge))
          (trans
            (cong (λ left → Bond.multiply group left childGauge)
              (fixesTreeEdge selected edge))
            (Bond.identityLeft group childGauge)))))
  where
  edgePrefix : Group
  edgePrefix = Bond.multiply group
    (gauge selected (parent tree edge))
    (edgeValue tree edge)

  childGauge : Group
  childGauge = gauge selected (child tree edge)

canonicalTreeGaugeUnique :
  ∀ {Vertex Edge Group} {group : Bond.ExactLinkGroup Group}
    {tree : RootedTreeTransport Vertex Edge Group group}
    (selected : RootAnchoredTreeGauge tree)
    vertex →
  gauge selected vertex ≡ canonicalTreeGauge tree vertex
canonicalTreeGaugeUnique {group = group} {tree = tree} selected =
  TreeInduction tree
    (λ vertex → gauge selected vertex ≡ canonicalTreeGauge tree vertex)
    (trans
      (rootAnchored selected)
      (sym (rootTransportIdentity tree)))
    (λ edge parentEquality →
      trans
        (fixedEdgeDeterminesChildGauge selected edge)
        (trans
          (cong
            (λ parentGauge → Bond.multiply group parentGauge
              (edgeValue tree edge))
            parentEquality)
          (sym (childTransportExtension tree edge))))

canonicalRootAnchoredGauge :
  ∀ {Vertex Edge Group} {group : Bond.ExactLinkGroup Group}
    (tree : RootedTreeTransport Vertex Edge Group group) →
  RootAnchoredTreeGauge tree
canonicalRootAnchoredGauge tree = record
  { gauge = canonicalTreeGauge tree
  ; rootAnchored = canonicalGaugeAnchoredAtRoot tree
  ; fixesTreeEdge = canonicalGaugeFixesTreeEdge tree
  }

canonicalGaugeFixedCoordinate :
  ∀ {Vertex Edge Group} {group : Bond.ExactLinkGroup Group} →
  RootedTreeTransport Vertex Edge Group group → Edge → Group
canonicalGaugeFixedCoordinate tree =
  gaugeTransformEdge tree (canonicalTreeGauge tree)

reconstructOriginalEdge :
  ∀ {Vertex Edge Group} {group : Bond.ExactLinkGroup Group} →
  RootedTreeTransport Vertex Edge Group group → Edge → Group
reconstructOriginalEdge {group = group} tree edge =
  Bond.multiply group
    (Bond.multiply group
      (Bond.inverse group
        (canonicalTreeGauge tree (parent tree edge)))
      (canonicalGaugeFixedCoordinate tree edge))
    (canonicalTreeGauge tree (child tree edge))

canonicalCoordinateReconstructsOriginalEdge :
  ∀ {Vertex Edge Group} {group : Bond.ExactLinkGroup Group}
    (tree : RootedTreeTransport Vertex Edge Group group)
    edge →
  reconstructOriginalEdge tree edge ≡ edgeValue tree edge
canonicalCoordinateReconstructsOriginalEdge {group = group} tree edge =
  trans
    (cong
      (λ left → Bond.multiply group left
        (canonicalTreeGauge tree (child tree edge)))
      (Bond.cancelMiddleGauge group
        (canonicalTreeGauge tree (parent tree edge))
        (edgeValue tree edge)
        (canonicalTreeGauge tree (child tree edge))))
    (trans
      (Bond.multiplyAssociative group
        (edgeValue tree edge)
        (Bond.inverse group
          (canonicalTreeGauge tree (child tree edge)))
        (canonicalTreeGauge tree (child tree edge)))
      (trans
        (cong (Bond.multiply group (edgeValue tree edge))
          (Bond.inverseLeft group
            (canonicalTreeGauge tree (child tree edge))))
        (Bond.identityRight group (edgeValue tree edge))))

spanningTreeCanonicalGaugeConstructionLevel : ProofLevel
spanningTreeCanonicalGaugeConstructionLevel = computed

spanningTreeEdgeGaugeFixingLevel : ProofLevel
spanningTreeEdgeGaugeFixingLevel = machineChecked

spanningTreeRootAnchoredUniquenessLevel : ProofLevel
spanningTreeRootAnchoredUniquenessLevel = machineChecked

spanningTreeCoordinateReconstructionLevel : ProofLevel
spanningTreeCoordinateReconstructionLevel = machineChecked

physicalPeriodicTreeInductionInputsLevel : ProofLevel
physicalPeriodicTreeInductionInputsLevel = conditional

physicalTreeTransportFromBondFieldInputsLevel : ProofLevel
physicalTreeTransportFromBondFieldInputsLevel = conditional

physicalBalabanSliceTransitionInputsLevel : ProofLevel
physicalBalabanSliceTransitionInputsLevel = conditional
