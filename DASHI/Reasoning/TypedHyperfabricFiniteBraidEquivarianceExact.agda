module DASHI.Reasoning.TypedHyperfabricFiniteBraidEquivarianceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Topology.FiniteBraidRhizomeCalculus as Braid

------------------------------------------------------------------------
-- FINITE BRAID -> TYPED HYPERFABRIC EQUIVARIANCE
--
-- FiniteBraidRhizomeCalculus owns the actual two-strand braid action,
-- inverses and finite isotopy classification.  A TypedHyperfabric does not
-- automatically inherit that action.  To transport a braid through a fabric,
-- a domain must provide:
--
--   * actions on vertices and edges;
--   * invertible maps on vertex/edge stalks;
--   * transport of incidences;
--   * a commuting restriction square.
--
-- Section transport is retained as a separate witness because an ordered
-- action/history trace alone does not manufacture a physical braid action.
------------------------------------------------------------------------

record Iso (A B : Set) : Set where
  constructor iso
  field
    to : A → B
    from : B → A
    fromTo : ∀ x → from (to x) ≡ x
    toFrom : ∀ y → to (from y) ≡ y

open Iso public

identityIso : ∀ {A : Set} → Iso A A
identityIso = iso (λ x → x) (λ x → x) (λ _ → refl) (λ _ → refl)

record TypedHyperfabricBraidEquivariance
    {Vertex Edge : Set}
    (fabric : Hyperfabric.TypedHyperfabric Vertex Edge) : Set₁ where
  constructor typed-hyperfabric-braid-equivariance
  field
    actVertex : Braid.Braid2 → Vertex → Vertex
    actEdge : Braid.Braid2 → Edge → Edge

    vertexStraight : ∀ vertex → actVertex Braid.straight vertex ≡ vertex
    edgeStraight : ∀ edge → actEdge Braid.straight edge ≡ edge

    vertexCompose :
      ∀ left right vertex →
      actVertex (Braid.compose left right) vertex
      ≡ actVertex left (actVertex right vertex)
    edgeCompose :
      ∀ left right edge →
      actEdge (Braid.compose left right) edge
      ≡ actEdge left (actEdge right edge)

    vertexStalkIso :
      (braid : Braid.Braid2) →
      (vertex : Vertex) →
      Iso
        (Hyperfabric.vertexStalk fabric vertex)
        (Hyperfabric.vertexStalk fabric (actVertex braid vertex))

    edgeStalkIso :
      (braid : Braid.Braid2) →
      (edge : Edge) →
      Iso
        (Hyperfabric.edgeStalk fabric edge)
        (Hyperfabric.edgeStalk fabric (actEdge braid edge))

    actIncidence :
      (braid : Braid.Braid2) →
      ∀ {vertex edge} →
      Hyperfabric.incidence fabric vertex edge →
      Hyperfabric.incidence fabric
        (actVertex braid vertex)
        (actEdge braid edge)

    restrictionEquivariant :
      (braid : Braid.Braid2) →
      ∀ {vertex edge}
        (membership : Hyperfabric.incidence fabric vertex edge)
        (value : Hyperfabric.vertexStalk fabric vertex) →
      Hyperfabric.restrict fabric
        (actIncidence braid membership)
        (Iso.to (vertexStalkIso braid vertex) value)
      ≡
      Iso.to (edgeStalkIso braid edge)
        (Hyperfabric.restrict fabric membership value)

open TypedHyperfabricBraidEquivariance public

record TypedHyperfabricBraidSectionTransport
    {Vertex Edge : Set}
    {fabric : Hyperfabric.TypedHyperfabric Vertex Edge}
    (action : TypedHyperfabricBraidEquivariance fabric) : Set₁ where
  constructor typed-hyperfabric-braid-section-transport
  field
    transportSection :
      Braid.Braid2 →
      Hyperfabric.GlobalSection fabric →
      Hyperfabric.GlobalSection fabric

    vertexTransportAgrees :
      ∀ braid section vertex →
      Iso.to (vertexStalkIso action braid vertex)
        (Hyperfabric.vertexValue section vertex)
      ≡
      Hyperfabric.vertexValue
        (transportSection braid section)
        (actVertex action braid vertex)

    edgeTransportAgrees :
      ∀ braid section edge →
      Iso.to (edgeStalkIso action braid edge)
        (Hyperfabric.edgeValue section edge)
      ≡
      Hyperfabric.edgeValue
        (transportSection braid section)
        (actEdge action braid edge)

open TypedHyperfabricBraidSectionTransport public

------------------------------------------------------------------------
-- Exact finite two-strand specimen.
--
-- This is not a theorem that every hyperfabric admits a braid action.  It is a
-- concrete witness that the canonical Braid2 action can act on a genuine
-- TypedHyperfabric while preserving incidence/restriction compatibility and
-- transporting compatible GlobalSections.
------------------------------------------------------------------------

data StrandIncidence : Braid.Strand → Braid.Strand → Set where
  leftOnLeft : StrandIncidence Braid.leftStrand Braid.leftStrand
  rightOnRight : StrandIncidence Braid.rightStrand Braid.rightStrand

strandFabric : Hyperfabric.TypedHyperfabric Braid.Strand Braid.Strand
strandFabric = record
  { vertexStalk = λ _ → Bool
  ; edgeStalk = λ _ → Bool
  ; incidence = StrandIncidence
  ; restrict = λ _ value → value
  ; edgeProvenance = λ _ → "FiniteBraidRhizomeCalculus two-strand specimen" ∷ []
  ; edgeSalience = λ _ → 1
  ; fabricLabel = "two-strand finite braid TypedHyperfabric specimen"
  }

actStrandIncidence :
  (braid : Braid.Braid2) →
  ∀ {vertex edge} →
  StrandIncidence vertex edge →
  StrandIncidence (Braid.act braid vertex) (Braid.act braid edge)
actStrandIncidence Braid.straight leftOnLeft = leftOnLeft
actStrandIncidence Braid.straight rightOnRight = rightOnRight
actStrandIncidence Braid.swap leftOnLeft = rightOnRight
actStrandIncidence Braid.swap rightOnRight = leftOnLeft

strandVertexCompose :
  ∀ left right vertex →
  Braid.act (Braid.compose left right) vertex
  ≡ Braid.act left (Braid.act right vertex)
strandVertexCompose Braid.straight Braid.straight Braid.leftStrand = refl
strandVertexCompose Braid.straight Braid.straight Braid.rightStrand = refl
strandVertexCompose Braid.straight Braid.swap Braid.leftStrand = refl
strandVertexCompose Braid.straight Braid.swap Braid.rightStrand = refl
strandVertexCompose Braid.swap Braid.straight Braid.leftStrand = refl
strandVertexCompose Braid.swap Braid.straight Braid.rightStrand = refl
strandVertexCompose Braid.swap Braid.swap Braid.leftStrand = refl
strandVertexCompose Braid.swap Braid.swap Braid.rightStrand = refl

strandBraidEquivariance : TypedHyperfabricBraidEquivariance strandFabric
strandBraidEquivariance = typed-hyperfabric-braid-equivariance
  Braid.act
  Braid.act
  (λ _ → refl)
  (λ _ → refl)
  strandVertexCompose
  strandVertexCompose
  (λ _ _ → identityIso)
  (λ _ _ → identityIso)
  actStrandIncidence
  (λ _ _ _ → refl)

swapSection :
  Hyperfabric.GlobalSection strandFabric →
  Hyperfabric.GlobalSection strandFabric
swapSection section = record
  { vertexValue = λ
      { Braid.leftStrand → Hyperfabric.vertexValue section Braid.rightStrand
      ; Braid.rightStrand → Hyperfabric.vertexValue section Braid.leftStrand
      }
  ; edgeValue = λ
      { Braid.leftStrand → Hyperfabric.edgeValue section Braid.rightStrand
      ; Braid.rightStrand → Hyperfabric.edgeValue section Braid.leftStrand
      }
  ; compatible = λ
      { leftOnLeft → Hyperfabric.compatible section rightOnRight
      ; rightOnRight → Hyperfabric.compatible section leftOnLeft
      }
  ; sectionReceipt = "finite Braid2 swap transported compatible section"
  }

transportStrandSection :
  Braid.Braid2 →
  Hyperfabric.GlobalSection strandFabric →
  Hyperfabric.GlobalSection strandFabric
transportStrandSection Braid.straight section = section
transportStrandSection Braid.swap section = swapSection section

strandVertexTransportAgrees :
  ∀ braid section vertex →
  Iso.to (vertexStalkIso strandBraidEquivariance braid vertex)
    (Hyperfabric.vertexValue section vertex)
  ≡
  Hyperfabric.vertexValue
    (transportStrandSection braid section)
    (actVertex strandBraidEquivariance braid vertex)
strandVertexTransportAgrees Braid.straight section Braid.leftStrand = refl
strandVertexTransportAgrees Braid.straight section Braid.rightStrand = refl
strandVertexTransportAgrees Braid.swap section Braid.leftStrand = refl
strandVertexTransportAgrees Braid.swap section Braid.rightStrand = refl

strandEdgeTransportAgrees :
  ∀ braid section edge →
  Iso.to (edgeStalkIso strandBraidEquivariance braid edge)
    (Hyperfabric.edgeValue section edge)
  ≡
  Hyperfabric.edgeValue
    (transportStrandSection braid section)
    (actEdge strandBraidEquivariance braid edge)
strandEdgeTransportAgrees Braid.straight section Braid.leftStrand = refl
strandEdgeTransportAgrees Braid.straight section Braid.rightStrand = refl
strandEdgeTransportAgrees Braid.swap section Braid.leftStrand = refl
strandEdgeTransportAgrees Braid.swap section Braid.rightStrand = refl

strandSectionTransport :
  TypedHyperfabricBraidSectionTransport strandBraidEquivariance
strandSectionTransport = typed-hyperfabric-braid-section-transport
  transportStrandSection
  strandVertexTransportAgrees
  strandEdgeTransportAgrees

------------------------------------------------------------------------
-- Authority / promotion boundary.
------------------------------------------------------------------------

record TypedHyperfabricFiniteBraidBoundary : Set where
  constructor typed-hyperfabric-finite-braid-boundary
  field
    finiteBraidRhizomeOwnsBraidAction : Bool
    restrictionEquivarianceRequired : Bool
    sectionTransportWitnessRequired : Bool
    finiteTwoStrandSectionTransportConstructed : Bool

    actionTraceAlonePaysHyperfabricBraidTransport : Bool
    actionTraceAlonePaysHyperfabricBraidTransportIsFalse :
      actionTraceAlonePaysHyperfabricBraidTransport ≡ false

    arbitraryTypedHyperfabricAutomaticallyBraidEquivariant : Bool
    arbitraryTypedHyperfabricAutomaticallyBraidEquivariantIsFalse :
      arbitraryTypedHyperfabricAutomaticallyBraidEquivariant ≡ false

    braidEquivarianceAutomaticallyAuthorizesConsumerQuotient : Bool
    braidEquivarianceAutomaticallyAuthorizesConsumerQuotientIsFalse :
      braidEquivarianceAutomaticallyAuthorizesConsumerQuotient ≡ false

    interpretation : String

open TypedHyperfabricFiniteBraidBoundary public

canonicalTypedHyperfabricFiniteBraidBoundary :
  TypedHyperfabricFiniteBraidBoundary
canonicalTypedHyperfabricFiniteBraidBoundary =
  typed-hyperfabric-finite-braid-boundary
    true
    true
    true
    true
    false refl
    false refl
    false refl
    "FiniteBraidRhizomeCalculus owns Braid2 deformation/action. A TypedHyperfabric admits that deformation only after explicit vertex/edge actions, invertible stalk maps, incidence transport and restriction equivariance are supplied. Section transport is an additional witness. Ordered action traces retain provenance/history but do not by themselves pay this physical equivariance obligation, and braid equivariance does not create consumer quotient authority."
