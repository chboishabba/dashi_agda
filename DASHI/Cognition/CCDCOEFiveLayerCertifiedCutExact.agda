module DASHI.Cognition.CCDCOEFiveLayerCertifiedCutExact where

-- Finite instance of the generic multiplex path theorem.
-- Nonoperational: no human networks, adversary inference or causal claims.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Cognition.CCDCOEMultiplexGraphCutCoreExact as G
import DASHI.Cognition.CCDCOECognitiveMultiplexInvariantExact as C

open G using (node)

data FullCross :
  C.InvariantLayer → C.InvariantLayer →
  C.Actor → C.Actor → Set where
  epToAx : (a : C.Actor) →
    FullCross C.epistemic C.axiological a a
  axToId : (a : C.Actor) →
    FullCross C.axiological C.identificatory a a
  idToSocial : (a : C.Actor) →
    FullCross C.identificatory C.social a a
  socialToTel : (a : C.Actor) →
    FullCross C.social C.teleological a a

data CutCross :
  C.InvariantLayer → C.InvariantLayer →
  C.Actor → C.Actor → Set where
  cutEpToAx : (a : C.Actor) →
    CutCross C.epistemic C.axiological a a
  cutAxToId : (a : C.Actor) →
    CutCross C.axiological C.identificatory a a
  cutSocialToTel : (a : C.Actor) →
    CutCross C.social C.teleological a a

fullNetwork : G.Multiplex C.Actor C.InvariantLayer
fullNetwork = record
  { G.Multiplex.within = λ _ _ _ → ⊤
  ; G.Multiplex.between = FullCross
  }

cutNetwork : G.Multiplex C.Actor C.InvariantLayer
cutNetwork = record
  { G.Multiplex.within = λ _ _ _ → ⊤
  ; G.Multiplex.between = CutCross
  }

-- Everyone remains in every layer, with complete local links, while
-- an interlayer separator splits the five-layer dependency chain.
side : G.LayerNode C.Actor C.InvariantLayer → Bool
side (node _ C.epistemic) = true
side (node _ C.axiological) = true
side (node _ C.identificatory) = true
side (node _ C.social) = false
side (node _ C.teleological) = false

-- Exhaustive constructor cases: a proof that NO retained link crosses
-- the identified partition, not merely that a named path is missing.
cutEdgePreservesSide :
  ∀ {u v} → G.NetworkEdge cutNetwork u v →
  side u ≡ side v
cutEdgePreservesSide (G.local localEvidence) = refl
cutEdgePreservesSide (G.cross (cutEpToAx _)) = refl
cutEdgePreservesSide (G.cross (cutAxToId _)) = refl
cutEdgePreservesSide (G.cross (cutSocialToTel _)) = refl

-- This is a genuinely global no-walk result for the declared cut network.
-- It includes arbitrary cross-actor travel inside each layer.
noCrossCutWalk :
  (a b : C.Actor) →
  G.Walk (G.NetworkEdge cutNetwork)
    (node a C.epistemic) (node b C.teleological) →
  G.Void
noCrossCutWalk a b =
  G.noWalkAcrossCertifiedCut
    (G.NetworkEdge cutNetwork)
    side
    cutEdgePreservesSide
    refl refl

-- Intact graph has a constructive route through all five layers.
fullSpanningWalk :
  (a : C.Actor) →
  G.Walk (G.NetworkEdge fullNetwork)
    (node a C.epistemic) (node a C.teleological)
fullSpanningWalk a =
  G.advance (G.cross (epToAx a))
    (G.advance (G.cross (axToId a))
      (G.advance (G.cross (idToSocial a))
        (G.advance (G.cross (socialToTel a)) G.halt)))

fullRouteIsConcatenable :
  (a : C.Actor) →
  G.Walk (G.NetworkEdge fullNetwork)
    (node a C.epistemic) (node a C.teleological)
fullRouteIsConcatenable a =
  G.appendWalk
    (G.advance (G.cross (epToAx a)) G.halt)
    (G.advance (G.cross (axToId a))
      (G.advance (G.cross (idToSocial a))
        (G.advance (G.cross (socialToTel a)) G.halt)))

-- Exactly the same within-layer edge types occur in both architectures.
localLinkSurvivesCut :
  (l : C.InvariantLayer) (a b : C.Actor) →
  G.NetworkEdge cutNetwork (node a l) (node b l)
localLinkSurvivesCut l a b = G.local tt

-- Their structural coexistence does not license any historical, military,
-- clinical, political, individual or causal inference.
