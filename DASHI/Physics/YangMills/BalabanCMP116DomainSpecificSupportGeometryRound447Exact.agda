{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116DomainSpecificSupportGeometryRound447Exact where

------------------------------------------------------------------------
-- B / ROUND447: DOMAIN-INDEXED TWO-MARK SUPPORT GEOMETRY.
--
-- CMP116 (1.29) decays with d_k(Y), which varies with the localization domain Y.
-- The older R416 convenience carrier sets every domain distance to the single
-- global ymTreeEdgeCount; that is too coarse for a literal source attachment.
--
-- This owner keeps the selected support distance fixed but makes the connecting
-- tree depth domain-indexed.  It is the correct geometry consumed by the
-- source-native rate split:
--
--   d_selected <= d_Y.
--
-- No counting theorem is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411

record DomainSpecificTwoMarkSupportGeometry
    (Domain Term : Set) : Set₁ where
  field
    leftMark rightMark : Support.Link

    domainTreeDistance : Domain → Nat

    containsSelectedLink : Domain → Support.Link → Set
    selectedDifferentiatedTermSurvives : Domain → Term → Set

    survivingTermContainsLeftMark :
      ∀ domain term →
      selectedDifferentiatedTermSurvives domain term →
      containsSelectedLink domain leftMark

    survivingTermContainsRightMark :
      ∀ domain term →
      selectedDifferentiatedTermSurvives domain term →
      containsSelectedLink domain rightMark

    -- Literal connected-core/tree geometry.  This is where the source Y_0
    -- connected component and its chosen spanning tree meet the physical source
    -- supports.  It is domain-specific; no global edge count is substituted.
    connectedDomainTreeDominatesSupportGraphDistance :
      ∀ domain →
      containsSelectedLink domain leftMark →
      containsSelectedLink domain rightMark →
      Graph.ymGraphDist leftMark rightMark
        Nat.≤ domainTreeDistance domain

open DomainSpecificTwoMarkSupportGeometry public

domainConnectsBothSelectedMarks :
  ∀ {Domain Term} →
  DomainSpecificTwoMarkSupportGeometry Domain Term →
  Domain → Set
domainConnectsBothSelectedMarks geometry domain =
  containsSelectedLink geometry domain (leftMark geometry)
  ×
  containsSelectedLink geometry domain (rightMark geometry)

survivingTermForcesConnection :
  ∀ {Domain Term}
    (geometry : DomainSpecificTwoMarkSupportGeometry Domain Term)
    domain term →
  selectedDifferentiatedTermSurvives geometry domain term →
  domainConnectsBothSelectedMarks geometry domain
survivingTermForcesConnection geometry domain term survives =
  survivingTermContainsLeftMark geometry domain term survives ,
  survivingTermContainsRightMark geometry domain term survives

selectedDistanceBelowDomainTreeDistance :
  ∀ {Domain Term}
    (geometry : DomainSpecificTwoMarkSupportGeometry Domain Term)
    domain →
  domainConnectsBothSelectedMarks geometry domain →
  Graph.ymGraphDist (leftMark geometry) (rightMark geometry)
    Nat.≤ domainTreeDistance geometry domain
selectedDistanceBelowDomainTreeDistance geometry domain (left , right) =
  connectedDomainTreeDominatesSupportGraphDistance geometry domain left right

asR411SelectedSupportConnectionGeometry :
  ∀ {Domain Term} →
  DomainSpecificTwoMarkSupportGeometry Domain Term →
  R411.SelectedSupportConnectionGeometry Domain Term
asR411SelectedSupportConnectionGeometry geometry = record
  { R411.SelectedSupportConnectionGeometry.selectedConnectingDistance =
      Graph.ymGraphDist (leftMark geometry) (rightMark geometry)
  ; R411.SelectedSupportConnectionGeometry.domainTreeDistance =
      domainTreeDistance geometry
  ; R411.SelectedSupportConnectionGeometry.selectedDifferentiatedTermSurvives =
      selectedDifferentiatedTermSurvives geometry
  ; R411.SelectedSupportConnectionGeometry.domainConnectsBothSupports =
      domainConnectsBothSelectedMarks geometry
  ; R411.SelectedSupportConnectionGeometry.survivingTermForcesSupportConnection =
      survivingTermForcesConnection geometry
  ; R411.SelectedSupportConnectionGeometry.supportConnectionForcesDistanceLower =
      selectedDistanceBelowDomainTreeDistance geometry
  }

round447DomainIndexedMetricCompilerLevel : ProofLevel
round447DomainIndexedMetricCompilerLevel = machineChecked

round447SelectedDistanceTransportCompilerLevel : ProofLevel
round447SelectedDistanceTransportCompilerLevel = machineChecked

-- Genuine B4 geometry: construct the source Y_0 connected core/tree for each
-- retained R429 domain and prove that its tree depth dominates the graph
-- distance between the two selected source links.
literalRound447ConnectedCoreTreeGeometryLevel : ProofLevel
literalRound447ConnectedCoreTreeGeometryLevel = conditional
