{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedSupportGraphRound416Exact where

------------------------------------------------------------------------
-- ROUND416 / LITERAL TWO-MARK SUPPORT WITNESS -> R411 GEOMETRY
--
-- R411 intentionally abstracted
--
--   surviving selected term -> domain connects both supports
--   support connection      -> selected distance <= domain tree distance.
--
-- The second arrow is not new CMP116 analysis.  On the canonical YM support
-- graph, P02/P03 already prove
--
--   graphDist(left,right) <= treePathLength(left,right) <= treeEdgeCount.
--
-- This owner replaces R411's opaque connection proposition by a concrete pair
-- of domain-membership witnesses for the two selected source links.  The only
-- literal source payment is then that a surviving twice-marked term contains
-- both selected links, plus the same-object identification of CMP116's domain
-- tree coordinate with this support-tree edge count.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411

record SelectedTwoMarkSupportGraph
    (Domain Term : Set) : Set₁ where
  field
    leftMark rightMark : Support.Link

    selectedConnectingDistance : Nat
    selectedDistanceIsSupportGraphDistance :
      selectedConnectingDistance ≡ Graph.ymGraphDist leftMark rightMark

    domainTreeDistance : Domain → Nat
    domainTreeDistanceIsSupportTreeEdgeCount :
      ∀ domain →
      domainTreeDistance domain ≡ Graph.ymTreeEdgeCount

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

open SelectedTwoMarkSupportGraph public

domainConnectsBothSelectedMarks :
  ∀ {Domain Term} →
  SelectedTwoMarkSupportGraph Domain Term →
  Domain → Set
domainConnectsBothSelectedMarks source domain =
  containsSelectedLink source domain (leftMark source)
  ×
  containsSelectedLink source domain (rightMark source)

survivingTermForcesConcreteSupportConnection :
  ∀ {Domain Term}
    (source : SelectedTwoMarkSupportGraph Domain Term)
    domain term →
  selectedDifferentiatedTermSurvives source domain term →
  domainConnectsBothSelectedMarks source domain
survivingTermForcesConcreteSupportConnection source domain term survives =
  survivingTermContainsLeftMark source domain term survives ,
  survivingTermContainsRightMark source domain term survives

supportGraphDistanceBelowTreeEdgeCount :
  ∀ {Domain Term}
    (source : SelectedTwoMarkSupportGraph Domain Term) →
  Graph.ymGraphDist (leftMark source) (rightMark source)
  Nat.≤ Graph.ymTreeEdgeCount
supportGraphDistanceBelowTreeEdgeCount source =
  NatP.≤-trans
    (Graph.p02GraphDistMinimality
      (leftMark source) (rightMark source))
    (Graph.p03TreePathBoundedByEdgeCount
      (leftMark source) (rightMark source))

selectedDistanceBelowDomainTreeDistance :
  ∀ {Domain Term}
    (source : SelectedTwoMarkSupportGraph Domain Term)
    domain →
  domainConnectsBothSelectedMarks source domain →
  selectedConnectingDistance source
  Nat.≤ domainTreeDistance source domain
selectedDistanceBelowDomainTreeDistance source domain connects =
  subst
    (λ lower →
      lower Nat.≤ domainTreeDistance source domain)
    (sym (selectedDistanceIsSupportGraphDistance source))
    (subst
      (λ upper →
        Graph.ymGraphDist (leftMark source) (rightMark source)
        Nat.≤ upper)
      (sym (domainTreeDistanceIsSupportTreeEdgeCount source domain))
      (supportGraphDistanceBelowTreeEdgeCount source))

asR411SelectedSupportConnectionGeometry :
  ∀ {Domain Term} →
  SelectedTwoMarkSupportGraph Domain Term →
  R411.SelectedSupportConnectionGeometry Domain Term
asR411SelectedSupportConnectionGeometry source = record
  { R411.SelectedSupportConnectionGeometry.selectedConnectingDistance =
      selectedConnectingDistance source
  ; R411.SelectedSupportConnectionGeometry.domainTreeDistance =
      domainTreeDistance source
  ; R411.SelectedSupportConnectionGeometry.selectedDifferentiatedTermSurvives =
      selectedDifferentiatedTermSurvives source
  ; R411.SelectedSupportConnectionGeometry.domainConnectsBothSupports =
      domainConnectsBothSelectedMarks source
  ; R411.SelectedSupportConnectionGeometry.survivingTermForcesSupportConnection =
      survivingTermForcesConcreteSupportConnection source
  ; R411.SelectedSupportConnectionGeometry.supportConnectionForcesDistanceLower =
      selectedDistanceBelowDomainTreeDistance source
  }

survivingSelectedTermForcesDistanceLower :
  ∀ {Domain Term}
    (source : SelectedTwoMarkSupportGraph Domain Term)
    domain term →
  selectedDifferentiatedTermSurvives source domain term →
  selectedConnectingDistance source
  Nat.≤ domainTreeDistance source domain
survivingSelectedTermForcesDistanceLower source domain term survives =
  R411.survivingTermForcesSelectedDistanceLower
    (asR411SelectedSupportConnectionGeometry source)
    domain term survives

round416SupportConnectionCompilerLevel : ProofLevel
round416SupportConnectionCompilerLevel = machineChecked

round416SupportDistanceCompilerLevel : ProofLevel
round416SupportDistanceCompilerLevel = machineChecked

-- Genuine source/application leaves after the graph theorem is reused:
--   * surviving two-J CMP116 terms contain both selected source links;
--   * selected physical support distance is the support-graph distance;
--   * CMP116 domain-tree distance is the same support-tree coordinate.
literalTwoMarkMembershipAndMetricAttachmentLevel : ProofLevel
literalTwoMarkMembershipAndMetricAttachmentLevel = conditional
