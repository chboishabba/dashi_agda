{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralSupportMetricAttachmentRound358Exact where

------------------------------------------------------------------------
-- ROUND358 / SOURCE METRIC ATTACHMENT REDUCES TO TWO SAME-OBJECT WELDS
--
-- R356 exposed four apparent source/application seams around the large-X
-- branch.  The existing YMSupportGraphDistance owner already provides, on the
-- SAME support graph:
--
--   graphDist <= treePathLength <= treeEdgeCount.
--
-- Therefore those graph-theoretic inequalities are not new YM mathematics.
-- To instantiate R356 on the literal CMP109/CMP116 carrier we only need:
--
--   G_exit : collarRadius <= ymGraphDist anchor outside
--   G_tree : cmp116TreeLength = ymTreeEdgeCount
--
-- for the correctly selected source anchor/outside pair and the SAME
-- localization object.  The first is the literal coefficient-collar exit
-- attachment; the second is the literal CMP116 tree/localisation-length
-- attachment.  This module compiles those two fields into R356 and proves the
-- resulting large-localisation payment.
--
-- No source citation/status creates either weld, and no new graph theorem is
-- introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (Nat; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph
import DASHI.Physics.YangMills.BalabanConnectedCollarSpanRound356Exact as R356

record LiteralSupportMetricAttachment : Set where
  field
    anchor outside : Graph.YMVertex
    collarRadius cmp116TreeLength : Nat

    -- Literal CMP109/CMP99 source application: the selected outside point is
    -- genuinely beyond the enlarged coefficient collar on the YM support
    -- graph.
    coefficientCollarExitOnSupportGraph :
      collarRadius ≤ Graph.ymGraphDist anchor outside

    -- Literal CMP116 source application: the tree/localisation length carried
    -- by the marked activity is the edge-count coordinate of this SAME support
    -- tree presentation.
    cmp116TreeLengthIsSupportTreeEdgeCount :
      cmp116TreeLength ≡ Graph.ymTreeEdgeCount

open LiteralSupportMetricAttachment public

asConnectedCollarSpan :
  LiteralSupportMetricAttachment →
  R356.ConnectedCollarSpan
asConnectedCollarSpan dataSet = record
  { R356.ConnectedCollarSpan.collarRadius = collarRadius dataSet
  ; R356.ConnectedCollarSpan.graphDistance =
      Graph.ymGraphDist (anchor dataSet) (outside dataSet)
  ; R356.ConnectedCollarSpan.treePathLength =
      Graph.Path.pathLength
        (Graph.ymTreePath (anchor dataSet) (outside dataSet))
  ; R356.ConnectedCollarSpan.treeSize = cmp116TreeLength dataSet
  ; R356.ConnectedCollarSpan.collarExitDistance =
      coefficientCollarExitOnSupportGraph dataSet
  ; R356.ConnectedCollarSpan.graphDistanceBelowTreePath =
      Graph.p02GraphDistMinimality
        (anchor dataSet) (outside dataSet)
  ; R356.ConnectedCollarSpan.treePathBelowTreeSize =
      subst
        (λ bound →
          Graph.Path.pathLength
            (Graph.ymTreePath (anchor dataSet) (outside dataSet))
          ≤ bound)
        (sym (cmp116TreeLengthIsSupportTreeEdgeCount dataSet))
        (Graph.p03TreePathBoundedByEdgeCount
          (anchor dataSet) (outside dataSet))
  }

literalSupportMetricAttachmentPaysLargeTree :
  (dataSet : LiteralSupportMetricAttachment) →
  collarRadius dataSet ≤ cmp116TreeLength dataSet
literalSupportMetricAttachmentPaysLargeTree dataSet =
  R356.connectedCollarExitForcesLargeTree
    (asConnectedCollarSpan dataSet)

------------------------------------------------------------------------
-- Pareto/source accounting.
------------------------------------------------------------------------

supportGraphIntermediateInequalitiesCompilerLevel : ProofLevel
supportGraphIntermediateInequalitiesCompilerLevel = machineChecked

literalCoefficientCollarExitAttachmentLevel : ProofLevel
literalCoefficientCollarExitAttachmentLevel = conditional

literalCMP116TreeLengthAttachmentLevel : ProofLevel
literalCMP116TreeLengthAttachmentLevel = conditional

freshGraphDistanceTheoremRequired : Bool
freshGraphDistanceTheoremRequired = false

freshGraphDistanceTheoremRequiredIsFalse :
  freshGraphDistanceTheoremRequired ≡ false
freshGraphDistanceTheoremRequiredIsFalse = refl

freshTreePathBoundTheoremRequired : Bool
freshTreePathBoundTheoremRequired = false

freshTreePathBoundTheoremRequiredIsFalse :
  freshTreePathBoundTheoremRequired ≡ false
freshTreePathBoundTheoremRequiredIsFalse = refl

sourceMetricAttachmentIsSingleOpaqueLeaf : Bool
sourceMetricAttachmentIsSingleOpaqueLeaf = false

sourceMetricAttachmentIsSingleOpaqueLeafIsFalse :
  sourceMetricAttachmentIsSingleOpaqueLeaf ≡ false
sourceMetricAttachmentIsSingleOpaqueLeafIsFalse = refl

record Round358Boundary : Set where
  constructor round358-boundary
  field
    supportGraphCompilerOwned : Bool
    supportGraphCompilerOwnedIsTrue : supportGraphCompilerOwned ≡ true

    coefficientCollarExitAttachmentStillOpen : Bool
    coefficientCollarExitAttachmentStillOpenIsTrue :
      coefficientCollarExitAttachmentStillOpen ≡ true

    cmp116TreeLengthAttachmentStillOpen : Bool
    cmp116TreeLengthAttachmentStillOpenIsTrue :
      cmp116TreeLengthAttachmentStillOpen ≡ true

    noFreshGraphTheoremRequired : Bool
    noFreshGraphTheoremRequiredIsTrue :
      noFreshGraphTheoremRequired ≡ true

canonicalRound358Boundary : Round358Boundary
canonicalRound358Boundary =
  round358-boundary
    true refl
    true refl
    true refl
    true refl

round358FrontierRefinementLevel : ProofLevel
round358FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
