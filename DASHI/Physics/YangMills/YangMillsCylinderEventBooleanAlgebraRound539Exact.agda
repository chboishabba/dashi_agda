{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsCylinderEventBooleanAlgebraRound539Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND539:
-- EXPLICIT BOOLEAN-ALGEBRA LAWS FOR CYLINDER EVENTS
--
-- A Caratheodory/Kolmogorov extension theorem needs an algebra/ring of events,
-- not merely fields named empty/complement/union.  R495 intentionally kept the
-- event operations abstract but did not encode their laws.
--
-- This module supplies the missing law interface on the SAME event operations
-- already carried by the cylinder premeasure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsCylinderMeasureRepresentationMaxCutRound495Exact as R495

intersection :
  ∀ {Event : Set} →
  R495.CylinderProbabilityPremeasure Event ℝ →
  Event → Event → Event
intersection premeasure left right =
  R495.complement premeasure
    (R495.union premeasure
      (R495.complement premeasure left)
      (R495.complement premeasure right))

record ProbabilityEventBooleanAlgebraLaws
    {Event : Set}
    (premeasure : R495.CylinderProbabilityPremeasure Event ℝ)
    : Set₁ where
  field
    unionAssociative :
      ∀ left middle right →
      R495.union premeasure
        (R495.union premeasure left middle) right
      ≡
      R495.union premeasure left
        (R495.union premeasure middle right)

    unionCommutative :
      ∀ left right →
      R495.union premeasure left right
      ≡ R495.union premeasure right left

    unionIdempotent :
      ∀ event →
      R495.union premeasure event event ≡ event

    emptyUnionIdentity :
      ∀ event →
      R495.union premeasure
        (R495.empty premeasure) event
      ≡ event

    wholeUnionAbsorbing :
      ∀ event →
      R495.union premeasure
        (R495.whole premeasure) event
      ≡ R495.whole premeasure

    complementInvolutive :
      ∀ event →
      R495.complement premeasure
        (R495.complement premeasure event)
      ≡ event

    excludedMiddle :
      ∀ event →
      R495.union premeasure event
        (R495.complement premeasure event)
      ≡ R495.whole premeasure

    unionDistributesOverIntersection :
      ∀ left middle right →
      R495.union premeasure left
        (intersection premeasure middle right)
      ≡
      intersection premeasure
        (R495.union premeasure left middle)
        (R495.union premeasure left right)

    disjointExactlyEmptyIntersection :
      ∀ left right →
      (R495.Disjoint premeasure left right →
        intersection premeasure left right
        ≡ R495.empty premeasure)
      ×
      (intersection premeasure left right
        ≡ R495.empty premeasure →
        R495.Disjoint premeasure left right)

open ProbabilityEventBooleanAlgebraLaws public

round539BooleanAlgebraInterfaceLevel : ProofLevel
round539BooleanAlgebraInterfaceLevel = machineChecked

-- Physical/source payment: the literal cylinder-event operations used by the
-- CMP119 family must instantiate these ordinary event-algebra laws.
literalRound539CylinderEventBooleanAlgebraLevel : ProofLevel
literalRound539CylinderEventBooleanAlgebraLevel = conditional
