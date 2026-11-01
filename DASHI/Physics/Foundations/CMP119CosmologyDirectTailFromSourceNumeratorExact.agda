{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyDirectTailFromSourceNumeratorExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _<_)

import DASHI.Physics.Foundations.CMP119CosmologyUnnormalizedSourceTailMarginExact as Margin
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyR144R109DirectTailAnchorExact as Direct
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerExact as RealSign
import DASHI.Physics.Foundations.CMP119CosmologyRealR136TraceReadoutBridgeExact as Readout
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order

import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

------------------------------------------------------------------------
-- DIRECT SOURCE-NUMERATOR PREFERRED SIGN ROUTE
--
-- The old terminal B2 interface decomposed the finite source into an E/R/B
-- envelope plus a vacuum coefficient and then compared that normalized upper
-- bound against the R109 tail.
--
-- The literal finite source already owns an unnormalized non-Wilson numerator N
-- and positive partition Z.  Therefore B1 can consume the strictly weaker and
-- more source-native quantitative statement
--
--   N_k + Tail_109(k) * Z_k < 0.
--
-- `CMP119CosmologyUnnormalizedSourceTailMarginExact` turns this into the exact
-- normalized finite margin required by the direct B1 anchor, and the existing
-- ordered embedding compiler then forces the completed rational response
-- negative.
------------------------------------------------------------------------

module _
    {Density Background Fluctuation
     Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm
     Configuration : Set}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm}
    {scale : Nat}
    (realization :
      Eq223.Eq223SourceMetricVariationRealization
        source Configuration scale)
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (orderLaws : Order.RationalPositiveFiniteMeasureOrderLaws measure)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (scaleLaw : Vacuum.RationalHaarScaleLaw measure)
    (signLaws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x →
      Source.referenceMeasureLogVariation
        (Eq223.sourceCompleteFiniteMetricVariation realization) h x
      ≡ 0ℚ)
    (r109Source : R109.SourceNativeStressScaleCauchy)
    (embedding : Additive.OrderedAdditiveRationalRealEmbedding)
    (realOrder : RealSign.RealWeakStrictTransitivity)
    (reflection :
      Readout.NegativeOrderReflectionAtZero (Additive.base embedding))
  where

  module M =
    Margin realization measure orderLaws partition scaleLaw signLaws referenceFixed

  sourceNumeratorMarginForcesNegativeCompletion :
    ∀ {completedResponse start} →
    Direct.DirectR144R109TailAnchor
      embedding r109Source completedResponse
      M.F.finiteEffectiveActionWeyl start →
    M.F.nonWilsonNumerator
      + Tail.r109RemainingTail r109Source start * M.F.z
      < 0ℚ →
    completedResponse < 0ℚ
  sourceNumeratorMarginForcesNegativeCompletion
      {completedResponse} {start} anchor sourceMargin =
    Direct.directTailMarginForcesNegativeRationalCompletion
      embedding realOrder reflection anchor
      (M.sourceNumeratorTailMarginForcesFiniteTailMargin
        (Tail.r109RemainingTail r109Source start)
        sourceMargin)

preferredSignCanConsumeUnnormalizedSourceMarginDirectly : Bool
preferredSignCanConsumeUnnormalizedSourceMarginDirectly = true

eq223ERBVacuumDecompositionIsRequiredTerminalB2Interface : Bool
eq223ERBVacuumDecompositionIsRequiredTerminalB2Interface = false

remainingSourceSignPaymentCanBeOneNumeratorTailMargin : Bool
remainingSourceSignPaymentCanBeOneNumeratorTailMargin = true
