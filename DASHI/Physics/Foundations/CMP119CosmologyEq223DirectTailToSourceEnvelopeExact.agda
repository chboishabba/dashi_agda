{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223DirectTailToSourceEnvelopeExact where

------------------------------------------------------------------------
-- EQ.(2.23) DIRECT-TAIL -> SOURCE-ENVELOPE PRODUCER.
--
-- This owner composes the two already-separated compiler facts:
--
--   embed Q_R136 <= embed D_Gamma,k + embed Tail_R109(k)
--   D_Gamma,k <= M_ERB + c_V
--
-- into the smaller terminal response coordinate
--
--   embed Q_R136
--     <= embed ((M_ERB + c_V) + Tail_R109(k)).
--
-- The physical producers are not collapsed: B1 still supplies the direct tail
-- receipt, and B2 still has to make the source envelope strictly negative.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_)

import DASHI.Physics.Foundations.CMP119CosmologyEq223CombinedERBEnvelopeMaxCutExact as Envelope
import DASHI.Physics.Foundations.CMP119CosmologyEq223FiniteEffectiveActionUpperExact as Finite
import DASHI.Physics.Foundations.CMP119CosmologyEq223R136SourceEnvelopeUpperExact as SourceEnvelope
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyR144R109DirectTailAnchorExact as Direct
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order

import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Additive
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

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
  where

  module F =
    Finite realization measure orderLaws partition scaleLaw signLaws referenceFixed
  module E = Envelope realization measure orderLaws partition scaleLaw

  sourceUpper : E.CombinedERBTraceEnvelope → ℚ
  sourceUpper envelope =
    E.combinedUpper envelope
      + Eq223.eq223VacuumTraceCoefficient realization

  directTailToSourceEnvelope :
    (completed : ℚ) →
    (start : Nat) →
    (envelope : E.CombinedERBTraceEnvelope) →
    Direct.DirectR144R109TailAnchor
      embedding r109Source completed F.finiteEffectiveActionWeyl start →
    SourceEnvelope.R136SourceEnvelopeUpper
      embedding r109Source completed (sourceUpper envelope) start
  directTailToSourceEnvelope completed start envelope direct =
    SourceEnvelope.fromDirectTailAndFiniteUpper
      embedding direct
      (F.finiteEffectiveActionWeylBelowCombinedSourceUpper envelope)

  sourceEnvelopeUpperIsCombinedERBPlusVacuum :
    (envelope : E.CombinedERBTraceEnvelope) →
    sourceUpper envelope
    ≡ E.combinedUpper envelope
        + Eq223.eq223VacuumTraceCoefficient realization
  sourceEnvelopeUpperIsCombinedERBPlusVacuum envelope =
    Agda.Builtin.Equality.refl

eq223FiniteUpperCompilesIntoR136SourceEnvelope : Bool
eq223FiniteUpperCompilesIntoR136SourceEnvelope = true

finiteDGammaRemainsTerminalConsumerCoordinate : Bool
finiteDGammaRemainsTerminalConsumerCoordinate = false

sourceEnvelopeCompilationAddsPhysicalPremise : Bool
sourceEnvelopeCompilationAddsPhysicalPremise = false
