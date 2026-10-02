{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223ConventionAwareSignRootExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_)

import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyConventionAwareSectorSignExact as Oriented
import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

module _
    {Density Background Fluctuation
     Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
     Configuration : Set}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    {scale : Nat}
    (realization :
      Eq223.Eq223SourceMetricVariationRealization
        source Configuration scale)
  where

  sourceMetricVariation :
    Source.CompleteFiniteMetricVariation Configuration
  sourceMetricVariation =
    Eq223.sourceCompleteFiniteMetricVariation realization

  sourceFourSectorBalance :
    Physical.PhysicalFiniteYMMeasure Configuration ℚ →
    ℚ
  sourceFourSectorBalance measure =
    Oriented.fourSectorBalance measure sourceMetricVariation

  sourceContinuumTraceNegativeFromExplicitConvention :
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x →
      Source.referenceMeasureLogVariation sourceMetricVariation h x ≡ 0ℚ)
    (continuumTrace : ℚ)
    (convention :
      Convention.FiniteWeylToContinuumTraceConvention
        measure partition sourceMetricVariation continuumTrace) →
    Oriented.NegativeOrientedTraceSign
      measure sourceMetricVariation
      (Convention.orientation convention) →
    continuumTrace < 0ℚ
  sourceContinuumTraceNegativeFromExplicitConvention
      measure partition laws referenceFixed continuumTrace convention witness =
    Oriented.continuumTraceNegativeFromExplicitConvention
      measure partition sourceMetricVariation laws referenceFixed
      continuumTrace convention witness

  sectorCallbacksPinnedToEq223Source : Bool
  sectorCallbacksPinnedToEq223Source = true

  conventionStillMustBeFixedBeforeChoosingBalanceSign : Bool
  conventionStillMustBeFixedBeforeChoosingBalanceSign = true
