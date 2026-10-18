{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223NegativeSectorDominanceExact where

------------------------------------------------------------------------
-- PREFERRED GRAVITATIONAL SOURCE-SIGN CUT ON THE LITERAL EQ.(2.23) SOURCE.
--
-- R144 fixes the one-point stress orientation as D_Gamma = - D Z / Z.
-- Therefore the useful finite Weyl sign is obtained when the literal Eq.(2.23)
-- non-Wilson numerator is negative.  Do not charge four unrelated signs.
-- The exact one-inequality target is
--
--     N_E + N_R + N_B < - N_V.
--
-- The generic sector-dominance compiler already proves that this is equivalent
-- to a negative four-sector balance and hence a negative matter-effective-
-- action Weyl response.  This owner pins that compiler to the actual selected
-- Eq.(2.23) E/R/B/V metric variations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_; -_)

import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologySectorDominanceSignMaxCutExact as Dominance
import DASHI.Physics.Foundations.CMP119CosmologyVacuumDominatedWeylSignExact as VacuumCut
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSignMaxCutExact as Sign
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
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

  literalVariation : Source.CompleteFiniteMetricVariation Configuration
  literalVariation = Eq223.sourceCompleteFiniteMetricVariation realization

  literalERBNumerator :
    Physical.PhysicalFiniteYMMeasure Configuration ℚ → ℚ
  literalERBNumerator measure =
    VacuumCut.erbNumerator measure literalVariation

  literalVacuumNumerator :
    Physical.PhysicalFiniteYMMeasure Configuration ℚ → ℚ
  literalVacuumNumerator measure =
    Sector.vacuumNumerator measure literalVariation

  LiteralNegativeSectorDominance :
    Physical.PhysicalFiniteYMMeasure Configuration ℚ → Set
  LiteralNegativeSectorDominance measure =
    literalERBNumerator measure < - literalVacuumNumerator measure

  literalDominanceForcesNegativeFourSectorBalance :
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) →
    LiteralNegativeSectorDominance measure →
    ((Sector.regularNumerator measure literalVariation
      + Sector.rOperationNumerator measure literalVariation)
      + (Sector.boundaryNumerator measure literalVariation
        + Sector.vacuumNumerator measure literalVariation))
    < 0ℚ
  literalDominanceForcesNegativeFourSectorBalance measure dominance =
    Dominance.erbBelowNegativeVacuumForcesNegativeFourSectorBalance
      measure literalVariation dominance

  literalDominanceForcesNegativeEffectiveActionWeyl :
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (laws : Sign.RationalWeylSignIntegrationLaws measure)
    (referenceFixed :
      ∀ h x → Source.referenceMeasureLogVariation literalVariation h x ≡ 0ℚ) →
    LiteralNegativeSectorDominance measure →
    Convention.matterEffectiveActionWeylResponse
      measure partition literalVariation < 0ℚ
  literalDominanceForcesNegativeEffectiveActionWeyl
      measure partition laws referenceFixed dominance =
    Dominance.sectorDominanceForcesNegativeMatterEffectiveActionWeyl
      measure literalVariation laws partition referenceFixed dominance

  preferredEq223SignIsOneDominanceInequality : Bool
  preferredEq223SignIsOneDominanceInequality = true

  cmp122AnalyticSmallnessDoesNotByItselfFixThisSign : Bool
  cmp122AnalyticSmallnessDoesNotByItselfFixThisSign = true
