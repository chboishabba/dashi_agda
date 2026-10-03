{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyBalabanLogWeightOrientationExact where

------------------------------------------------------------------------
-- BALABAN SOURCE CONVENTION: THE GENERATED BLOCK ACTION IS LOG-WEIGHT ORIENTED.
--
-- Primary calibration: T. Balaban, CMP 109 (1987), DOI 10.1007/BF01215223,
-- Eqs. (0.17), (0.19): the blocked action is defined as the logarithm of a
-- normalized block integral.  Therefore the preferred source-facing finite
-- orientation is +D log Z, not Gamma = - log Z.
--
-- What remains physical/same-object is NOT the sign convention.  It is the
-- equality identifying the selected R136 continuum first variation with this
-- exact normalized finite log-weight response.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Foundations.CMP119CosmologyFiniteWeylConventionFirewallExact as Convention
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

record BalabanLogWeightContinuumWeld
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (authority : Partition.PhysicalFinitePartitionAuthority measure)
    (d : Source.CompleteFiniteMetricVariation Configuration)
    (continuumResponse : ℚ)
    : Set₁ where
  field
    sameObjectLogWeightResponse :
      continuumResponse
      ≡ Convention.logPartitionWeylResponse measure authority d

open BalabanLogWeightContinuumWeld public

asFiniteWeylToContinuumConvention :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    {authority : Partition.PhysicalFinitePartitionAuthority measure}
    {d : Source.CompleteFiniteMetricVariation Configuration}
    {continuumResponse : ℚ} →
  BalabanLogWeightContinuumWeld measure authority d continuumResponse →
  Convention.FiniteWeylToContinuumTraceConvention
    measure authority d continuumResponse
asFiniteWeylToContinuumConvention weld = record
  { Convention.FiniteWeylToContinuumTraceConvention.orientation =
      Convention.continuumReadsLogPartitionResponse
  ; Convention.FiniteWeylToContinuumTraceConvention.selectedOrientationIsCorrect =
      sameObjectLogWeightResponse weld
  }

preferredBalabanOrientationIsLogPartition :
  Convention.FiniteToContinuumWeylOrientation
preferredBalabanOrientationIsLogPartition =
  Convention.continuumReadsLogPartitionResponse

preferredBalabanOrientationIsNotAFreeBranch : Bool
preferredBalabanOrientationIsNotAFreeBranch = true

remainingOrientationLeafIsSameObjectR136ToLogWeightResponse : Bool
remainingOrientationLeafIsSameObjectR136ToLogWeightResponse = true
