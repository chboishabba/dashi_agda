{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR109TailMonotonicityExact where

------------------------------------------------------------------------
-- ROUND109 REMAINING-TAIL ANTITONICITY.
--
-- The preferred finite->continuum cosmology route pays the literal Round109
-- remaining tail
--
--   C * (1/2) * (1/2)^k.
--
-- The repository already proves antitonicity of the exact rational halfPower
-- used here.  Hence once a source/tail margin is paid at one RG scale, every
-- later scale carries no larger completion debt.  No new convergence theorem
-- or physical estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base as Nat using (_≤_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanCMP116PhysicalDistanceLowerRound390Exact as Half
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Scale
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact as Sum
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

r109RemainingTailAntitone :
  (source : R109.SourceNativeStressScaleCauchy) →
  ∀ {near far : Nat} →
  near Nat.≤ far →
  Tail.r109RemainingTail source far
  ≤ Tail.r109RemainingTail source near
r109RemainingTailAntitone source {near} {far} near≤far =
  let
    majorant =
      Sum.commonMajorant
        (Source.sourceCompatibleSameFamilyIncrement
          (R109.source source)
          (R109.smallHistory source)
          (R109.stressInsertion source))

    powerFarBelowNear : Geo.halfPower far ≤ Geo.halfPower near
    powerFarBelowNear = Half.halfPowerAntitone near≤far

    halfScaled :
      Geo.half * Geo.halfPower far
      ≤ Geo.half * Geo.halfPower near
    halfScaled =
      Norm.scaleNonnegative
        Geo.half Geo.halfNonnegative powerFarBelowNear
  in
  Norm.scaleNonnegative
    (Scale.coefficient majorant)
    (Scale.coefficientNonnegative majorant)
    halfScaled

laterScaleNeverIncreasesR109CompletionDebt : Bool
laterScaleNeverIncreasesR109CompletionDebt = true
