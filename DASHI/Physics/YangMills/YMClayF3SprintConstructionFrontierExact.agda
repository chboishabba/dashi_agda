{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayF3SprintConstructionFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.YMSprint112ContinuumSamplingProjectionMapCandidate as Sampling112
import DASHI.Physics.Closure.YMSprint112RenormalizedInterpolationMapCandidate as Interpolation112
import DASHI.Physics.Closure.YMSprint116NormGaugeWindowClosureReducer as Norm116
import DASHI.Physics.Closure.YMSprint116ResidualConvergenceClosureReducer as Residual116

------------------------------------------------------------------------
-- F3 PHYSICAL CONSTRUCTION FRONTIER
--
-- The repository already has the Sprint109+ recovery consumers and the
-- Sprint111-122 map/estimate construction program. The residual is not
-- abstract Mosco theory. It is physical discharge of the concrete
-- sampling/interpolation and analytic estimate package.
--
-- Receipts and reducer flags below are diagnostic only. They never inhabit
-- theorem-bearing fields of PhysicalF3ConstructionInputs.
------------------------------------------------------------------------

record PhysicalF3ConstructionInputs : Set₁ where
  field
    ActualSamplingProjectionPa : Set
    actualSamplingProjectionPa : ActualSamplingProjectionPa

    ActualRenormalizedInterpolationEa : Set
    actualRenormalizedInterpolationEa :
      ActualRenormalizedInterpolationEa

    GaugeQuotientRepresentativeIndependence : Set
    gaugeQuotientRepresentativeIndependence :
      GaugeQuotientRepresentativeIndependence

    UniformNormAndApproximateInverseControl : Set
    uniformNormAndApproximateInverseControl :
      UniformNormAndApproximateInverseControl

    ResidualAndStrongConvergence : Set
    residualAndStrongConvergence :
      ResidualAndStrongConvergence

    EnergyLiminfLimsupRecovery : Set
    energyLiminfLimsupRecovery :
      EnergyLiminfLimsupRecovery

    VacuumSectorStability : Set
    vacuumSectorStability :
      VacuumSectorStability

    LiteralWilsonMeasureConvergence : Set
    literalWilsonMeasureConvergence :
      LiteralWilsonMeasureConvergence

open PhysicalF3ConstructionInputs public

sprint112SamplingMapConstructed : Bool
sprint112SamplingMapConstructed =
  Sampling112.samplingProjectionMapConstructedHere

sprint112InterpolationMapConstructed : Bool
sprint112InterpolationMapConstructed =
  Interpolation112.interpolationMapConstructedHere

sprint116UnconditionalNormWindowClosed : Bool
sprint116UnconditionalNormWindowClosed =
  Norm116.unconditionalNormWindowTheoremProvedHere

sprint116QuotientGaugeAnalyticFeedsDischarged : Bool
sprint116QuotientGaugeAnalyticFeedsDischarged =
  Norm116.quotientGaugeAnalyticFeedsDischargedHere

sprint116ResidualReducerExists : Bool
sprint116ResidualReducerExists =
  Residual116.residualConvergenceClosureReducerRecorded

sprint112SamplingStillOpen : sprint112SamplingMapConstructed ≡ false
sprint112SamplingStillOpen = refl

sprint112InterpolationStillOpen : sprint112InterpolationMapConstructed ≡ false
sprint112InterpolationStillOpen = refl

sprint116NormWindowStillOpen :
  sprint116UnconditionalNormWindowClosed ≡ false
sprint116NormWindowStillOpen = refl

sprint116QuotientGaugeStillOpen :
  sprint116QuotientGaugeAnalyticFeedsDischarged ≡ false
sprint116QuotientGaugeStillOpen = refl

f3ConstructionProgramIdentified : Bool
f3ConstructionProgramIdentified = true

f3ConstructionProgramIdentifiedIsTrue :
  f3ConstructionProgramIdentified ≡ true
f3ConstructionProgramIdentifiedIsTrue = refl

physicalF3ConstructionLevel : ProofLevel
physicalF3ConstructionLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
