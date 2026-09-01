module DASHI.Chemistry.RefineryFeedstockSaltConstraintBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Geology.SaltGeochemistryExact as Salt
import DASHI.Chemistry.DrinkingWaterDistributionResidualCorrosionBidiExact as Corrosion

------------------------------------------------------------------------
-- REFINERY FEEDSTOCK / SALT / PROCESS-CONSTRAINT BIDI
--
-- The purpose of this owner is structural: crude/feedstock composition,
-- desalting state, corrosion/fouling burden, effective throughput and product
-- yield are distinct coordinates.  Salt/chloride chemistry can constrain a
-- refinery application, but salt content alone does not determine refinery
-- economics, outage state, corrosion mechanism or crack spread.
--
-- Existing source authority is reused:
-- * SaltGeochemistryExact owns brine/salinity/composition non-collapse and
--   material-lineage requirements.
-- * DrinkingWaterDistributionResidualCorrosionBidiExact owns the generic
--   chloride-presence != unique-corrosion-cause boundary.
--
-- Actual refinery thresholds, crude assays, desalter efficiencies, materials,
-- operating temperatures and corrosion data remain application receipts.
------------------------------------------------------------------------

data FeedstockState : Set where
  sameNominalCrudeLowSaltBurden
  sameNominalCrudeHighSaltBurden
  : FeedstockState

data NominalCrudeSurface : Set where
  sameCrudeGradeLabel : NominalCrudeSurface

data SaltWaterBurden : Set where
  lowerSaltWaterBurden higherSaltWaterBurden : SaltWaterBurden

data DesalterState : Set where
  desalterAdequate desalterConstrained : DesalterState

data ReliabilityBurden : Set where
  lowerReliabilityBurden higherReliabilityBurden : ReliabilityBurden

data EffectiveThroughput : Set where
  throughputAvailable throughputConstrained : EffectiveThroughput

data ProductYieldState : Set where
  productYieldAvailable productYieldConstrained : ProductYieldState

nominalCrudeSurface : FeedstockState → NominalCrudeSurface
nominalCrudeSurface _ = sameCrudeGradeLabel

saltWaterBurden : FeedstockState → SaltWaterBurden
saltWaterBurden sameNominalCrudeLowSaltBurden = lowerSaltWaterBurden
saltWaterBurden sameNominalCrudeHighSaltBurden = higherSaltWaterBurden

desalterState : FeedstockState → DesalterState
desalterState sameNominalCrudeLowSaltBurden = desalterAdequate
desalterState sameNominalCrudeHighSaltBurden = desalterConstrained

reliabilityBurden : FeedstockState → ReliabilityBurden
reliabilityBurden sameNominalCrudeLowSaltBurden = lowerReliabilityBurden
reliabilityBurden sameNominalCrudeHighSaltBurden = higherReliabilityBurden

effectiveThroughput : FeedstockState → EffectiveThroughput
effectiveThroughput sameNominalCrudeLowSaltBurden = throughputAvailable
effectiveThroughput sameNominalCrudeHighSaltBurden = throughputConstrained

productYieldState : FeedstockState → ProductYieldState
productYieldState sameNominalCrudeLowSaltBurden = productYieldAvailable
productYieldState sameNominalCrudeHighSaltBurden = productYieldConstrained

sameNominalCrude :
  nominalCrudeSurface sameNominalCrudeLowSaltBurden
  ≡ nominalCrudeSurface sameNominalCrudeHighSaltBurden
sameNominalCrude = refl

saltBurdenDiffers :
  saltWaterBurden sameNominalCrudeLowSaltBurden
  ≡ saltWaterBurden sameNominalCrudeHighSaltBurden → ⊥
saltBurdenDiffers ()

throughputDiffers :
  effectiveThroughput sameNominalCrudeLowSaltBurden
  ≡ effectiveThroughput sameNominalCrudeHighSaltBurden → ⊥
throughputDiffers ()

nominalCrudeCannotRecoverSaltBurden :
  INF.FactorsThrough nominalCrudeSurface saltWaterBurden → ⊥
nominalCrudeCannotRecoverSaltBurden =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameNominalCrudeLowSaltBurden
      sameNominalCrudeHighSaltBurden
      sameNominalCrude
      saltBurdenDiffers)

nominalCrudeCannotRecoverEffectiveThroughput :
  INF.FactorsThrough nominalCrudeSurface effectiveThroughput → ⊥
nominalCrudeCannotRecoverEffectiveThroughput =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameNominalCrudeLowSaltBurden
      sameNominalCrudeHighSaltBurden
      sameNominalCrude
      throughputDiffers)

------------------------------------------------------------------------
-- Refinery application receipts preserve the intermediate process fibres.
------------------------------------------------------------------------

record RefineryFeedstockReceipt : Set where
  constructor refinery-feedstock-receipt
  field
    feedstockAssayReference : String
    waterSedimentReference : String
    saltOrChlorideMeasurementReference : String
    fullIonicCompositionReference : String
    desalterOperatingReference : String
    downstreamChlorideSpeciationReference : String
    materialsCorrosionReference : String
    foulingDepositionReference : String
    throughputConstraintReference : String
    productYieldReference : String
    validationReference : String

------------------------------------------------------------------------
-- Existing-owner welds.
------------------------------------------------------------------------

saltBoundary : Salt.SaltGeochemistryBoundary
saltBoundary = Salt.canonicalSaltGeochemistryBoundary

corrosionBoundary : Corrosion.DistributionResidualCorrosionBoundary
corrosionBoundary = Corrosion.canonicalDistributionResidualCorrosionBoundary

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record RefineryFeedstockSaltBoundary : Set where
  constructor refinery-feedstock-salt-boundary
  field
    crudeGradeLabelDeterminesSaltBurden : Bool
    crudeGradeLabelDeterminesSaltBurdenIsFalse :
      crudeGradeLabelDeterminesSaltBurden ≡ false
    saltScalarDeterminesFullFeedstockChemistry : Bool
    saltScalarDeterminesFullFeedstockChemistryIsFalse :
      saltScalarDeterminesFullFeedstockChemistry ≡ false
    chloridePresenceDeterminesUniqueCorrosionMechanism : Bool
    chloridePresenceDeterminesUniqueCorrosionMechanismIsFalse :
      chloridePresenceDeterminesUniqueCorrosionMechanism ≡ false
    crudeAvailabilityEqualsUsableRefineryThroughput : Bool
    crudeAvailabilityEqualsUsableRefineryThroughputIsFalse :
      crudeAvailabilityEqualsUsableRefineryThroughput ≡ false
    saltBurdenAloneDeterminesCrackSpread : Bool
    saltBurdenAloneDeterminesCrackSpreadIsFalse :
      saltBurdenAloneDeterminesCrackSpread ≡ false
    applicationNeedsAssayProcessMaterialAndValidationReceipts : Bool
    applicationNeedsAssayProcessMaterialAndValidationReceiptsIsTrue :
      applicationNeedsAssayProcessMaterialAndValidationReceipts ≡ true

canonicalRefineryFeedstockSaltBoundary : RefineryFeedstockSaltBoundary
canonicalRefineryFeedstockSaltBoundary =
  refinery-feedstock-salt-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
