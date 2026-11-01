module DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeResidualExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Package the literal covariant backward-divergence derivative as the actual
-- finite residual jet consumed by the Hessian pipeline.  Its value is zero at
-- the selected gauge-fixed background, its first component is exactly
-- `backgroundGaugeFirst`, and its second component is set to zero because the
-- value/second pairing vanishes identically at an exact residual background.
--
-- The module proves, by finite Fubini and the side-four site enumeration, that
-- the generic `residualFirstNormSquared` is exactly the background gauge energy
-- used by the signed `-32 rho` and `-64 rho` theorems.  The flat comparison is
-- transported through the explicit positive-bond/periodic-field bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_; _-_; _≤_; _/_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (pair; Product)
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as Flat
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact as Global
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeSignedLowerExact as Signed

backgroundGaugeComponentJet :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Flat.GaugeCoordinate4 → Jets.ScalarSecondJet
backgroundGaugeComponentJet background fieldValue coordinate =
  Jets.scalarJet 0ℚ (Gauge.backgroundGaugeFirst background fieldValue coordinate) 0ℚ

backgroundGaugeResidual :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Jets.FiniteResidualSecondJet Flat.GaugeCoordinate4
backgroundGaugeResidual background fieldValue = record
  { Jets.FiniteResidualSecondJet.coordinates = Flat.flatGaugeCoordinates
  ; Jets.FiniteResidualSecondJet.componentJet =
      backgroundGaugeComponentJet background fieldValue
  }

backgroundGaugeResidualExact : ∀ background fieldValue →
  Jets.ExactResidualBackground (backgroundGaugeResidual background fieldValue)
backgroundGaugeResidualExact background fieldValue = record
  { Jets.ExactResidualBackground.residualZero = λ _ → refl }

backgroundGaugeResidualFirstNormSquared :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → ℚ
backgroundGaugeResidualFirstNormSquared background fieldValue =
  Jets.residualFirstNormSquared (backgroundGaugeResidual background fieldValue)

literalMapSumEqualsIndexedSum :
  ∀ {A : Set} (values : List A) (term : A → ℚ) →
  Jets.sumRational (map term values)
  ≡ Sums.sumRational values term
literalMapSumEqualsIndexedSum [] term = refl
literalMapSumEqualsIndexedSum (value ∷ values) term =
  cong (term value +_)
    (literalMapSumEqualsIndexedSum values term)

backgroundGaugeFirstNormAsCoordinateSiteSum : ∀ background fieldValue →
  backgroundGaugeResidualFirstNormSquared background fieldValue
  ≡ Sums.sumRational Coordinates.lieCoordinates3
      (λ coordinate →
        Sums.sumRational (Block.physicalBlockSites Path4.side4)
          (λ site →
            Gauge.backgroundGaugeFirst background fieldValue (pair coordinate site)
            * Gauge.backgroundGaugeFirst background fieldValue (pair coordinate site)))
backgroundGaugeFirstNormAsCoordinateSiteSum background fieldValue =
  let
    squareFirst : Flat.GaugeCoordinate4 → ℚ
    squareFirst coordinate =
      Gauge.backgroundGaugeFirst background fieldValue coordinate
      * Gauge.backgroundGaugeFirst background fieldValue coordinate
  in
  trans
    (literalMapSumEqualsIndexedSum Flat.flatGaugeCoordinates squareFirst)
    (Fubini.sumCartesian
      Coordinates.lieCoordinates3
      (Block.physicalBlockSites Path4.side4)
      squareFirst)

backgroundGaugeCoordinateSiteSwap : ∀ background fieldValue →
  Sums.sumRational Coordinates.lieCoordinates3
      (λ coordinate →
        Sums.sumRational (Block.physicalBlockSites Path4.side4)
          (λ site →
            Gauge.backgroundGaugeFirst background fieldValue (pair coordinate site)
            * Gauge.backgroundGaugeFirst background fieldValue (pair coordinate site)))
  ≡ Sums.sumRational (Block.physicalBlockSites Path4.side4)
      (λ site → Signed.backgroundGaugePointEnergy background fieldValue site)
backgroundGaugeCoordinateSiteSwap background fieldValue =
  trans
    (Fubini.sumSwap
      Coordinates.lieCoordinates3
      (Block.physicalBlockSites Path4.side4)
      (λ coordinate site →
        Gauge.backgroundGaugeFirst background fieldValue (pair coordinate site)
        * Gauge.backgroundGaugeFirst background fieldValue (pair coordinate site)))
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4)
      (λ site →
        Sums.sumRational Coordinates.lieCoordinates3
          (λ coordinate →
            Gauge.backgroundGaugeFirst background fieldValue (pair coordinate site)
            * Gauge.backgroundGaugeFirst background fieldValue (pair coordinate site)))
      (Signed.backgroundGaugePointEnergy background fieldValue)
      (λ site → refl))

backgroundGaugeGlobalSiteSumIsPeriodic : ∀ background fieldValue →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
      (λ site → Signed.backgroundGaugePointEnergy background fieldValue site)
  ≡ Signed.backgroundGaugeEnergy background fieldValue
backgroundGaugeGlobalSiteSumIsPeriodic background fieldValue =
  trans
    (Partition.globalSiteSumMatchesCoordinateSum4
      (Signed.backgroundGaugePointEnergy background fieldValue))
    (sym
      (Global.periodicSumSitesMatchesCoordinateSum4
        (Signed.backgroundGaugePointEnergy background fieldValue)))

backgroundGaugeResidualFirstNormIsEnergy : ∀ background fieldValue →
  backgroundGaugeResidualFirstNormSquared background fieldValue
  ≡ Signed.backgroundGaugeEnergy background fieldValue
backgroundGaugeResidualFirstNormIsEnergy background fieldValue =
  trans
    (backgroundGaugeFirstNormAsCoordinateSiteSum background fieldValue)
    (trans
      (backgroundGaugeCoordinateSiteSwap background fieldValue)
      (backgroundGaugeGlobalSiteSumIsPeriodic background fieldValue))

backgroundGaugeResidualSecondVariationIsEnergy : ∀ background fieldValue →
  Jets.residualSecondVariation (backgroundGaugeResidual background fieldValue)
  ≡ Signed.backgroundGaugeEnergy background fieldValue
backgroundGaugeResidualSecondVariationIsEnergy background fieldValue =
  trans
    (Jets.residualSecondVariationAtExactBackground
      (backgroundGaugeResidual background fieldValue)
      (backgroundGaugeResidualExact background fieldValue))
    (backgroundGaugeResidualFirstNormIsEnergy background fieldValue)

backgroundGaugeResidualSignedLowerSixtyFour :
  ∀ background fieldValue →
  Signed.ConfiguredInverseLinkRadius background →
  - ((+ 64 / 1) * Signed.rho
      * Coordinates.physicalSU2BondNormSq fieldValue)
  ≤ Jets.residualSecondVariation
      (backgroundGaugeResidual background fieldValue)
      - Periodic.physicalPeriodicDivergenceEnergy
          (Bridge.asPeriodicField fieldValue)
backgroundGaugeResidualSignedLowerSixtyFour background fieldValue radius =
  let
    signed = Signed.backgroundGaugeSignedLowerSixtyFour
      background fieldValue radius
  in
  subst
    (λ left →
      - ((+ 64 / 1) * Signed.rho
          * Coordinates.physicalSU2BondNormSq fieldValue)
      ≤ left - Periodic.physicalPeriodicDivergenceEnergy
          (Bridge.asPeriodicField fieldValue))
    (sym (backgroundGaugeResidualSecondVariationIsEnergy background fieldValue))
    (subst
      (λ right →
        - ((+ 64 / 1) * Signed.rho
            * Coordinates.physicalSU2BondNormSq fieldValue)
        ≤ Signed.backgroundGaugeEnergy background fieldValue - right)
      (Signed.flatGaugeEnergyIsPhysicalDivergence fieldValue)
      signed)

physicalBackgroundGaugeResidualLevel : ProofLevel
physicalBackgroundGaugeResidualLevel = machineChecked

physicalBackgroundGaugeResidualEnergyLevel : ProofLevel
physicalBackgroundGaugeResidualEnergyLevel = machineChecked

physicalBackgroundGaugeResidualSignedLevel : ProofLevel
physicalBackgroundGaugeResidualSignedLevel = machineChecked
