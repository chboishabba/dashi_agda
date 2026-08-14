module DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact where

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
-- Construct the exact flat-background gauge residual jet on the repository's
-- literal physical perturbation.  Its first jet is the backward periodic
-- divergence `sum_mu delta_mu h_mu^a(x)`, while its value and second jet vanish.
-- The generic squared-residual chain rule therefore reduces to the first-jet
-- square, and the finite coordinate sum is proved equal to the physical
-- periodic divergence energy.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _+_)
open import Relation.Binary.PropositionalEquality using
  (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Product; pair; cartesian)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge

GaugeCoordinate4 : Set
GaugeCoordinate4 = Product Physical.LieCoordinate3 Periodic.Site4

flatGaugeCoordinates : List GaugeCoordinate4
flatGaugeCoordinates =
  cartesian Physical.lieCoordinates3
    (Block.physicalBlockSites Path4.side4)

flatGaugeFirst :
  Physical.PhysicalSU2BondField4 → GaugeCoordinate4 → ℚ
flatGaugeFirst fieldValue (pair coordinate site) =
  Periodic.periodicDivergence (Bridge.asPeriodicField fieldValue coordinate) site

flatGaugeComponentJet :
  Physical.PhysicalSU2BondField4 → GaugeCoordinate4 → Jets.ScalarSecondJet
flatGaugeComponentJet fieldValue coordinate =
  Jets.scalarJet 0ℚ (flatGaugeFirst fieldValue coordinate) 0ℚ

flatGaugeResidual :
  Physical.PhysicalSU2BondField4 →
  Jets.FiniteResidualSecondJet GaugeCoordinate4
flatGaugeResidual fieldValue = record
  { Jets.FiniteResidualSecondJet.coordinates = flatGaugeCoordinates
  ; Jets.FiniteResidualSecondJet.componentJet = flatGaugeComponentJet fieldValue
  }

flatGaugeBackgroundExact : ∀ fieldValue →
  Jets.ExactResidualBackground (flatGaugeResidual fieldValue)
flatGaugeBackgroundExact fieldValue = record
  { Jets.ExactResidualBackground.residualZero = λ _ → refl }

flatGaugeFirstNormSquared : Physical.PhysicalSU2BondField4 → ℚ
flatGaugeFirstNormSquared fieldValue =
  Jets.residualFirstNormSquared (flatGaugeResidual fieldValue)

literalMapSumEqualsIndexedSum :
  ∀ {A : Set} (values : List A) (term : A → ℚ) →
  Jets.sumRational (map term values)
  ≡ Sums.sumRational values term
literalMapSumEqualsIndexedSum [] term = refl
literalMapSumEqualsIndexedSum (value ∷ values) term =
  cong (term value +_)
    (literalMapSumEqualsIndexedSum values term)

flatGaugeFirstNormAsCoordinateSiteSum : ∀ fieldValue →
  flatGaugeFirstNormSquared fieldValue
  ≡ Sums.sumRational Physical.lieCoordinates3
      (λ coordinate →
        Sums.sumRational (Block.physicalBlockSites Path4.side4)
          (λ site →
            Periodic.periodicDivergence
              (Bridge.asPeriodicField fieldValue coordinate) site
            * Periodic.periodicDivergence
              (Bridge.asPeriodicField fieldValue coordinate) site))
flatGaugeFirstNormAsCoordinateSiteSum fieldValue =
  let
    squareFirst : GaugeCoordinate4 → ℚ
    squareFirst coordinate =
      flatGaugeFirst fieldValue coordinate * flatGaugeFirst fieldValue coordinate
  in
  trans
    (literalMapSumEqualsIndexedSum flatGaugeCoordinates squareFirst)
    (Fubini.sumCartesian
      Physical.lieCoordinates3
      (Block.physicalBlockSites Path4.side4)
      squareFirst)

flatGaugeFirstNormIsPeriodicDivergence : ∀ fieldValue →
  flatGaugeFirstNormSquared fieldValue
  ≡ Periodic.physicalPeriodicDivergenceEnergy
      (Bridge.asPeriodicField fieldValue)
flatGaugeFirstNormIsPeriodicDivergence fieldValue =
  flatGaugeFirstNormAsCoordinateSiteSum fieldValue

flatGaugeSecondVariationIsPeriodicDivergence : ∀ fieldValue →
  Jets.residualSecondVariation (flatGaugeResidual fieldValue)
  ≡ Periodic.physicalPeriodicDivergenceEnergy
      (Bridge.asPeriodicField fieldValue)
flatGaugeSecondVariationIsPeriodicDivergence fieldValue =
  trans
    (Jets.residualSecondVariationAtExactBackground
      (flatGaugeResidual fieldValue) (flatGaugeBackgroundExact fieldValue))
    (flatGaugeFirstNormIsPeriodicDivergence fieldValue)

physicalFlatGaugeJetLevel : ProofLevel
physicalFlatGaugeJetLevel = machineChecked

physicalFlatGaugeExactBackgroundLevel : ProofLevel
physicalFlatGaugeExactBackgroundLevel = machineChecked

physicalFlatGaugeDivergenceIdentificationLevel : ProofLevel
physicalFlatGaugeDivergenceIdentificationLevel = machineChecked
