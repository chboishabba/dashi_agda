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
-- literal physical perturbation.  The coordinate set is
--
--   LieCoordinate3 x sideFourSite,
--
-- and the first jet is the backward periodic divergence
--
--   D F_0[h](a,x) = sum_mu delta_mu h_mu^a(x).
--
-- The residual value and second jet are zero.  Therefore the generic squared
-- residual chain rule reduces definitionally to the sum of first-jet squares.
-- This module proves that finite sum is exactly the physical periodic
-- divergence energy used in the Hodge theorem.
--
-- Hence both flat halves of the Hodge decomposition are now literal:
-- the rational Wilson plaquette Hessian is curl squared and the rational gauge
-- Hessian is divergence squared for the same PhysicalSU2BondField4 h.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (map)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing
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
flatGaugeFirst field (pair coordinate site) =
  Periodic.periodicDivergence (Bridge.asPeriodicField field coordinate) site

flatGaugeComponentJet :
  Physical.PhysicalSU2BondField4 → GaugeCoordinate4 → Jets.ScalarSecondJet
flatGaugeComponentJet field coordinate =
  Jets.scalarJet 0ℚ (flatGaugeFirst field coordinate) 0ℚ

flatGaugeResidual :
  Physical.PhysicalSU2BondField4 →
  Jets.FiniteResidualSecondJet GaugeCoordinate4
flatGaugeResidual field = record
  { Jets.FiniteResidualSecondJet.coordinates = flatGaugeCoordinates
  ; Jets.FiniteResidualSecondJet.componentJet = flatGaugeComponentJet field
  }

flatGaugeBackgroundExact : ∀ field →
  Jets.ExactResidualBackground (flatGaugeResidual field)
flatGaugeBackgroundExact field = record
  { Jets.ExactResidualBackground.residualZero = λ _ → refl }

flatGaugeFirstNormSquared : Physical.PhysicalSU2BondField4 → ℚ
flatGaugeFirstNormSquared field =
  Jets.residualFirstNormSquared (flatGaugeResidual field)

flatGaugeFirstNormAsCoordinateSiteSum : ∀ field →
  flatGaugeFirstNormSquared field
  ≡ Sums.sumRational Physical.lieCoordinates3
      (λ coordinate →
        Sums.sumRational (Block.physicalBlockSites Path4.side4)
          (λ site →
            Periodic.periodicDivergence
              (Bridge.asPeriodicField field coordinate) site
            * Periodic.periodicDivergence
              (Bridge.asPeriodicField field coordinate) site))
flatGaugeFirstNormAsCoordinateSiteSum field =
  trans
    (Fubini.sumRationalMap
      (λ coordinateSite → coordinateSite)
      flatGaugeCoordinates
      (λ coordinateSite →
        let jet = Jets.componentJet (flatGaugeResidual field) coordinateSite
        in Jets.jetFirst jet * Jets.jetFirst jet))
    (trans
      (Fubini.sumCartesian
        Physical.lieCoordinates3
        (Block.physicalBlockSites Path4.side4)
        (λ coordinateSite →
          let jet = Jets.componentJet (flatGaugeResidual field) coordinateSite
          in Jets.jetFirst jet * Jets.jetFirst jet))
      refl)

flatGaugeFirstNormIsPeriodicDivergence : ∀ field →
  flatGaugeFirstNormSquared field
  ≡ Periodic.physicalPeriodicDivergenceEnergy
      (Bridge.asPeriodicField field)
flatGaugeFirstNormIsPeriodicDivergence field =
  trans
    (flatGaugeFirstNormAsCoordinateSiteSum field)
    refl

flatGaugeSecondVariationIsPeriodicDivergence : ∀ field →
  Jets.residualSecondVariation (flatGaugeResidual field)
  ≡ Periodic.physicalPeriodicDivergenceEnergy
      (Bridge.asPeriodicField field)
flatGaugeSecondVariationIsPeriodicDivergence field =
  trans
    (Jets.residualSecondVariationAtExactBackground
      (flatGaugeResidual field) (flatGaugeBackgroundExact field))
    (flatGaugeFirstNormIsPeriodicDivergence field)

physicalFlatGaugeJetLevel : ProofLevel
physicalFlatGaugeJetLevel = machineChecked

physicalFlatGaugeExactBackgroundLevel : ProofLevel
physicalFlatGaugeExactBackgroundLevel = machineChecked

physicalFlatGaugeDivergenceIdentificationLevel : ProofLevel
physicalFlatGaugeDivergenceIdentificationLevel = machineChecked
