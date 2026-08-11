module DASHI.Physics.YangMills.BalabanSelectedConstraintDerivativeSectorBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
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
-- Turn the nonlinear Gate-I derivative threshold 29/2048 into an exact
-- two-sector budget on the repository's literal tagged 780-row carrier.
--
-- The gauge sector is not left abstract: it is the literal difference
-- D F_U[h]-D F_A[h].  The preceding two-background theorem gives
--
--   ||D F_U-D F_A||^2 <= (1/262144) ||h||^2.
--
-- Hence the block-average sector may consume 3711/262144, and the two
-- coefficients add exactly to 29/2048.  The raw tagged-row norm is exactly the
-- sum of the twelve average-row square and the 768 gauge-row square.  The
-- exact Pythagorean theorem for the mean-zero projection then shows
--
--   ||P(delta Q,delta F)||^2 <= ||(delta Q,delta F)||^2.
--
-- Thus the only physical derivative estimate still missing is the nonlinear
-- block-average derivative variation with coefficient 3711/262144.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair; map)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageRowCarrierExact as AverageRows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionOrthogonalityExact as Projection
import DASHI.Physics.YangMills.BalabanSelectedCombinedProjectionNormExact as ProjectionNorm
import DASHI.Physics.YangMills.BalabanSelectedGaugeDerivativeTwoBackgroundVariationExact as GaugeVariation

AverageVariation : Set
AverageVariation = Average.SelectedBlockAverageRow4 → ℚ

GaugeSectorVariation : Set
GaugeSectorVariation = FlatGauge.GaugeCoordinate4 → ℚ

RawVariation : Set
RawVariation = Combined.SelectedConstraintRow4 → ℚ

averageVariationNormSq : AverageVariation → ℚ
averageVariationNormSq variation =
  Sums.sumRational
    (Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector)
    (λ row → variation row * variation row)

gaugeVariationNormSq : GaugeSectorVariation → ℚ
gaugeVariationNormSq variation =
  Sums.sumRational
    (Basis.elements Rows.selectedGaugeRowFiniteSelector)
    (λ row → variation row * variation row)

combineDerivativeSectors : AverageVariation → GaugeSectorVariation → RawVariation
combineDerivativeSectors average gauge (Combined.averageConstraintRow row) = average row
combineDerivativeSectors average gauge (Combined.gaugeConstraintRow row) = gauge row

combinedDerivativeSectorNormExact : ∀ average gauge →
  ProjectionNorm.rawMultiplierNormSq (combineDerivativeSectors average gauge)
  ≡ averageVariationNormSq average + gaugeVariationNormSq gauge
combinedDerivativeSectorNormExact average gauge =
  let
    averageRows = Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector
    gaugeRows = Basis.elements Rows.selectedGaugeRowFiniteSelector
  in
  trans
    (Fubini.sumRationalAppend
      (map Combined.averageConstraintRow averageRows)
      (map Combined.gaugeConstraintRow gaugeRows)
      (λ row →
        combineDerivativeSectors average gauge row
          * combineDerivativeSectors average gauge row))
    (cong₂ _+_
      (Fubini.sumRationalMap Combined.averageConstraintRow averageRows
        (λ row →
          combineDerivativeSectors average gauge row
            * combineDerivativeSectors average gauge row))
      (Fubini.sumRationalMap Combined.gaugeConstraintRow gaugeRows
        (λ row →
          combineDerivativeSectors average gauge row
            * combineDerivativeSectors average gauge row)))

literalGaugeTwoBackgroundVariation :
  Physical.RationalSU2Background4 →
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → GaugeSectorVariation
literalGaugeTwoBackgroundVariation left right field (pair coordinate site) =
  Gauge.backgroundGaugeFirst left field (pair coordinate site)
  - Gauge.backgroundGaugeFirst right field (pair coordinate site)

literalGaugeVariationPointwiseExact :
  ∀ left right field coordinate site →
  literalGaugeTwoBackgroundVariation left right field (pair coordinate site)
  ≡ GaugeVariation.gaugeDerivativeTwoBackgroundCoordinate
      left right field coordinate site
literalGaugeVariationPointwiseExact left right field coordinate site = refl

literalGaugeVariationNormExact : ∀ left right field →
  gaugeVariationNormSq (literalGaugeTwoBackgroundVariation left right field)
  ≡ GaugeVariation.gaugeDerivativeTwoBackgroundVariationEnergy
      left right field
literalGaugeVariationNormExact left right field =
  let
    dx = λ site →
      GaugeVariation.gaugeDerivativeTwoBackgroundCoordinate
        left right field Coordinates.coordinateX site
    dy = λ site →
      GaugeVariation.gaugeDerivativeTwoBackgroundCoordinate
        left right field Coordinates.coordinateY site
    dz = λ site →
      GaugeVariation.gaugeDerivativeTwoBackgroundCoordinate
        left right field Coordinates.coordinateZ site

    afterCartesian :
      gaugeVariationNormSq (literalGaugeTwoBackgroundVariation left right field)
      ≡ Sums.sumRational Coordinates.lieCoordinates3
          (λ coordinate →
            Sums.sumRational (Block.physicalBlockSites Path4.side4)
              (λ site →
                GaugeVariation.gaugeDerivativeTwoBackgroundCoordinate
                  left right field coordinate site
                * GaugeVariation.gaugeDerivativeTwoBackgroundCoordinate
                    left right field coordinate site))
    afterCartesian =
      Fubini.sumCartesian Coordinates.lieCoordinates3
        (Block.physicalBlockSites Path4.side4)
        (λ row →
          literalGaugeTwoBackgroundVariation left right field row
            * literalGaugeTwoBackgroundVariation left right field row)

    toPeriodic :
      Sums.sumRational Coordinates.lieCoordinates3
        (λ coordinate →
          Sums.sumRational (Block.physicalBlockSites Path4.side4)
            (λ site →
              GaugeVariation.gaugeDerivativeTwoBackgroundCoordinate
                left right field coordinate site
              * GaugeVariation.gaugeDerivativeTwoBackgroundCoordinate
                  left right field coordinate site))
      ≡ Periodic.sumSites (λ site → dx site * dx site)
        + (Periodic.sumSites (λ site → dy site * dy site)
        + Periodic.sumSites (λ site → dz site * dz site))
    toPeriodic =
      trans
        (Sums.sumRationalCong Coordinates.lieCoordinates3 _ _
          (λ coordinate →
            sym
              (Bridge.sumSitesMatchesGlobalSiteSum
                (λ site →
                  GaugeVariation.gaugeDerivativeTwoBackgroundCoordinate
                    left right field coordinate site
                  * GaugeVariation.gaugeDerivativeTwoBackgroundCoordinate
                      left right field coordinate site))))
        (ℚRing.solve-∀
          (Periodic.sumSites (λ site → dx site * dx site))
          (Periodic.sumSites (λ site → dy site * dy site))
          (Periodic.sumSites (λ site → dz site * dz site)))

    energySplit :
      GaugeVariation.gaugeDerivativeTwoBackgroundVariationEnergy left right field
      ≡ Periodic.sumSites (λ site → dx site * dx site)
        + (Periodic.sumSites (λ site → dy site * dy site)
        + Periodic.sumSites (λ site → dz site * dz site))
    energySplit =
      trans
        (Periodic.sumSitesAdd
          (λ site → dx site * dx site)
          (λ site → dy site * dy site + dz site * dz site))
        (cong
          (Periodic.sumSites (λ site → dx site * dx site) +_)
          (Periodic.sumSitesAdd
            (λ site → dy site * dy site)
            (λ site → dz site * dz site)))
  in
  trans afterCartesian (trans toPeriodic (sym energySplit))

selectedReducedCombinedDerivativeVariationUpper :
  ∀ left right field averageVariation →
  Relaxed.RelaxedInverseLinkRadius left →
  Relaxed.RelaxedInverseLinkRadius right →
  averageVariationNormSq averageVariation
    ≤ GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
        * Coordinates.physicalSU2BondNormSq field →
  ProjectionNorm.rawMultiplierNormSq
    (Projection.selectedReducedProjection
      (combineDerivativeSectors averageVariation
        (literalGaugeTwoBackgroundVariation left right field)))
  ≤ GaugeVariation.fullDerivativeVariationSquaredBudget
      * Coordinates.physicalSU2BondNormSq field
selectedReducedCombinedDerivativeVariationUpper
    left right field averageVariation leftRadius rightRadius averageUpper =
  let
    gauge = literalGaugeTwoBackgroundVariation left right field
    combined = combineDerivativeSectors averageVariation gauge
    norm = Coordinates.physicalSU2BondNormSq field

    projectedBelowRaw = ProjectionNorm.selectedProjectionNormSqBelowRaw combined

    gaugeUpperEnergy =
      GaugeVariation.selectedGaugeDerivativeTwoBackgroundVariationUpper
        left right field leftRadius rightRadius

    gaugeUpper :
      gaugeVariationNormSq gauge
      ≤ GaugeVariation.gaugeDerivativeTwoBackgroundSquaredCoefficient * norm
    gaugeUpper =
      subst
        (λ lower → lower
          ≤ GaugeVariation.gaugeDerivativeTwoBackgroundSquaredCoefficient * norm)
        (sym (literalGaugeVariationNormExact left right field))
        gaugeUpperEnergy

    sectorUpper = ℚP.+-mono-≤ averageUpper gaugeUpper

    rawUpper :
      ProjectionNorm.rawMultiplierNormSq combined
      ≤ (GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
          + GaugeVariation.gaugeDerivativeTwoBackgroundSquaredCoefficient) * norm
    rawUpper =
      subst
        (λ lower →
          lower
          ≤ (GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
              + GaugeVariation.gaugeDerivativeTwoBackgroundSquaredCoefficient) * norm)
        (sym (combinedDerivativeSectorNormExact averageVariation gauge))
        (subst
          (λ upper →
            averageVariationNormSq averageVariation + gaugeVariationNormSq gauge
            ≤ upper)
          (ℚRing.solve-∀
            GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
            GaugeVariation.gaugeDerivativeTwoBackgroundSquaredCoefficient norm)
          sectorUpper)

    projectedUpper = ℚP.≤-trans projectedBelowRaw rawUpper
    coefficientExact =
      trans
        (ℚP.+-comm
          GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
          GaugeVariation.gaugeDerivativeTwoBackgroundSquaredCoefficient)
        GaugeVariation.gaugePlusBlockBudgetExact
  in
  subst
    (λ coefficient →
      ProjectionNorm.rawMultiplierNormSq
        (Projection.selectedReducedProjection combined)
      ≤ coefficient * norm)
    coefficientExact projectedUpper

selectedConstraintRawSectorNormSplitLevel : ProofLevel
selectedConstraintRawSectorNormSplitLevel = machineChecked

selectedConstraintGaugeSectorBudgetLevel : ProofLevel
selectedConstraintGaugeSectorBudgetLevel = machineChecked

selectedConstraintReducedDerivativeBudgetLevel : ProofLevel
selectedConstraintReducedDerivativeBudgetLevel = machineChecked

selectedBlockAverageNonlinearDerivativeVariationLevel : ProofLevel
selectedBlockAverageNonlinearDerivativeVariationLevel = conditional
