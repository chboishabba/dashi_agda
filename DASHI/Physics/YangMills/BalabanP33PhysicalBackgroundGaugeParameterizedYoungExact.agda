module DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact where

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
-- The previous physical theorem fixed the Young parameter at rho and therefore
-- required the stronger radius N(U^-1-1) <= rho^2.  This module proves the
-- exact parameterized inequality.  If
--
--   ||DF_A-DF_1||^2 <= 16 delta ||h||^2,
--   ||DF_1||^2      <= 16       ||h||^2,
--   invEta * eta = 1,
--
-- then
--
--   H_gf(A;h)-H_div^0(h)
--     >= -16 (eta + invEta*delta) ||h||^2.
--
-- The requested conservative -64 rho estimate therefore needs only
--
--   eta = 2 rho,  invEta = 4096,  delta = 4 rho^2,
--
-- rather than delta = rho^2.  The radius premise remains attached to the
-- literal background links; no arbitrary gauge-energy scalar is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeDefectNormSquaredExact as Pointwise
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact as Global
import DASHI.Physics.YangMills.BalabanP33PeriodicDivergenceUpperExact as Divergence
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeSignedLowerExact as Signed
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeResidualExact as Residual

record GaugeYoungParameters : Set where
  field
    eta invEta delta : ℚ
    etaNonnegative : 0ℚ ≤ eta
    invEtaNonnegative : 0ℚ ≤ invEta
    deltaNonnegative : 0ℚ ≤ delta
    reciprocal : invEta * eta ≡ + 1 / 1

open GaugeYoungParameters public

weightedSquare : GaugeYoungParameters → ℚ → ℚ → ℚ
weightedSquare parameters flat defect =
  invEta parameters
    * ((eta parameters * flat + defect)
      * (eta parameters * flat + defect))
  + defect * defect

weightedSquareNonnegative :
  ∀ parameters flat defect →
  0ℚ ≤ weightedSquare parameters flat defect
weightedSquareNonnegative parameters flat defect =
  FiniteL2.addNonnegative
    (Norm.scaleNonnegative
      (invEta parameters)
      (invEtaNonnegative parameters)
      (FiniteL2.squareNonnegative
        (eta parameters * flat + defect)))
    (FiniteL2.squareNonnegative defect)

weightedSquareWithReciprocalExact :
  ∀ parameters flat defect →
  weightedSquare parameters flat defect
  ≡ ((flat + defect) * (flat + defect) - flat * flat)
    + eta parameters * (flat * flat)
    + invEta parameters * (defect * defect)
weightedSquareWithReciprocalExact parameters flat defect =
  let
    expanded :
      weightedSquare parameters flat defect
      ≡ ((flat + defect) * (flat + defect) - flat * flat)
        + eta parameters * (flat * flat)
        + invEta parameters * (defect * defect)
        + (invEta parameters * eta parameters - (+ 1 / 1))
          * (eta parameters * flat * flat
            + (+ 2 / 1) * flat * defect)
    expanded = ℚRing.solve-∀
      (eta parameters) (invEta parameters) flat defect
  in
  trans expanded
    (subst
      (λ product →
        ((flat + defect) * (flat + defect) - flat * flat)
          + eta parameters * (flat * flat)
          + invEta parameters * (defect * defect)
          + (product - (+ 1 / 1))
            * (eta parameters * flat * flat
              + (+ 2 / 1) * flat * defect)
        ≡ ((flat + defect) * (flat + defect) - flat * flat)
          + eta parameters * (flat * flat)
          + invEta parameters * (defect * defect))
      (sym (reciprocal parameters))
      (ℚRing.solve []))

weightedDifferenceLower :
  ∀ parameters flat defect →
  - (eta parameters * (flat * flat))
    - invEta parameters * (defect * defect)
  ≤ (flat + defect) * (flat + defect) - flat * flat
weightedDifferenceLower parameters flat defect =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (weightedSquareWithReciprocalExact parameters flat defect)
      (weightedSquareNonnegative parameters flat defect))

pointwiseGaugeEnergyDifferenceLower :
  ∀ parameters background field site →
  - (eta parameters * Signed.flatGaugePointEnergy field site)
    - invEta parameters
      * Signed.gaugeDefectPointEnergy background field site
  ≤ Signed.backgroundGaugePointEnergy background field site
    - Signed.flatGaugePointEnergy field site
pointwiseGaugeEnergyDifferenceLower parameters background field site
  rewrite Signed.backgroundFirstIsFlatPlusDefect
      background field Coordinates.coordinateX site
        | Signed.backgroundFirstIsFlatPlusDefect
      background field Coordinates.coordinateY site
        | Signed.backgroundFirstIsFlatPlusDefect
      background field Coordinates.coordinateZ site =
  let
    fx = Gauge.flatGaugeFirstFromAxes field
      (pair Coordinates.coordinateX site)
    fy = Gauge.flatGaugeFirstFromAxes field
      (pair Coordinates.coordinateY site)
    fz = Gauge.flatGaugeFirstFromAxes field
      (pair Coordinates.coordinateZ site)

    rx = Pointwise.backgroundGaugeDefectCoordinate
      background field Coordinates.coordinateX site
    ry = Pointwise.backgroundGaugeDefectCoordinate
      background field Coordinates.coordinateY site
    rz = Pointwise.backgroundGaugeDefectCoordinate
      background field Coordinates.coordinateZ site

    combined =
      ℚP.+-mono-≤
        (weightedDifferenceLower parameters fx rx)
        (ℚP.+-mono-≤
          (weightedDifferenceLower parameters fy ry)
          (weightedDifferenceLower parameters fz rz))
  in
  subst
    (λ lower →
      lower
      ≤ Signed.coordinateSquareSum
          (λ coordinate →
            Gauge.flatGaugeFirstFromAxes field (pair coordinate site)
            + Pointwise.backgroundGaugeDefectCoordinate
                background field coordinate site)
        - Signed.flatGaugePointEnergy field site)
    (ℚRing.solve-∀
      (eta parameters) (invEta parameters)
      fx fy fz rx ry rz)
    (subst
      (λ upper →
        (- (eta parameters * (fx * fx))
          - invEta parameters * (rx * rx))
        + ((- (eta parameters * (fy * fy))
          - invEta parameters * (ry * ry))
        + (- (eta parameters * (fz * fz))
          - invEta parameters * (rz * rz)))
        ≤ upper)
      (ℚRing.solve-∀ fx fy fz rx ry rz)
      combined)

backgroundGaugeEnergyDifferenceLower :
  ∀ parameters background field →
  - (eta parameters * Signed.flatGaugeEnergy field)
    - invEta parameters
      * Global.globalGaugeDerivativeDefectEnergy background field
  ≤ Signed.backgroundGaugeEnergy background field
    - Signed.flatGaugeEnergy field
backgroundGaugeEnergyDifferenceLower parameters background field =
  let
    raw =
      Global.sumSitesMonotone
        (λ site →
          - (eta parameters * Signed.flatGaugePointEnergy field site)
          - invEta parameters
            * Signed.gaugeDefectPointEnergy background field site)
        (λ site →
          Signed.backgroundGaugePointEnergy background field site
          - Signed.flatGaugePointEnergy field site)
        (pointwiseGaugeEnergyDifferenceLower
          parameters background field)

    lowerExact :
      Periodic.sumSites
        (λ site →
          - (eta parameters * Signed.flatGaugePointEnergy field site)
          - invEta parameters
            * Signed.gaugeDefectPointEnergy background field site)
      ≡ - (eta parameters * Signed.flatGaugeEnergy field)
        - invEta parameters
          * Global.globalGaugeDerivativeDefectEnergy background field
    lowerExact =
      trans
        (Periodic.sumSitesSubtract
          (λ site →
            - (eta parameters * Signed.flatGaugePointEnergy field site))
          (λ site →
            invEta parameters
              * Signed.gaugeDefectPointEnergy background field site))
        (cong₂ _-_
          (trans
            (Periodic.sumSitesNeg
              (λ site →
                eta parameters * Signed.flatGaugePointEnergy field site))
            (cong -_
              (Periodic.sumSitesScale
                (eta parameters) (Signed.flatGaugePointEnergy field))))
          (Periodic.sumSitesScale
            (invEta parameters)
            (Signed.gaugeDefectPointEnergy background field)))

    upperExact =
      Periodic.sumSitesSubtract
        (Signed.backgroundGaugePointEnergy background field)
        (Signed.flatGaugePointEnergy field)
  in
  subst
    (λ lower →
      lower
      ≤ Signed.backgroundGaugeEnergy background field
        - Signed.flatGaugeEnergy field)
    lowerExact
    (subst
      (λ upper →
        Periodic.sumSites
          (λ site →
            - (eta parameters * Signed.flatGaugePointEnergy field site)
            - invEta parameters
              * Signed.gaugeDefectPointEnergy background field site)
        ≤ upper)
      upperExact raw)

parameterizedGaugeCoefficient : GaugeYoungParameters → ℚ
parameterizedGaugeCoefficient parameters =
  (+ 16 / 1)
    * (eta parameters + invEta parameters * delta parameters)

backgroundGaugeSignedLowerParameterized :
  ∀ parameters background field →
  Global.UniformInverseLinkDefectSq background (delta parameters) →
  - (parameterizedGaugeCoefficient parameters
      * Coordinates.physicalSU2BondNormSq field)
  ≤ Signed.backgroundGaugeEnergy background field
    - Signed.flatGaugeEnergy field
backgroundGaugeSignedLowerParameterized
    parameters background field radius =
  let
    norm = Coordinates.physicalSU2BondNormSq field

    flatUpper : Signed.flatGaugeEnergy field ≤ (+ 16 / 1) * norm
    flatUpper =
      subst
        (λ lower → lower ≤ (+ 16 / 1) * norm)
        (sym (Signed.flatGaugeEnergyIsPhysicalDivergence field))
        (Divergence.physicalPeriodicDivergenceUpper field)

    defectUpper :
      Global.globalGaugeDerivativeDefectEnergy background field
      ≤ (+ 16 / 1) * delta parameters * norm
    defectUpper =
      Global.globalGaugeDerivativeDefectUniformBound
        background field
        (delta parameters)
        (deltaNonnegative parameters)
        radius

    negativeFlat =
      Signed.negativeScaleAntimono
        (eta parameters) (etaNonnegative parameters) flatUpper

    negativeDefect =
      Signed.negativeScaleAntimono
        (invEta parameters) (invEtaNonnegative parameters) defectUpper

    combined = ℚP.+-mono-≤ negativeFlat negativeDefect

    coefficientExact :
      - (parameterizedGaugeCoefficient parameters * norm)
      ≡ - (eta parameters * ((+ 16 / 1) * norm))
        - invEta parameters
          * ((+ 16 / 1) * delta parameters * norm)
    coefficientExact =
      ℚRing.solve-∀
        (eta parameters) (invEta parameters)
        (delta parameters) norm
  in
  ℚP.≤-trans
    (subst
      (λ lower →
        lower
        ≤ - (eta parameters * ((+ 16 / 1) * norm))
          - invEta parameters
            * ((+ 16 / 1) * delta parameters * norm))
      (sym coefficientExact)
      ℚP.≤-refl)
    (ℚP.≤-trans combined
      (backgroundGaugeEnergyDifferenceLower
        parameters background field))

------------------------------------------------------------------------
-- Relaxed radius sufficient for the configured -64 rho budget.
------------------------------------------------------------------------

twoRho invTwoRho fourRhoSquare : ℚ
twoRho = (+ 2 / 1) * Signed.rho
invTwoRho = + 4096 / 1
fourRhoSquare = (+ 4 / 1) * Signed.rhoSquare

relaxedGaugeParameters : GaugeYoungParameters
relaxedGaugeParameters = record
  { eta = twoRho
  ; invEta = invTwoRho
  ; delta = fourRhoSquare
  ; etaNonnegative = ℚP.nonNegative⁻¹ twoRho
  ; invEtaNonnegative = ℚP.nonNegative⁻¹ invTwoRho
  ; deltaNonnegative = ℚP.nonNegative⁻¹ fourRhoSquare
  ; reciprocal = ℚRing.solve []
  }

relaxedCoefficientExact :
  parameterizedGaugeCoefficient relaxedGaugeParameters
  ≡ (+ 64 / 1) * Signed.rho
relaxedCoefficientExact = ℚRing.solve []

RelaxedInverseLinkRadius : Physical.RationalSU2Background4 → Set
RelaxedInverseLinkRadius background =
  Global.UniformInverseLinkDefectSq background fourRhoSquare

backgroundGaugeSignedLowerSixtyFourRelaxed :
  ∀ background field →
  RelaxedInverseLinkRadius background →
  - ((+ 64 / 1) * Signed.rho
      * Coordinates.physicalSU2BondNormSq field)
  ≤ Signed.backgroundGaugeEnergy background field
    - Signed.flatGaugeEnergy field
backgroundGaugeSignedLowerSixtyFourRelaxed background field radius =
  subst
    (λ coefficient →
      - (coefficient * Coordinates.physicalSU2BondNormSq field)
      ≤ Signed.backgroundGaugeEnergy background field
        - Signed.flatGaugeEnergy field)
    relaxedCoefficientExact
    (backgroundGaugeSignedLowerParameterized
      relaxedGaugeParameters background field radius)

backgroundGaugeResidualSignedLowerSixtyFourRelaxed :
  ∀ background field →
  RelaxedInverseLinkRadius background →
  - ((+ 64 / 1) * Signed.rho
      * Coordinates.physicalSU2BondNormSq field)
  ≤ Jets.residualSecondVariation
      (Residual.backgroundGaugeResidual background field)
      - Periodic.physicalPeriodicDivergenceEnergy field
backgroundGaugeResidualSignedLowerSixtyFourRelaxed
    background field radius =
  subst
    (λ left →
      - ((+ 64 / 1) * Signed.rho
          * Coordinates.physicalSU2BondNormSq field)
      ≤ left - Periodic.physicalPeriodicDivergenceEnergy field)
    (sym
      (Residual.backgroundGaugeResidualSecondVariationIsEnergy
        background field))
    (subst
      (λ right →
        - ((+ 64 / 1) * Signed.rho
            * Coordinates.physicalSU2BondNormSq field)
        ≤ Signed.backgroundGaugeEnergy background field - right)
      (Signed.flatGaugeEnergyIsPhysicalDivergence field)
      (backgroundGaugeSignedLowerSixtyFourRelaxed
        background field radius))

physicalGaugeParameterizedYoungLevel : ProofLevel
physicalGaugeParameterizedYoungLevel = machineChecked

physicalGaugeRelaxedSixtyFourLevel : ProofLevel
physicalGaugeRelaxedSixtyFourLevel = machineChecked

physicalRelaxedInverseLinkRadiusProducerLevel : ProofLevel
physicalRelaxedInverseLinkRadiusProducerLevel = conditional
