module DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeSignedLowerExact where

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
-- Close the signed algebra of the physical background-gauge defect.  Under the
-- explicit link-radius hypothesis
--
--   N(U_b^-1-1) <= rho^2,       rho = 1/8192,
--
-- the preceding exact modules give
--
--   ||D F_A-D F_1||^2 <= 16 rho^2 ||h||^2,
--   ||D F_1||^2       <= 16       ||h||^2.
--
-- The exact rational weighted-square identity
--
--   (v+r)^2-v^2 >= -rho v^2-rho^-1 r^2
--
-- then yields the stronger signed estimate
--
--   H_gf(A;h)-H_div^0(h) >= -32 rho ||h||^2,
--
-- and hence the requested conservative bound
--
--   H_gf(A;h)-H_div^0(h) >= -64 rho ||h||^2.
--
-- The physical field is stored on positive bonds `(site,axis)`.  Every use of
-- the periodic divergence now passes through the repository's explicit
-- carrier bridge to the curried representation `axis -> site`; the two
-- representations are isomorphic but not definitionally equal.
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
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeDefectNormSquaredExact as Pointwise
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact as Global
import DASHI.Physics.YangMills.BalabanP33PeriodicDivergenceUpperExact as Divergence

rho invRho : ℚ
rho = + 1 / 8192
invRho = + 8192 / 1

rhoNonnegative : 0ℚ ≤ rho
rhoNonnegative = ℚP.nonNegative⁻¹ rho

invRhoNonnegative : 0ℚ ≤ invRho
invRhoNonnegative = ℚP.nonNegative⁻¹ invRho

rhoSquare : ℚ
rhoSquare = rho * rho

rhoSquareNonnegative : 0ℚ ≤ rhoSquare
rhoSquareNonnegative = FiniteL2.squareNonnegative rho

------------------------------------------------------------------------
-- Exact finite positive sums and physical norm nonnegativity.
------------------------------------------------------------------------

sumIndex4Nonnegative : ∀ term →
  (∀ index → 0ℚ ≤ term index) →
  0ℚ ≤ Periodic.sumIndex4 term
sumIndex4Nonnegative term pointwise =
  FiniteL2.addNonnegative
    (pointwise Periodic.index0)
    (FiniteL2.addNonnegative
      (pointwise Periodic.index1)
      (FiniteL2.addNonnegative
        (pointwise Periodic.index2)
        (FiniteL2.addNonnegative
          (pointwise Periodic.index3)
          ℚP.≤-refl)))

sumSitesNonnegative : ∀ term →
  (∀ site → 0ℚ ≤ term site) →
  0ℚ ≤ Periodic.sumSites term
sumSitesNonnegative term pointwise =
  sumIndex4Nonnegative _ (λ x0 →
    sumIndex4Nonnegative _ (λ x1 →
      sumIndex4Nonnegative _ (λ x2 →
        sumIndex4Nonnegative _ (λ x3 →
          pointwise (pair (pair x0 x1) (pair x2 x3))))))

axisInsertionNormSqNonnegative : ∀ field axis →
  0ℚ ≤ Global.axisInsertionNormSq field axis
axisInsertionNormSqNonnegative field axis =
  sumSitesNonnegative _
    (λ site → Norm.normSqNonnegative
      (Gauge.insertionQuaternion field axis site))

periodicPhysicalBondNormSqNonnegative : ∀ field →
  0ℚ ≤ Global.periodicPhysicalBondNormSq field
periodicPhysicalBondNormSqNonnegative field =
  FiniteL2.addNonnegative
    (axisInsertionNormSqNonnegative field Periodic.axis0)
    (FiniteL2.addNonnegative
      (axisInsertionNormSqNonnegative field Periodic.axis1)
      (FiniteL2.addNonnegative
        (axisInsertionNormSqNonnegative field Periodic.axis2)
        (axisInsertionNormSqNonnegative field Periodic.axis3)))

physicalBondNormSqNonnegative : ∀ field →
  0ℚ ≤ Coordinates.physicalSU2BondNormSq field
physicalBondNormSqNonnegative field =
  subst
    (λ selected → 0ℚ ≤ selected)
    (Global.periodicPhysicalBondNormSqExact field)
    (periodicPhysicalBondNormSqNonnegative field)

------------------------------------------------------------------------
-- Literal gauge energies on the periodic physical carrier.
------------------------------------------------------------------------

coordinateSquareSum : (Coordinates.LieCoordinate3 → ℚ) → ℚ
coordinateSquareSum values =
  values Coordinates.coordinateX * values Coordinates.coordinateX
  + values Coordinates.coordinateY * values Coordinates.coordinateY
  + values Coordinates.coordinateZ * values Coordinates.coordinateZ

backgroundGaugePointEnergy :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Periodic.Site4 → ℚ
backgroundGaugePointEnergy background field site =
  coordinateSquareSum
    (λ coordinate →
      Gauge.backgroundGaugeFirst background field (pair coordinate site))

flatGaugePointEnergy :
  Coordinates.PhysicalSU2BondField4 → Periodic.Site4 → ℚ
flatGaugePointEnergy field site =
  coordinateSquareSum
    (λ coordinate →
      Gauge.flatGaugeFirstFromAxes field (pair coordinate site))

gaugeDefectPointEnergy :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Periodic.Site4 → ℚ
gaugeDefectPointEnergy = Pointwise.pointwiseGaugeDefectEnergy

backgroundGaugeEnergy :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → ℚ
backgroundGaugeEnergy background field =
  Periodic.sumSites (backgroundGaugePointEnergy background field)

flatGaugeEnergy : Coordinates.PhysicalSU2BondField4 → ℚ
flatGaugeEnergy field = Periodic.sumSites (flatGaugePointEnergy field)

flatGaugePointIsPeriodicDivergence :
  ∀ field site →
  flatGaugePointEnergy field site
  ≡
    Periodic.periodicDivergence
      (Bridge.asPeriodicField field Coordinates.coordinateX) site
      * Periodic.periodicDivergence
          (Bridge.asPeriodicField field Coordinates.coordinateX) site
    + Periodic.periodicDivergence
        (Bridge.asPeriodicField field Coordinates.coordinateY) site
      * Periodic.periodicDivergence
          (Bridge.asPeriodicField field Coordinates.coordinateY) site
    + Periodic.periodicDivergence
        (Bridge.asPeriodicField field Coordinates.coordinateZ) site
      * Periodic.periodicDivergence
          (Bridge.asPeriodicField field Coordinates.coordinateZ) site
flatGaugePointIsPeriodicDivergence field site
  rewrite Gauge.flatGaugeFirstFromAxesIsPeriodicDivergence
      field Coordinates.coordinateX site
        | Gauge.flatGaugeFirstFromAxesIsPeriodicDivergence
      field Coordinates.coordinateY site
        | Gauge.flatGaugeFirstFromAxesIsPeriodicDivergence
      field Coordinates.coordinateZ site =
  refl

flatGaugeEnergyIsPhysicalDivergence : ∀ field →
  flatGaugeEnergy field
  ≡ Periodic.physicalPeriodicDivergenceEnergy
      (Bridge.asPeriodicField field)
flatGaugeEnergyIsPhysicalDivergence field =
  trans
    (Periodic.sumSitesCong _ _
      (flatGaugePointIsPeriodicDivergence field))
    (trans
      (Periodic.sumSitesAdd
        (λ site →
          Periodic.periodicDivergence
            (Bridge.asPeriodicField field Coordinates.coordinateX) site
          * Periodic.periodicDivergence
            (Bridge.asPeriodicField field Coordinates.coordinateX) site)
        (λ site →
          Periodic.periodicDivergence
            (Bridge.asPeriodicField field Coordinates.coordinateY) site
            * Periodic.periodicDivergence
              (Bridge.asPeriodicField field Coordinates.coordinateY) site
          + Periodic.periodicDivergence
              (Bridge.asPeriodicField field Coordinates.coordinateZ) site
            * Periodic.periodicDivergence
              (Bridge.asPeriodicField field Coordinates.coordinateZ) site))
      (cong₂ _+_ refl
        (Periodic.sumSitesAdd
          (λ site →
            Periodic.periodicDivergence
              (Bridge.asPeriodicField field Coordinates.coordinateY) site
            * Periodic.periodicDivergence
              (Bridge.asPeriodicField field Coordinates.coordinateY) site)
          (λ site →
            Periodic.periodicDivergence
              (Bridge.asPeriodicField field Coordinates.coordinateZ) site
            * Periodic.periodicDivergence
              (Bridge.asPeriodicField field Coordinates.coordinateZ) site))))

------------------------------------------------------------------------
-- Weighted scalar Young inequality at the configured rational radius.
------------------------------------------------------------------------

weightedGaugeSquareNonnegative : ∀ flat defect →
  0ℚ ≤ invRho * ((rho * flat + defect) * (rho * flat + defect))
    + defect * defect
weightedGaugeSquareNonnegative flat defect =
  FiniteL2.addNonnegative
    (Norm.scaleNonnegative invRho invRhoNonnegative
      (FiniteL2.squareNonnegative (rho * flat + defect)))
    (FiniteL2.squareNonnegative defect)

weightedGaugeDifferenceLower : ∀ flat defect →
  - (rho * (flat * flat)) - invRho * (defect * defect)
  ≤ (flat + defect) * (flat + defect) - flat * flat
weightedGaugeDifferenceLower flat defect =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (ℚRing.solve-∀ flat defect)
      (weightedGaugeSquareNonnegative flat defect))

backgroundFirstIsFlatPlusDefect :
  ∀ background field coordinate site →
  Gauge.backgroundGaugeFirst background field (pair coordinate site)
  ≡ Gauge.flatGaugeFirstFromAxes field (pair coordinate site)
    + Pointwise.backgroundGaugeDefectCoordinate
        background field coordinate site
backgroundFirstIsFlatPlusDefect background field coordinate site =
  ℚRing.solve-∀
    (Gauge.backgroundGaugeFirst background field (pair coordinate site))
    (Gauge.flatGaugeFirstFromAxes field (pair coordinate site))

pointwiseGaugeEnergyDifferenceLower :
  ∀ background field site →
  - (rho * flatGaugePointEnergy field site)
    - invRho * gaugeDefectPointEnergy background field site
  ≤ backgroundGaugePointEnergy background field site
    - flatGaugePointEnergy field site
pointwiseGaugeEnergyDifferenceLower background field site
  rewrite backgroundFirstIsFlatPlusDefect
      background field Coordinates.coordinateX site
        | backgroundFirstIsFlatPlusDefect
      background field Coordinates.coordinateY site
        | backgroundFirstIsFlatPlusDefect
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
        (weightedGaugeDifferenceLower fx rx)
        (ℚP.+-mono-≤
          (weightedGaugeDifferenceLower fy ry)
          (weightedGaugeDifferenceLower fz rz))
  in
  subst
    (λ lower →
      lower
      ≤ coordinateSquareSum
          (λ coordinate →
            Gauge.flatGaugeFirstFromAxes field (pair coordinate site)
            + Pointwise.backgroundGaugeDefectCoordinate
                background field coordinate site)
        - flatGaugePointEnergy field site)
    (ℚRing.solve-∀ fx fy fz rx ry rz)
    (subst
      (λ upper →
        (- (rho * (fx * fx)) - invRho * (rx * rx))
        + ((- (rho * (fy * fy)) - invRho * (ry * ry))
        + (- (rho * (fz * fz)) - invRho * (rz * rz)))
        ≤ upper)
      (ℚRing.solve-∀ fx fy fz rx ry rz)
      combined)

backgroundGaugeEnergyDifferenceLower : ∀ background field →
  - (rho * flatGaugeEnergy field)
    - invRho * Global.globalGaugeDerivativeDefectEnergy background field
  ≤ backgroundGaugeEnergy background field - flatGaugeEnergy field
backgroundGaugeEnergyDifferenceLower background field =
  let
    raw :
      Periodic.sumSites
        (λ site →
          - (rho * flatGaugePointEnergy field site)
          - invRho * gaugeDefectPointEnergy background field site)
      ≤ Periodic.sumSites
          (λ site →
            backgroundGaugePointEnergy background field site
            - flatGaugePointEnergy field site)
    raw =
      Global.sumSitesMonotone _ _
        (pointwiseGaugeEnergyDifferenceLower background field)

    lowerExact :
      Periodic.sumSites
        (λ site →
          - (rho * flatGaugePointEnergy field site)
          - invRho * gaugeDefectPointEnergy background field site)
      ≡ - (rho * flatGaugeEnergy field)
        - invRho * Global.globalGaugeDerivativeDefectEnergy background field
    lowerExact =
      trans
        (Periodic.sumSitesSubtract
          (λ site → - (rho * flatGaugePointEnergy field site))
          (λ site → invRho * gaugeDefectPointEnergy background field site))
        (cong₂ _-_
          (trans
            (Periodic.sumSitesNeg
              (λ site → rho * flatGaugePointEnergy field site))
            (cong -_
              (Periodic.sumSitesScale rho
                (flatGaugePointEnergy field))))
          (Periodic.sumSitesScale invRho
            (gaugeDefectPointEnergy background field)))

    upperExact :
      Periodic.sumSites
        (λ site →
          backgroundGaugePointEnergy background field site
          - flatGaugePointEnergy field site)
      ≡ backgroundGaugeEnergy background field - flatGaugeEnergy field
    upperExact =
      Periodic.sumSitesSubtract
        (backgroundGaugePointEnergy background field)
        (flatGaugePointEnergy field)
  in
  subst
    (λ lower →
      lower ≤ backgroundGaugeEnergy background field - flatGaugeEnergy field)
    lowerExact
    (subst
      (λ upper →
        Periodic.sumSites
          (λ site →
            - (rho * flatGaugePointEnergy field site)
            - invRho * gaugeDefectPointEnergy background field site)
        ≤ upper)
      upperExact raw)

------------------------------------------------------------------------
-- Strong and conservative signed physical bounds.
------------------------------------------------------------------------

ConfiguredInverseLinkRadius : Physical.RationalSU2Background4 → Set
ConfiguredInverseLinkRadius background =
  Global.UniformInverseLinkDefectSq background rhoSquare

negativeScaleAntimono : ∀ scale {left right} →
  0ℚ ≤ scale → left ≤ right →
  - (scale * right) ≤ - (scale * left)
negativeScaleAntimono scale scaleNonnegative leftBelowRight =
  ℚP.neg-antimono-≤
    (Norm.scaleNonnegative scale scaleNonnegative leftBelowRight)

backgroundGaugeSignedLowerThirtyTwo :
  ∀ background field →
  ConfiguredInverseLinkRadius background →
  - ((+ 32 / 1) * rho * Coordinates.physicalSU2BondNormSq field)
  ≤ backgroundGaugeEnergy background field - flatGaugeEnergy field
backgroundGaugeSignedLowerThirtyTwo background field radius =
  let
    norm = Coordinates.physicalSU2BondNormSq field

    flatUpper : flatGaugeEnergy field ≤ (+ 16 / 1) * norm
    flatUpper =
      subst
        (λ lower → lower ≤ (+ 16 / 1) * norm)
        (sym (flatGaugeEnergyIsPhysicalDivergence field))
        (Divergence.physicalPeriodicDivergenceUpper field)

    defectUpper :
      Global.globalGaugeDerivativeDefectEnergy background field
      ≤ (+ 16 / 1) * rhoSquare * norm
    defectUpper =
      Global.globalGaugeDerivativeDefectUniformBound
        background field rhoSquare rhoSquareNonnegative radius

    negativeFlat :
      - (rho * ((+ 16 / 1) * norm))
      ≤ - (rho * flatGaugeEnergy field)
    negativeFlat = negativeScaleAntimono rho rhoNonnegative flatUpper

    negativeDefect :
      - (invRho * ((+ 16 / 1) * rhoSquare * norm))
      ≤ - (invRho
        * Global.globalGaugeDerivativeDefectEnergy background field)
    negativeDefect =
      negativeScaleAntimono invRho invRhoNonnegative defectUpper

    combinedNegative :
      - (rho * ((+ 16 / 1) * norm))
        - invRho * ((+ 16 / 1) * rhoSquare * norm)
      ≤ - (rho * flatGaugeEnergy field)
        - invRho
          * Global.globalGaugeDerivativeDefectEnergy background field
    combinedNegative = ℚP.+-mono-≤ negativeFlat negativeDefect

    algebra :
      - ((+ 32 / 1) * rho * norm)
      ≡ - (rho * ((+ 16 / 1) * norm))
        - invRho * ((+ 16 / 1) * rhoSquare * norm)
    algebra = ℚRing.solve-∀ norm

    algebraLower :
      - ((+ 32 / 1) * rho * norm)
      ≤ - (rho * ((+ 16 / 1) * norm))
        - invRho * ((+ 16 / 1) * rhoSquare * norm)
    algebraLower =
      subst
        (λ lower →
          lower
          ≤ - (rho * ((+ 16 / 1) * norm))
            - invRho * ((+ 16 / 1) * rhoSquare * norm))
        (sym algebra)
        ℚP.≤-refl
  in
  ℚP.≤-trans algebraLower
    (ℚP.≤-trans combinedNegative
      (backgroundGaugeEnergyDifferenceLower background field))

backgroundGaugeSignedLowerSixtyFour :
  ∀ background field →
  ConfiguredInverseLinkRadius background →
  - ((+ 64 / 1) * rho * Coordinates.physicalSU2BondNormSq field)
  ≤ backgroundGaugeEnergy background field - flatGaugeEnergy field
backgroundGaugeSignedLowerSixtyFour background field radius =
  let
    norm = Coordinates.physicalSU2BondNormSq field

    weakerToStronger :
      - ((+ 64 / 1) * rho * norm)
      ≤ - ((+ 32 / 1) * rho * norm)
    weakerToStronger =
      Norm.nonnegativeDifferenceImpliesBelow
        (subst
          (λ selected → 0ℚ ≤ selected)
          (ℚRing.solve-∀ norm)
          (Norm.scaleNonnegative
            ((+ 32 / 1) * rho)
            (ℚP.nonNegative⁻¹ ((+ 32 / 1) * rho))
            (physicalBondNormSqNonnegative field)))
  in
  ℚP.≤-trans weakerToStronger
    (backgroundGaugeSignedLowerThirtyTwo background field radius)

physicalGaugeWeightedYoungLevel : ProofLevel
physicalGaugeWeightedYoungLevel = machineChecked

physicalBackgroundGaugeSignedThirtyTwoLevel : ProofLevel
physicalBackgroundGaugeSignedThirtyTwoLevel = machineChecked

physicalBackgroundGaugeSignedSixtyFourLevel : ProofLevel
physicalBackgroundGaugeSignedSixtyFourLevel = machineChecked

physicalConfiguredInverseLinkRadiusProducerLevel : ProofLevel
physicalConfiguredInverseLinkRadiusProducerLevel = conditional
