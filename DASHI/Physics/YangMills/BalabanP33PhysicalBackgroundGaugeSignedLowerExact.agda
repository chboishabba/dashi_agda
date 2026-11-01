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

axisInsertionNormSqNonnegative : ∀ fieldValue axis →
  0ℚ ≤ Global.axisInsertionNormSq fieldValue axis
axisInsertionNormSqNonnegative fieldValue axis =
  sumSitesNonnegative _
    (λ site → Norm.normSqNonnegative
      (Gauge.insertionQuaternion fieldValue axis site))

periodicPhysicalBondNormSqNonnegative : ∀ fieldValue →
  0ℚ ≤ Global.periodicPhysicalBondNormSq fieldValue
periodicPhysicalBondNormSqNonnegative fieldValue =
  FiniteL2.addNonnegative
    (axisInsertionNormSqNonnegative fieldValue Periodic.axis0)
    (FiniteL2.addNonnegative
      (axisInsertionNormSqNonnegative fieldValue Periodic.axis1)
      (FiniteL2.addNonnegative
        (axisInsertionNormSqNonnegative fieldValue Periodic.axis2)
        (axisInsertionNormSqNonnegative fieldValue Periodic.axis3)))

physicalBondNormSqNonnegative : ∀ fieldValue →
  0ℚ ≤ Coordinates.physicalSU2BondNormSq fieldValue
physicalBondNormSqNonnegative fieldValue =
  subst
    (λ selected → 0ℚ ≤ selected)
    (Global.periodicPhysicalBondNormSqExact fieldValue)
    (periodicPhysicalBondNormSqNonnegative fieldValue)

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
backgroundGaugePointEnergy background fieldValue site =
  coordinateSquareSum
    (λ coordinate →
      Gauge.backgroundGaugeFirst background fieldValue (pair coordinate site))

flatGaugePointEnergy :
  Coordinates.PhysicalSU2BondField4 → Periodic.Site4 → ℚ
flatGaugePointEnergy fieldValue site =
  coordinateSquareSum
    (λ coordinate →
      Gauge.flatGaugeFirstFromAxes fieldValue (pair coordinate site))

gaugeDefectPointEnergy :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Periodic.Site4 → ℚ
gaugeDefectPointEnergy = Pointwise.pointwiseGaugeDefectEnergy

backgroundGaugeEnergy :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → ℚ
backgroundGaugeEnergy background fieldValue =
  Periodic.sumSites (backgroundGaugePointEnergy background fieldValue)

flatGaugeEnergy : Coordinates.PhysicalSU2BondField4 → ℚ
flatGaugeEnergy fieldValue = Periodic.sumSites (flatGaugePointEnergy fieldValue)

flatGaugePointIsPeriodicDivergence :
  ∀ fieldValue site →
  flatGaugePointEnergy fieldValue site
  ≡
    Periodic.periodicDivergence
      (Bridge.asPeriodicField fieldValue Coordinates.coordinateX) site
      * Periodic.periodicDivergence
          (Bridge.asPeriodicField fieldValue Coordinates.coordinateX) site
    + Periodic.periodicDivergence
        (Bridge.asPeriodicField fieldValue Coordinates.coordinateY) site
      * Periodic.periodicDivergence
          (Bridge.asPeriodicField fieldValue Coordinates.coordinateY) site
    + Periodic.periodicDivergence
        (Bridge.asPeriodicField fieldValue Coordinates.coordinateZ) site
      * Periodic.periodicDivergence
          (Bridge.asPeriodicField fieldValue Coordinates.coordinateZ) site
flatGaugePointIsPeriodicDivergence fieldValue site
  rewrite Gauge.flatGaugeFirstFromAxesIsPeriodicDivergence
      fieldValue Coordinates.coordinateX site
        | Gauge.flatGaugeFirstFromAxesIsPeriodicDivergence
      fieldValue Coordinates.coordinateY site
        | Gauge.flatGaugeFirstFromAxesIsPeriodicDivergence
      fieldValue Coordinates.coordinateZ site =
  refl

flatGaugeEnergyIsPhysicalDivergence : ∀ fieldValue →
  flatGaugeEnergy fieldValue
  ≡ Periodic.physicalPeriodicDivergenceEnergy
      (Bridge.asPeriodicField fieldValue)
flatGaugeEnergyIsPhysicalDivergence fieldValue =
  trans
    (Periodic.sumSitesCong _ _
      (flatGaugePointIsPeriodicDivergence fieldValue))
    (trans
      (Periodic.sumSitesAdd
        (λ site →
          Periodic.periodicDivergence
            (Bridge.asPeriodicField fieldValue Coordinates.coordinateX) site
          * Periodic.periodicDivergence
            (Bridge.asPeriodicField fieldValue Coordinates.coordinateX) site)
        (λ site →
          Periodic.periodicDivergence
            (Bridge.asPeriodicField fieldValue Coordinates.coordinateY) site
            * Periodic.periodicDivergence
              (Bridge.asPeriodicField fieldValue Coordinates.coordinateY) site
          + Periodic.periodicDivergence
              (Bridge.asPeriodicField fieldValue Coordinates.coordinateZ) site
            * Periodic.periodicDivergence
              (Bridge.asPeriodicField fieldValue Coordinates.coordinateZ) site))
      (cong₂ _+_ refl
        (Periodic.sumSitesAdd
          (λ site →
            Periodic.periodicDivergence
              (Bridge.asPeriodicField fieldValue Coordinates.coordinateY) site
            * Periodic.periodicDivergence
              (Bridge.asPeriodicField fieldValue Coordinates.coordinateY) site)
          (λ site →
            Periodic.periodicDivergence
              (Bridge.asPeriodicField fieldValue Coordinates.coordinateZ) site
            * Periodic.periodicDivergence
              (Bridge.asPeriodicField fieldValue Coordinates.coordinateZ) site))))

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
  ∀ background fieldValue coordinate site →
  Gauge.backgroundGaugeFirst background fieldValue (pair coordinate site)
  ≡ Gauge.flatGaugeFirstFromAxes fieldValue (pair coordinate site)
    + Pointwise.backgroundGaugeDefectCoordinate
        background fieldValue coordinate site
backgroundFirstIsFlatPlusDefect background fieldValue coordinate site =
  ℚRing.solve-∀
    (Gauge.backgroundGaugeFirst background fieldValue (pair coordinate site))
    (Gauge.flatGaugeFirstFromAxes fieldValue (pair coordinate site))

pointwiseGaugeEnergyDifferenceLower :
  ∀ background fieldValue site →
  - (rho * flatGaugePointEnergy fieldValue site)
    - invRho * gaugeDefectPointEnergy background fieldValue site
  ≤ backgroundGaugePointEnergy background fieldValue site
    - flatGaugePointEnergy fieldValue site
pointwiseGaugeEnergyDifferenceLower background fieldValue site
  rewrite backgroundFirstIsFlatPlusDefect
      background fieldValue Coordinates.coordinateX site
        | backgroundFirstIsFlatPlusDefect
      background fieldValue Coordinates.coordinateY site
        | backgroundFirstIsFlatPlusDefect
      background fieldValue Coordinates.coordinateZ site =
  let
    fx = Gauge.flatGaugeFirstFromAxes fieldValue
      (pair Coordinates.coordinateX site)
    fy = Gauge.flatGaugeFirstFromAxes fieldValue
      (pair Coordinates.coordinateY site)
    fz = Gauge.flatGaugeFirstFromAxes fieldValue
      (pair Coordinates.coordinateZ site)

    rx = Pointwise.backgroundGaugeDefectCoordinate
      background fieldValue Coordinates.coordinateX site
    ry = Pointwise.backgroundGaugeDefectCoordinate
      background fieldValue Coordinates.coordinateY site
    rz = Pointwise.backgroundGaugeDefectCoordinate
      background fieldValue Coordinates.coordinateZ site

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
            Gauge.flatGaugeFirstFromAxes fieldValue (pair coordinate site)
            + Pointwise.backgroundGaugeDefectCoordinate
                background fieldValue coordinate site)
        - flatGaugePointEnergy fieldValue site)
    (ℚRing.solve-∀ fx fy fz rx ry rz)
    (subst
      (λ upper →
        (- (rho * (fx * fx)) - invRho * (rx * rx))
        + ((- (rho * (fy * fy)) - invRho * (ry * ry))
        + (- (rho * (fz * fz)) - invRho * (rz * rz)))
        ≤ upper)
      (ℚRing.solve-∀ fx fy fz rx ry rz)
      combined)

backgroundGaugeEnergyDifferenceLower : ∀ background fieldValue →
  - (rho * flatGaugeEnergy fieldValue)
    - invRho * Global.globalGaugeDerivativeDefectEnergy background fieldValue
  ≤ backgroundGaugeEnergy background fieldValue - flatGaugeEnergy fieldValue
backgroundGaugeEnergyDifferenceLower background fieldValue =
  let
    raw :
      Periodic.sumSites
        (λ site →
          - (rho * flatGaugePointEnergy fieldValue site)
          - invRho * gaugeDefectPointEnergy background fieldValue site)
      ≤ Periodic.sumSites
          (λ site →
            backgroundGaugePointEnergy background fieldValue site
            - flatGaugePointEnergy fieldValue site)
    raw =
      Global.sumSitesMonotone _ _
        (pointwiseGaugeEnergyDifferenceLower background fieldValue)

    lowerExact :
      Periodic.sumSites
        (λ site →
          - (rho * flatGaugePointEnergy fieldValue site)
          - invRho * gaugeDefectPointEnergy background fieldValue site)
      ≡ - (rho * flatGaugeEnergy fieldValue)
        - invRho * Global.globalGaugeDerivativeDefectEnergy background fieldValue
    lowerExact =
      trans
        (Periodic.sumSitesSubtract
          (λ site → - (rho * flatGaugePointEnergy fieldValue site))
          (λ site → invRho * gaugeDefectPointEnergy background fieldValue site))
        (cong₂ _-_
          (trans
            (Periodic.sumSitesNeg
              (λ site → rho * flatGaugePointEnergy fieldValue site))
            (cong -_
              (Periodic.sumSitesScale rho
                (flatGaugePointEnergy fieldValue))))
          (Periodic.sumSitesScale invRho
            (gaugeDefectPointEnergy background fieldValue)))

    upperExact :
      Periodic.sumSites
        (λ site →
          backgroundGaugePointEnergy background fieldValue site
          - flatGaugePointEnergy fieldValue site)
      ≡ backgroundGaugeEnergy background fieldValue - flatGaugeEnergy fieldValue
    upperExact =
      Periodic.sumSitesSubtract
        (backgroundGaugePointEnergy background fieldValue)
        (flatGaugePointEnergy fieldValue)
  in
  subst
    (λ lower →
      lower ≤ backgroundGaugeEnergy background fieldValue - flatGaugeEnergy fieldValue)
    lowerExact
    (subst
      (λ upper →
        Periodic.sumSites
          (λ site →
            - (rho * flatGaugePointEnergy fieldValue site)
            - invRho * gaugeDefectPointEnergy background fieldValue site)
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
  ∀ background fieldValue →
  ConfiguredInverseLinkRadius background →
  - ((+ 32 / 1) * rho * Coordinates.physicalSU2BondNormSq fieldValue)
  ≤ backgroundGaugeEnergy background fieldValue - flatGaugeEnergy fieldValue
backgroundGaugeSignedLowerThirtyTwo background fieldValue radius =
  let
    norm = Coordinates.physicalSU2BondNormSq fieldValue

    flatUpper : flatGaugeEnergy fieldValue ≤ (+ 16 / 1) * norm
    flatUpper =
      subst
        (λ lower → lower ≤ (+ 16 / 1) * norm)
        (sym (flatGaugeEnergyIsPhysicalDivergence fieldValue))
        (Divergence.physicalPeriodicDivergenceUpper fieldValue)

    defectUpper :
      Global.globalGaugeDerivativeDefectEnergy background fieldValue
      ≤ (+ 16 / 1) * rhoSquare * norm
    defectUpper =
      Global.globalGaugeDerivativeDefectUniformBound
        background fieldValue rhoSquare rhoSquareNonnegative radius

    negativeFlat :
      - (rho * ((+ 16 / 1) * norm))
      ≤ - (rho * flatGaugeEnergy fieldValue)
    negativeFlat = negativeScaleAntimono rho rhoNonnegative flatUpper

    negativeDefect :
      - (invRho * ((+ 16 / 1) * rhoSquare * norm))
      ≤ - (invRho
        * Global.globalGaugeDerivativeDefectEnergy background fieldValue)
    negativeDefect =
      negativeScaleAntimono invRho invRhoNonnegative defectUpper

    combinedNegative :
      - (rho * ((+ 16 / 1) * norm))
        - invRho * ((+ 16 / 1) * rhoSquare * norm)
      ≤ - (rho * flatGaugeEnergy fieldValue)
        - invRho
          * Global.globalGaugeDerivativeDefectEnergy background fieldValue
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
      (backgroundGaugeEnergyDifferenceLower background fieldValue))

backgroundGaugeSignedLowerSixtyFour :
  ∀ background fieldValue →
  ConfiguredInverseLinkRadius background →
  - ((+ 64 / 1) * rho * Coordinates.physicalSU2BondNormSq fieldValue)
  ≤ backgroundGaugeEnergy background fieldValue - flatGaugeEnergy fieldValue
backgroundGaugeSignedLowerSixtyFour background fieldValue radius =
  let
    norm = Coordinates.physicalSU2BondNormSq fieldValue

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
            (physicalBondNormSqNonnegative fieldValue)))
  in
  ℚP.≤-trans weakerToStronger
    (backgroundGaugeSignedLowerThirtyTwo background fieldValue radius)

physicalGaugeWeightedYoungLevel : ProofLevel
physicalGaugeWeightedYoungLevel = machineChecked

physicalBackgroundGaugeSignedThirtyTwoLevel : ProofLevel
physicalBackgroundGaugeSignedThirtyTwoLevel = machineChecked

physicalBackgroundGaugeSignedSixtyFourLevel : ProofLevel
physicalBackgroundGaugeSignedSixtyFourLevel = machineChecked

physicalConfiguredInverseLinkRadiusProducerLevel : ProofLevel
physicalConfiguredInverseLinkRadiusProducerLevel = conditional
