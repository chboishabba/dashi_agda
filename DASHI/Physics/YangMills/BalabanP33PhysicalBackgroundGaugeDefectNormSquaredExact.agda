module DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeDefectNormSquaredExact where

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
-- Convert the literal background-gauge derivative defect into a concrete
-- pointwise norm-square estimate.  At each site, let d_mu be the exact
-- quaternion adjoint defect on the transported predecessor bond.  Then
--
--   sum_a |(DF_A-DF_1)^a(x)|^2
--     <= N(d_0+d_1+d_2+d_3)
--     <= 4 sum_mu N(d_mu)
--     <= 16 sum_mu N(U_mu(x-mu)^-1-1) N(h_mu(x-mu)).
--
-- Every inequality is over exact rationals and is connected to the literal
-- gauge derivative.  What remains for G-local is the global periodic
-- reindexing, a uniform selected-background link-defect radius, and the signed
-- comparison of squared gauge energies.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointNormSquaredExact as AdjointNorm
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge

axisDefect0 axisDefect1 axisDefect2 axisDefect3 :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Site4 → Q.RationalQuaternion
axisDefect0 background fieldValue site =
  Gauge.axisAdjointDefect background fieldValue Periodic.axis0 site
axisDefect1 background fieldValue site =
  Gauge.axisAdjointDefect background fieldValue Periodic.axis1 site
axisDefect2 background fieldValue site =
  Gauge.axisAdjointDefect background fieldValue Periodic.axis2 site
axisDefect3 background fieldValue site =
  Gauge.axisAdjointDefect background fieldValue Periodic.axis3 site

axisDefectSum :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Site4 → Q.RationalQuaternion
axisDefectSum background fieldValue site =
  axisDefect0 background fieldValue site Q.+q
    (axisDefect1 background fieldValue site Q.+q
      (axisDefect2 background fieldValue site Q.+q
        axisDefect3 background fieldValue site))

coordinateSum4Exact :
  ∀ coordinate first second third fourth →
  Gauge.quaternionCoordinate coordinate
    (first Q.+q (second Q.+q (third Q.+q fourth)))
  ≡ Gauge.quaternionCoordinate coordinate first
    + Gauge.quaternionCoordinate coordinate second
    + Gauge.quaternionCoordinate coordinate third
    + Gauge.quaternionCoordinate coordinate fourth
coordinateSum4Exact Coordinates.coordinateX
    (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)
    (Q.quat c0 c1 c2 c3) (Q.quat d0 d1 d2 d3) =
  ℚRing.solve-∀ a1 b1 c1 d1
coordinateSum4Exact Coordinates.coordinateY
    (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)
    (Q.quat c0 c1 c2 c3) (Q.quat d0 d1 d2 d3) =
  ℚRing.solve-∀ a2 b2 c2 d2
coordinateSum4Exact Coordinates.coordinateZ
    (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)
    (Q.quat c0 c1 c2 c3) (Q.quat d0 d1 d2 d3) =
  ℚRing.solve-∀ a3 b3 c3 d3

backgroundGaugeDefectCoordinate :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Coordinates.LieCoordinate3 → Periodic.Site4 → ℚ
backgroundGaugeDefectCoordinate background fieldValue coordinate site =
  Gauge.backgroundGaugeFirst background fieldValue (pair coordinate site)
  - Gauge.flatGaugeFirstFromAxes fieldValue (pair coordinate site)

backgroundGaugeDefectCoordinateIsNegativeSum :
  ∀ background fieldValue coordinate site →
  backgroundGaugeDefectCoordinate background fieldValue coordinate site
  ≡ - Gauge.quaternionCoordinate coordinate
      (axisDefectSum background fieldValue site)
backgroundGaugeDefectCoordinateIsNegativeSum
    background fieldValue coordinate site =
  let
    d0 = axisDefect0 background fieldValue site
    d1 = axisDefect1 background fieldValue site
    d2 = axisDefect2 background fieldValue site
    d3 = axisDefect3 background fieldValue site

    literal =
      Gauge.backgroundGaugeFirstMinusFlatExact
        background fieldValue coordinate site

    sumExact :
      Gauge.quaternionCoordinate coordinate d0
        + (Gauge.quaternionCoordinate coordinate d1
          + (Gauge.quaternionCoordinate coordinate d2
            + (Gauge.quaternionCoordinate coordinate d3 + 0ℚ)))
      ≡ Gauge.quaternionCoordinate coordinate
          (d0 Q.+q (d1 Q.+q (d2 Q.+q d3)))
    sumExact =
      trans
        (ℚRing.solve-∀
          (Gauge.quaternionCoordinate coordinate d0)
          (Gauge.quaternionCoordinate coordinate d1)
          (Gauge.quaternionCoordinate coordinate d2)
          (Gauge.quaternionCoordinate coordinate d3))
        (sym (coordinateSum4Exact coordinate d0 d1 d2 d3))
  in
  trans literal (cong -_ sumExact)

pointwiseGaugeDefectEnergy :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Periodic.Site4 → ℚ
pointwiseGaugeDefectEnergy background fieldValue site =
  let
    dx = backgroundGaugeDefectCoordinate
      background fieldValue Coordinates.coordinateX site
    dy = backgroundGaugeDefectCoordinate
      background fieldValue Coordinates.coordinateY site
    dz = backgroundGaugeDefectCoordinate
      background fieldValue Coordinates.coordinateZ site
  in
  dx * dx + dy * dy + dz * dz

vectorPartNormSqBelowNormSq : ∀ value →
  Q.q1 value * Q.q1 value
    + Q.q2 value * Q.q2 value
    + Q.q3 value * Q.q3 value
  ≤ Norm.normSq value
vectorPartNormSqBelowNormSq (Q.quat q0 q1 q2 q3) =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (ℚRing.solve-∀ q0 q1 q2 q3)
      (FiniteL2.squareNonnegative q0))

pointwiseGaugeDefectEnergyBelowQuaternionSum :
  ∀ background fieldValue site →
  pointwiseGaugeDefectEnergy background fieldValue site
  ≤ Norm.normSq (axisDefectSum background fieldValue site)
pointwiseGaugeDefectEnergyBelowQuaternionSum background fieldValue site =
  let
    sum = axisDefectSum background fieldValue site

    dxExact = backgroundGaugeDefectCoordinateIsNegativeSum
      background fieldValue Coordinates.coordinateX site
    dyExact = backgroundGaugeDefectCoordinateIsNegativeSum
      background fieldValue Coordinates.coordinateY site
    dzExact = backgroundGaugeDefectCoordinateIsNegativeSum
      background fieldValue Coordinates.coordinateZ site

    energyExact :
      pointwiseGaugeDefectEnergy background fieldValue site
      ≡ Q.q1 sum * Q.q1 sum
        + Q.q2 sum * Q.q2 sum
        + Q.q3 sum * Q.q3 sum
    energyExact
      rewrite dxExact | dyExact | dzExact =
      ℚRing.solve-∀ (Q.q1 sum) (Q.q2 sum) (Q.q3 sum)
  in
  subst
    (λ lower → lower ≤ Norm.normSq sum)
    (sym energyExact)
    (vectorPartNormSqBelowNormSq sum)

axisLinkDefectCharge :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Site4 → ℚ
axisLinkDefectCharge background fieldValue axis site =
  let
    previousSite = Periodic.shiftBackward axis site
    bond = pair previousSite axis
    insertion = Gauge.insertionQuaternion fieldValue axis previousSite
  in
  Norm.normSq
      (Telescope._-q_ (Physical.inverseLink background bond) Q.oneQ)
    * Norm.normSq insertion

pointwiseGaugeLinkDefectCharge :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → Periodic.Site4 → ℚ
pointwiseGaugeLinkDefectCharge background fieldValue site =
  axisLinkDefectCharge background fieldValue Periodic.axis0 site
  + axisLinkDefectCharge background fieldValue Periodic.axis1 site
  + axisLinkDefectCharge background fieldValue Periodic.axis2 site
  + axisLinkDefectCharge background fieldValue Periodic.axis3 site

axisAdjointDefectNormSqBound :
  ∀ background fieldValue axis site →
  Norm.normSq (Gauge.axisAdjointDefect background fieldValue axis site)
  ≤ (+ 4 / 1) * axisLinkDefectCharge background fieldValue axis site
axisAdjointDefectNormSqBound background fieldValue axis site =
  AdjointNorm.physicalInverseLinkAdjointDefectNormSqBound
    background
    (pair (Periodic.shiftBackward axis site) axis)
    (Gauge.insertionQuaternion fieldValue axis
      (Periodic.shiftBackward axis site))

pointwiseGaugeDefectNormSqBound :
  ∀ background fieldValue site →
  pointwiseGaugeDefectEnergy background fieldValue site
  ≤ (+ 16 / 1) * pointwiseGaugeLinkDefectCharge background fieldValue site
pointwiseGaugeDefectNormSqBound background fieldValue site =
  let
    d0 = axisDefect0 background fieldValue site
    d1 = axisDefect1 background fieldValue site
    d2 = axisDefect2 background fieldValue site
    d3 = axisDefect3 background fieldValue site

    vectorBelow =
      pointwiseGaugeDefectEnergyBelowQuaternionSum background fieldValue site

    sumBelow :
      Norm.normSq (axisDefectSum background fieldValue site)
      ≤ (+ 4 / 1)
          * (Norm.normSq d0 + Norm.normSq d1
            + Norm.normSq d2 + Norm.normSq d3)
    sumBelow = Norm.normSqSum4Bound d0 d1 d2 d3

    axesBelow :
      Norm.normSq d0 + Norm.normSq d1
        + Norm.normSq d2 + Norm.normSq d3
      ≤ (+ 4 / 1)
          * pointwiseGaugeLinkDefectCharge background fieldValue site
    axesBelow =
      subst
        (λ upper →
          Norm.normSq d0 + Norm.normSq d1
            + Norm.normSq d2 + Norm.normSq d3
          ≤ upper)
        (ℚRing.solve-∀
          (axisLinkDefectCharge background fieldValue Periodic.axis0 site)
          (axisLinkDefectCharge background fieldValue Periodic.axis1 site)
          (axisLinkDefectCharge background fieldValue Periodic.axis2 site)
          (axisLinkDefectCharge background fieldValue Periodic.axis3 site))
        (ℚP.+-mono-≤
          (ℚP.+-mono-≤
            (ℚP.+-mono-≤
              (axisAdjointDefectNormSqBound
                background fieldValue Periodic.axis0 site)
              (axisAdjointDefectNormSqBound
                background fieldValue Periodic.axis1 site))
            (axisAdjointDefectNormSqBound
              background fieldValue Periodic.axis2 site))
          (axisAdjointDefectNormSqBound
            background fieldValue Periodic.axis3 site))

    scaledAxes :
      (+ 4 / 1)
        * (Norm.normSq d0 + Norm.normSq d1
          + Norm.normSq d2 + Norm.normSq d3)
      ≤ (+ 16 / 1)
          * pointwiseGaugeLinkDefectCharge background fieldValue site
    scaledAxes =
      subst
        (λ upper →
          (+ 4 / 1)
            * (Norm.normSq d0 + Norm.normSq d1
              + Norm.normSq d2 + Norm.normSq d3)
          ≤ upper)
        (ℚRing.solve-∀
          (pointwiseGaugeLinkDefectCharge background fieldValue site))
        (Norm.scaleNonnegative (+ 4 / 1)
          (ℚP.nonNegative⁻¹ (+ 4 / 1)) axesBelow)
  in
  ℚP.≤-trans vectorBelow (ℚP.≤-trans sumBelow scaledAxes)

physicalBackgroundGaugePointwiseNormLevel : ProofLevel
physicalBackgroundGaugePointwiseNormLevel = machineChecked

physicalBackgroundGaugeGlobalReindexLevel : ProofLevel
physicalBackgroundGaugeGlobalReindexLevel = conditional

physicalBackgroundGaugeSignedEnergyLevel : ProofLevel
physicalBackgroundGaugeSignedEnergyLevel = conditional
