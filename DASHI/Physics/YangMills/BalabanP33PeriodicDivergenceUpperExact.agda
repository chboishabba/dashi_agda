module DASHI.Physics.YangMills.BalabanP33PeriodicDivergenceUpperExact where

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
-- Prove the literal side-four operator-norm bound for the flat backward
-- divergence.  Pointwise,
--
--   |d0+d1+d2+d3|^2 <= 4 sum_mu |d_mu|^2,
--
-- while periodic reindexing gives
--
--   sum_x |f(x)-f(x-mu)|^2 <= 4 sum_x |f(x)|^2.
--
-- Hence for a scalar four-bond field
--
--   H_div^0(h) <= 16 sum_mu ||h_mu||^2,
--
-- and after the exact three-coordinate physical lift
--
--   H_div^0(h) <= 16 ||h||^2_SU(2).
--
-- This is the missing flat-divergence upper estimate needed to turn the global
-- derivative-defect norm bound into a signed gauge-energy lower bound.
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
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact as GlobalGauge

scalarDifferenceSquareBound : ∀ left right →
  (left - right) * (left - right)
  ≤ (+ 2 / 1) * (left * left + right * right)
scalarDifferenceSquareBound left right =
  subst
    (λ lower →
      lower ≤ (+ 2 / 1) * (left * left + right * right))
    (ℚRing.solve-∀ left right)
    (subst
      (λ upper →
        (left + (- right)) * (left + (- right)) ≤ upper)
      (ℚRing.solve-∀ left right)
      (Norm.scalarTwoTermSquareBound left (- right)))

scalarSum4SquareBound : ∀ first second third fourth →
  (first + (second + (third + fourth)))
    * (first + (second + (third + fourth)))
  ≤ (+ 4 / 1)
      * (first * first + second * second
        + third * third + fourth * fourth)
scalarSum4SquareBound first second third fourth =
  let
    q0 = Q.quat first 0ℚ 0ℚ 0ℚ
    q1 = Q.quat second 0ℚ 0ℚ 0ℚ
    q2 = Q.quat third 0ℚ 0ℚ 0ℚ
    q3 = Q.quat fourth 0ℚ 0ℚ 0ℚ

    raw = Norm.normSqSum4Bound q0 q1 q2 q3
  in
  subst
    (λ lower →
      lower
      ≤ (+ 4 / 1)
          * (first * first + second * second
            + third * third + fourth * fourth))
    (ℚRing.solve-∀ first second third fourth)
    (subst
      (λ upper →
        Norm.normSq (q0 Q.+q (q1 Q.+q (q2 Q.+q q3))) ≤ upper)
      (ℚRing.solve-∀ first second third fourth)
      raw)

backwardDifferenceNormSqBound : ∀ axis field →
  Periodic.fieldNormSq (Periodic.backwardDifference axis field)
  ≤ (+ 4 / 1) * Periodic.fieldNormSq field
backwardDifferenceNormSqBound axis field =
  let
    pointwise : ∀ site →
      Periodic.backwardDifference axis field site
        * Periodic.backwardDifference axis field site
      ≤ (+ 2 / 1)
          * (field site * field site
            + field (Periodic.shiftBackward axis site)
              * field (Periodic.shiftBackward axis site))
    pointwise site =
      scalarDifferenceSquareBound
        (field site) (field (Periodic.shiftBackward axis site))

    raw :
      Periodic.fieldNormSq (Periodic.backwardDifference axis field)
      ≤ Periodic.sumSites
          (λ site →
            (+ 2 / 1)
              * (field site * field site
                + field (Periodic.shiftBackward axis site)
                  * field (Periodic.shiftBackward axis site)))
    raw = GlobalGauge.sumSitesMonotone _ _ pointwise

    expanded :
      Periodic.sumSites
        (λ site →
          (+ 2 / 1)
            * (field site * field site
              + field (Periodic.shiftBackward axis site)
                * field (Periodic.shiftBackward axis site)))
      ≡ (+ 4 / 1) * Periodic.fieldNormSq field
    expanded =
      trans
        (Periodic.sumSitesScale (+ 2 / 1)
          (λ site →
            field site * field site
            + field (Periodic.shiftBackward axis site)
              * field (Periodic.shiftBackward axis site)))
        (trans
          (cong ((+ 2 / 1) *_)
            (Periodic.sumSitesAdd
              (λ site → field site * field site)
              (λ site →
                field (Periodic.shiftBackward axis site)
                * field (Periodic.shiftBackward axis site))))
          (trans
            (cong
              (λ selected →
                (+ 2 / 1)
                  * (Periodic.fieldNormSq field + selected))
              (Periodic.sumSitesBackwardInvariant
                (λ site → field site * field site) axis))
            (ℚRing.solve-∀ (Periodic.fieldNormSq field))))
  in
  subst
    (λ upper →
      Periodic.fieldNormSq (Periodic.backwardDifference axis field)
      ≤ upper)
    expanded raw

scalarBondNormSq : Periodic.BondField4 → ℚ
scalarBondNormSq field =
  Periodic.fieldNormSq (field Periodic.axis0)
  + (Periodic.fieldNormSq (field Periodic.axis1)
  + (Periodic.fieldNormSq (field Periodic.axis2)
  + Periodic.fieldNormSq (field Periodic.axis3)))

periodicDivergencePointwiseSquareBound : ∀ field site →
  Periodic.periodicDivergence field site
    * Periodic.periodicDivergence field site
  ≤ (+ 4 / 1)
      * (
        Periodic.backwardDifference Periodic.axis0
          (field Periodic.axis0) site
        * Periodic.backwardDifference Periodic.axis0
          (field Periodic.axis0) site
      + Periodic.backwardDifference Periodic.axis1
          (field Periodic.axis1) site
        * Periodic.backwardDifference Periodic.axis1
          (field Periodic.axis1) site
      + Periodic.backwardDifference Periodic.axis2
          (field Periodic.axis2) site
        * Periodic.backwardDifference Periodic.axis2
          (field Periodic.axis2) site
      + Periodic.backwardDifference Periodic.axis3
          (field Periodic.axis3) site
        * Periodic.backwardDifference Periodic.axis3
          (field Periodic.axis3) site)
periodicDivergencePointwiseSquareBound field site =
  scalarSum4SquareBound
    (Periodic.backwardDifference Periodic.axis0 (field Periodic.axis0) site)
    (Periodic.backwardDifference Periodic.axis1 (field Periodic.axis1) site)
    (Periodic.backwardDifference Periodic.axis2 (field Periodic.axis2) site)
    (Periodic.backwardDifference Periodic.axis3 (field Periodic.axis3) site)

periodicDivergenceEnergyBelowBackwardNorms : ∀ field →
  Periodic.periodicDivergenceEnergy field
  ≤ (+ 4 / 1)
      * (
        Periodic.fieldNormSq
          (Periodic.backwardDifference Periodic.axis0 (field Periodic.axis0))
      + Periodic.fieldNormSq
          (Periodic.backwardDifference Periodic.axis1 (field Periodic.axis1))
      + Periodic.fieldNormSq
          (Periodic.backwardDifference Periodic.axis2 (field Periodic.axis2))
      + Periodic.fieldNormSq
          (Periodic.backwardDifference Periodic.axis3 (field Periodic.axis3)))
periodicDivergenceEnergyBelowBackwardNorms field =
  let
    raw =
      GlobalGauge.sumSitesMonotone _ _
        (periodicDivergencePointwiseSquareBound field)

    expanded =
      trans
        (Periodic.sumSitesScale (+ 4 / 1)
          (λ site →
            Periodic.backwardDifference Periodic.axis0
              (field Periodic.axis0) site
              * Periodic.backwardDifference Periodic.axis0
                  (field Periodic.axis0) site
            + Periodic.backwardDifference Periodic.axis1
              (field Periodic.axis1) site
              * Periodic.backwardDifference Periodic.axis1
                  (field Periodic.axis1) site
            + Periodic.backwardDifference Periodic.axis2
              (field Periodic.axis2) site
              * Periodic.backwardDifference Periodic.axis2
                  (field Periodic.axis2) site
            + Periodic.backwardDifference Periodic.axis3
              (field Periodic.axis3) site
              * Periodic.backwardDifference Periodic.axis3
                  (field Periodic.axis3) site))
        (cong ((+ 4 / 1) *_)
          (trans
            (Periodic.sumSitesAdd
              (λ site →
                Periodic.backwardDifference Periodic.axis0
                  (field Periodic.axis0) site
                * Periodic.backwardDifference Periodic.axis0
                  (field Periodic.axis0) site)
              (λ site →
                Periodic.backwardDifference Periodic.axis1
                  (field Periodic.axis1) site
                * Periodic.backwardDifference Periodic.axis1
                  (field Periodic.axis1) site
                + Periodic.backwardDifference Periodic.axis2
                  (field Periodic.axis2) site
                * Periodic.backwardDifference Periodic.axis2
                  (field Periodic.axis2) site
                + Periodic.backwardDifference Periodic.axis3
                  (field Periodic.axis3) site
                * Periodic.backwardDifference Periodic.axis3
                  (field Periodic.axis3) site))
            (cong₂ _+_ refl
              (trans
                (Periodic.sumSitesAdd
                  (λ site →
                    Periodic.backwardDifference Periodic.axis1
                      (field Periodic.axis1) site
                    * Periodic.backwardDifference Periodic.axis1
                      (field Periodic.axis1) site)
                  (λ site →
                    Periodic.backwardDifference Periodic.axis2
                      (field Periodic.axis2) site
                    * Periodic.backwardDifference Periodic.axis2
                      (field Periodic.axis2) site
                    + Periodic.backwardDifference Periodic.axis3
                      (field Periodic.axis3) site
                    * Periodic.backwardDifference Periodic.axis3
                      (field Periodic.axis3) site))
                (cong₂ _+_ refl
                  (Periodic.sumSitesAdd
                    (λ site →
                      Periodic.backwardDifference Periodic.axis2
                        (field Periodic.axis2) site
                      * Periodic.backwardDifference Periodic.axis2
                        (field Periodic.axis2) site)
                    (λ site →
                      Periodic.backwardDifference Periodic.axis3
                        (field Periodic.axis3) site
                      * Periodic.backwardDifference Periodic.axis3
                        (field Periodic.axis3) site)))))))
  in
  subst
    (λ upper → Periodic.periodicDivergenceEnergy field ≤ upper)
    expanded raw

periodicDivergenceUpper : ∀ field →
  Periodic.periodicDivergenceEnergy field
  ≤ (+ 16 / 1) * scalarBondNormSq field
periodicDivergenceUpper field =
  let
    first = periodicDivergenceEnergyBelowBackwardNorms field

    componentBounds =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (ℚP.+-mono-≤
            (backwardDifferenceNormSqBound
              Periodic.axis0 (field Periodic.axis0))
            (backwardDifferenceNormSqBound
              Periodic.axis1 (field Periodic.axis1)))
          (backwardDifferenceNormSqBound
            Periodic.axis2 (field Periodic.axis2)))
        (backwardDifferenceNormSqBound
          Periodic.axis3 (field Periodic.axis3))

    scaled =
      Norm.scaleNonnegative (+ 4 / 1)
        (ℚP.nonNegative⁻¹ (+ 4 / 1)) componentBounds

    combined = ℚP.≤-trans first scaled
  in
  subst
    (λ upper → Periodic.periodicDivergenceEnergy field ≤ upper)
    (ℚRing.solve-∀
      (Periodic.fieldNormSq (field Periodic.axis0))
      (Periodic.fieldNormSq (field Periodic.axis1))
      (Periodic.fieldNormSq (field Periodic.axis2))
      (Periodic.fieldNormSq (field Periodic.axis3)))
    combined

physicalPeriodicDivergenceUpper : ∀ field →
  Periodic.physicalPeriodicDivergenceEnergy field
  ≤ (+ 16 / 1) * Coordinates.physicalSU2BondNormSq field
physicalPeriodicDivergenceUpper field =
  let
    xBound = periodicDivergenceUpper (field Coordinates.coordinateX)
    yBound = periodicDivergenceUpper (field Coordinates.coordinateY)
    zBound = periodicDivergenceUpper (field Coordinates.coordinateZ)

    combined =
      ℚP.+-mono-≤ xBound (ℚP.+-mono-≤ yBound zBound)

    toPeriodicPhysical :
      (+ 16 / 1)
        * scalarBondNormSq (field Coordinates.coordinateX)
      + ((+ 16 / 1)
        * scalarBondNormSq (field Coordinates.coordinateY)
      + (+ 16 / 1)
        * scalarBondNormSq (field Coordinates.coordinateZ))
      ≡ (+ 16 / 1) * GlobalGauge.periodicPhysicalBondNormSq field
    toPeriodicPhysical
      rewrite GlobalGauge.axisInsertionNormSqExact field Periodic.axis0
            | GlobalGauge.axisInsertionNormSqExact field Periodic.axis1
            | GlobalGauge.axisInsertionNormSqExact field Periodic.axis2
            | GlobalGauge.axisInsertionNormSqExact field Periodic.axis3 =
      ℚRing.solve-∀
        (Periodic.fieldNormSq
          (λ site → field Coordinates.coordinateX (Periodic.pair site Periodic.axis0)))
        (Periodic.fieldNormSq
          (λ site → field Coordinates.coordinateX (Periodic.pair site Periodic.axis1)))
        (Periodic.fieldNormSq
          (λ site → field Coordinates.coordinateX (Periodic.pair site Periodic.axis2)))
        (Periodic.fieldNormSq
          (λ site → field Coordinates.coordinateX (Periodic.pair site Periodic.axis3)))
        (Periodic.fieldNormSq
          (λ site → field Coordinates.coordinateY (Periodic.pair site Periodic.axis0)))
        (Periodic.fieldNormSq
          (λ site → field Coordinates.coordinateY (Periodic.pair site Periodic.axis1)))
        (Periodic.fieldNormSq
          (λ site → field Coordinates.coordinateY (Periodic.pair site Periodic.axis2)))
        (Periodic.fieldNormSq
          (λ site → field Coordinates.coordinateY (Periodic.pair site Periodic.axis3)))
        (Periodic.fieldNormSq
          (λ site → field Coordinates.coordinateZ (Periodic.pair site Periodic.axis0)))
        (Periodic.fieldNormSq
          (λ site → field Coordinates.coordinateZ (Periodic.pair site Periodic.axis1)))
        (Periodic.fieldNormSq
          (λ site → field Coordinates.coordinateZ (Periodic.pair site Periodic.axis2)))
        (Periodic.fieldNormSq
          (λ site → field Coordinates.coordinateZ (Periodic.pair site Periodic.axis3)))
  in
  subst
    (λ upper → Periodic.physicalPeriodicDivergenceEnergy field ≤ upper)
    (trans toPeriodicPhysical
      (cong ((+ 16 / 1) *_)
        (GlobalGauge.periodicPhysicalBondNormSqExact field)))
    combined

periodicBackwardDifferenceUpperLevel : ProofLevel
periodicBackwardDifferenceUpperLevel = machineChecked

periodicDivergenceUpperLevel : ProofLevel
periodicDivergenceUpperLevel = machineChecked

physicalPeriodicDivergenceUpperLevel : ProofLevel
physicalPeriodicDivergenceUpperLevel = machineChecked
