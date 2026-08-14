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
-- Hence H_div^0(h) <= 16 ||h||^2.  The physical lift explicitly converts the
-- repository's positive-bond carrier `(site,axis) -> Q` into the periodic
-- axis-indexed carrier `axis -> site -> Q`; these function spaces are
-- isomorphic but not definitionally equal, so the conversion is part of the
-- theorem rather than being hidden by an invalid unification.
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
import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact as GlobalGauge

scalarDifferenceSquareBound : ∀ left right →
  (left - right) * (left - right)
  ≤ (+ 2 / 1) * (left * left + right * right)
scalarDifferenceSquareBound left right =
  subst
    (λ lower → lower ≤ (+ 2 / 1) * (left * left + right * right))
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

backwardDifferenceNormSqBound : ∀ axis fieldValue →
  Periodic.fieldNormSq (Periodic.backwardDifference axis fieldValue)
  ≤ (+ 4 / 1) * Periodic.fieldNormSq fieldValue
backwardDifferenceNormSqBound axis fieldValue =
  let
    pointwise : ∀ site →
      Periodic.backwardDifference axis fieldValue site
        * Periodic.backwardDifference axis fieldValue site
      ≤ (+ 2 / 1)
          * (fieldValue site * fieldValue site
            + fieldValue (Periodic.shiftBackward axis site)
              * fieldValue (Periodic.shiftBackward axis site))
    pointwise site =
      scalarDifferenceSquareBound
        (fieldValue site) (fieldValue (Periodic.shiftBackward axis site))

    raw = GlobalGauge.sumSitesMonotone _ _ pointwise

    expanded :
      Periodic.sumSites
        (λ site →
          (+ 2 / 1)
            * (fieldValue site * fieldValue site
              + fieldValue (Periodic.shiftBackward axis site)
                * fieldValue (Periodic.shiftBackward axis site)))
      ≡ (+ 4 / 1) * Periodic.fieldNormSq fieldValue
    expanded =
      trans
        (Periodic.sumSitesScale (+ 2 / 1)
          (λ site →
            fieldValue site * fieldValue site
            + fieldValue (Periodic.shiftBackward axis site)
              * fieldValue (Periodic.shiftBackward axis site)))
        (trans
          (cong ((+ 2 / 1) *_)
            (Periodic.sumSitesAdd
              (λ site → fieldValue site * fieldValue site)
              (λ site →
                fieldValue (Periodic.shiftBackward axis site)
                * fieldValue (Periodic.shiftBackward axis site))))
          (trans
            (cong
              (λ selected →
                (+ 2 / 1)
                  * (Periodic.fieldNormSq fieldValue + selected))
              (Periodic.sumSitesBackwardInvariant
                (λ site → fieldValue site * fieldValue site) axis))
            (ℚRing.solve-∀ (Periodic.fieldNormSq fieldValue))))
  in
  subst
    (λ upper →
      Periodic.fieldNormSq (Periodic.backwardDifference axis fieldValue)
      ≤ upper)
    expanded raw

scalarBondNormSq : Periodic.BondField4 → ℚ
scalarBondNormSq fieldValue =
  Periodic.fieldNormSq (fieldValue Periodic.axis0)
  + (Periodic.fieldNormSq (fieldValue Periodic.axis1)
  + (Periodic.fieldNormSq (fieldValue Periodic.axis2)
  + Periodic.fieldNormSq (fieldValue Periodic.axis3)))

periodicDivergencePointwiseSquareBound : ∀ fieldValue site →
  Periodic.periodicDivergence fieldValue site
    * Periodic.periodicDivergence fieldValue site
  ≤ (+ 4 / 1)
      * (
        Periodic.backwardDifference Periodic.axis0
          (fieldValue Periodic.axis0) site
        * Periodic.backwardDifference Periodic.axis0
          (fieldValue Periodic.axis0) site
      + Periodic.backwardDifference Periodic.axis1
          (fieldValue Periodic.axis1) site
        * Periodic.backwardDifference Periodic.axis1
          (fieldValue Periodic.axis1) site
      + Periodic.backwardDifference Periodic.axis2
          (fieldValue Periodic.axis2) site
        * Periodic.backwardDifference Periodic.axis2
          (fieldValue Periodic.axis2) site
      + Periodic.backwardDifference Periodic.axis3
          (fieldValue Periodic.axis3) site
        * Periodic.backwardDifference Periodic.axis3
          (fieldValue Periodic.axis3) site)
periodicDivergencePointwiseSquareBound fieldValue site =
  scalarSum4SquareBound
    (Periodic.backwardDifference Periodic.axis0 (fieldValue Periodic.axis0) site)
    (Periodic.backwardDifference Periodic.axis1 (fieldValue Periodic.axis1) site)
    (Periodic.backwardDifference Periodic.axis2 (fieldValue Periodic.axis2) site)
    (Periodic.backwardDifference Periodic.axis3 (fieldValue Periodic.axis3) site)

periodicDivergenceEnergyBelowBackwardNorms : ∀ fieldValue →
  Periodic.periodicDivergenceEnergy fieldValue
  ≤ (+ 4 / 1)
      * (
        Periodic.fieldNormSq
          (Periodic.backwardDifference Periodic.axis0 (fieldValue Periodic.axis0))
      + Periodic.fieldNormSq
          (Periodic.backwardDifference Periodic.axis1 (fieldValue Periodic.axis1))
      + Periodic.fieldNormSq
          (Periodic.backwardDifference Periodic.axis2 (fieldValue Periodic.axis2))
      + Periodic.fieldNormSq
          (Periodic.backwardDifference Periodic.axis3 (fieldValue Periodic.axis3)))
periodicDivergenceEnergyBelowBackwardNorms fieldValue =
  let
    raw = GlobalGauge.sumSitesMonotone _ _
      (periodicDivergencePointwiseSquareBound fieldValue)

    expanded =
      trans
        (Periodic.sumSitesScale (+ 4 / 1)
          (λ site →
            Periodic.backwardDifference Periodic.axis0
              (fieldValue Periodic.axis0) site
              * Periodic.backwardDifference Periodic.axis0
                  (fieldValue Periodic.axis0) site
            + Periodic.backwardDifference Periodic.axis1
              (fieldValue Periodic.axis1) site
              * Periodic.backwardDifference Periodic.axis1
                  (fieldValue Periodic.axis1) site
            + Periodic.backwardDifference Periodic.axis2
              (fieldValue Periodic.axis2) site
              * Periodic.backwardDifference Periodic.axis2
                  (fieldValue Periodic.axis2) site
            + Periodic.backwardDifference Periodic.axis3
              (fieldValue Periodic.axis3) site
              * Periodic.backwardDifference Periodic.axis3
                  (fieldValue Periodic.axis3) site))
        (cong ((+ 4 / 1) *_)
          (trans
            (Periodic.sumSitesAdd
              (λ site →
                Periodic.backwardDifference Periodic.axis0
                  (fieldValue Periodic.axis0) site
                * Periodic.backwardDifference Periodic.axis0
                  (fieldValue Periodic.axis0) site)
              (λ site →
                Periodic.backwardDifference Periodic.axis1
                  (fieldValue Periodic.axis1) site
                * Periodic.backwardDifference Periodic.axis1
                  (fieldValue Periodic.axis1) site
                + Periodic.backwardDifference Periodic.axis2
                  (fieldValue Periodic.axis2) site
                * Periodic.backwardDifference Periodic.axis2
                  (fieldValue Periodic.axis2) site
                + Periodic.backwardDifference Periodic.axis3
                  (fieldValue Periodic.axis3) site
                * Periodic.backwardDifference Periodic.axis3
                  (fieldValue Periodic.axis3) site))
            (cong₂ _+_ refl
              (trans
                (Periodic.sumSitesAdd
                  (λ site →
                    Periodic.backwardDifference Periodic.axis1
                      (fieldValue Periodic.axis1) site
                    * Periodic.backwardDifference Periodic.axis1
                      (fieldValue Periodic.axis1) site)
                  (λ site →
                    Periodic.backwardDifference Periodic.axis2
                      (fieldValue Periodic.axis2) site
                    * Periodic.backwardDifference Periodic.axis2
                      (fieldValue Periodic.axis2) site
                    + Periodic.backwardDifference Periodic.axis3
                      (fieldValue Periodic.axis3) site
                    * Periodic.backwardDifference Periodic.axis3
                      (fieldValue Periodic.axis3) site))
                (cong₂ _+_ refl
                  (Periodic.sumSitesAdd
                    (λ site →
                      Periodic.backwardDifference Periodic.axis2
                        (fieldValue Periodic.axis2) site
                      * Periodic.backwardDifference Periodic.axis2
                        (fieldValue Periodic.axis2) site)
                    (λ site →
                      Periodic.backwardDifference Periodic.axis3
                        (fieldValue Periodic.axis3) site
                      * Periodic.backwardDifference Periodic.axis3
                        (fieldValue Periodic.axis3) site)))))))
  in
  subst
    (λ upper → Periodic.periodicDivergenceEnergy fieldValue ≤ upper)
    expanded raw

periodicDivergenceUpper : ∀ fieldValue →
  Periodic.periodicDivergenceEnergy fieldValue
  ≤ (+ 16 / 1) * scalarBondNormSq fieldValue
periodicDivergenceUpper fieldValue =
  let
    first = periodicDivergenceEnergyBelowBackwardNorms fieldValue

    componentBounds =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (ℚP.+-mono-≤
            (backwardDifferenceNormSqBound
              Periodic.axis0 (fieldValue Periodic.axis0))
            (backwardDifferenceNormSqBound
              Periodic.axis1 (fieldValue Periodic.axis1)))
          (backwardDifferenceNormSqBound
            Periodic.axis2 (fieldValue Periodic.axis2)))
        (backwardDifferenceNormSqBound
          Periodic.axis3 (fieldValue Periodic.axis3))

    scaled =
      Norm.scaleNonnegative (+ 4 / 1)
        (ℚP.nonNegative⁻¹ (+ 4 / 1)) componentBounds

    combined = ℚP.≤-trans first scaled
  in
  subst
    (λ upper → Periodic.periodicDivergenceEnergy fieldValue ≤ upper)
    (ℚRing.solve-∀
      (Periodic.fieldNormSq (fieldValue Periodic.axis0))
      (Periodic.fieldNormSq (fieldValue Periodic.axis1))
      (Periodic.fieldNormSq (fieldValue Periodic.axis2))
      (Periodic.fieldNormSq (fieldValue Periodic.axis3)))
    combined

physicalPeriodicDivergenceUpper :
  ∀ (fieldValue : Coordinates.PhysicalSU2BondField4) →
  Periodic.physicalPeriodicDivergenceEnergy (Bridge.asPeriodicField fieldValue)
  ≤ (+ 16 / 1) * Coordinates.physicalSU2BondNormSq fieldValue
physicalPeriodicDivergenceUpper fieldValue =
  let
    xField = Bridge.asPeriodicField fieldValue Coordinates.coordinateX
    yField = Bridge.asPeriodicField fieldValue Coordinates.coordinateY
    zField = Bridge.asPeriodicField fieldValue Coordinates.coordinateZ

    xBound = periodicDivergenceUpper xField
    yBound = periodicDivergenceUpper yField
    zBound = periodicDivergenceUpper zField

    combined = ℚP.+-mono-≤ xBound (ℚP.+-mono-≤ yBound zBound)

    toPeriodicPhysical :
      (+ 16 / 1) * scalarBondNormSq xField
      + ((+ 16 / 1) * scalarBondNormSq yField
      + (+ 16 / 1) * scalarBondNormSq zField)
      ≡ (+ 16 / 1) * GlobalGauge.periodicPhysicalBondNormSq fieldValue
    toPeriodicPhysical
      rewrite GlobalGauge.axisInsertionNormSqExact fieldValue Periodic.axis0
            | GlobalGauge.axisInsertionNormSqExact fieldValue Periodic.axis1
            | GlobalGauge.axisInsertionNormSqExact fieldValue Periodic.axis2
            | GlobalGauge.axisInsertionNormSqExact fieldValue Periodic.axis3 =
      ℚRing.solve-∀
        (Periodic.fieldNormSq
          (λ site → fieldValue Coordinates.coordinateX (Periodic.pair site Periodic.axis0)))
        (Periodic.fieldNormSq
          (λ site → fieldValue Coordinates.coordinateX (Periodic.pair site Periodic.axis1)))
        (Periodic.fieldNormSq
          (λ site → fieldValue Coordinates.coordinateX (Periodic.pair site Periodic.axis2)))
        (Periodic.fieldNormSq
          (λ site → fieldValue Coordinates.coordinateX (Periodic.pair site Periodic.axis3)))
        (Periodic.fieldNormSq
          (λ site → fieldValue Coordinates.coordinateY (Periodic.pair site Periodic.axis0)))
        (Periodic.fieldNormSq
          (λ site → fieldValue Coordinates.coordinateY (Periodic.pair site Periodic.axis1)))
        (Periodic.fieldNormSq
          (λ site → fieldValue Coordinates.coordinateY (Periodic.pair site Periodic.axis2)))
        (Periodic.fieldNormSq
          (λ site → fieldValue Coordinates.coordinateY (Periodic.pair site Periodic.axis3)))
        (Periodic.fieldNormSq
          (λ site → fieldValue Coordinates.coordinateZ (Periodic.pair site Periodic.axis0)))
        (Periodic.fieldNormSq
          (λ site → fieldValue Coordinates.coordinateZ (Periodic.pair site Periodic.axis1)))
        (Periodic.fieldNormSq
          (λ site → fieldValue Coordinates.coordinateZ (Periodic.pair site Periodic.axis2)))
        (Periodic.fieldNormSq
          (λ site → fieldValue Coordinates.coordinateZ (Periodic.pair site Periodic.axis3)))
  in
  subst
    (λ upper →
      Periodic.physicalPeriodicDivergenceEnergy (Bridge.asPeriodicField fieldValue)
      ≤ upper)
    (trans toPeriodicPhysical
      (cong ((+ 16 / 1) *_)
        (GlobalGauge.periodicPhysicalBondNormSqExact fieldValue)))
    combined

periodicBackwardDifferenceUpperLevel : ProofLevel
periodicBackwardDifferenceUpperLevel = machineChecked

periodicDivergenceUpperLevel : ProofLevel
periodicDivergenceUpperLevel = machineChecked

physicalPeriodicDivergenceUpperLevel : ProofLevel
physicalPeriodicDivergenceUpperLevel = machineChecked
