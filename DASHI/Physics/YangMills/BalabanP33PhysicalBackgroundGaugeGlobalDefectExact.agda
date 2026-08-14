module DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeGlobalDefectExact where

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
-- John H. Conway and Derek A. Smith,
-- "On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry",
-- A K Peters, 2003. DOI: 10.1201/9781439864180.
--
-- DASHI CONTRIBUTION
--
-- Sum the pointwise covariant-gauge derivative defect on the literal side-four
-- torus and reindex every predecessor bond exactly.  If every inverse
-- background link satisfies
--
--   N(U_b^-1 - 1) <= delta,
--
-- then
--
--   sum_{x,a} |(D F_A-D F_1)^a(x)|^2
--     <= 16 delta ||h||^2_SU(2).
--
-- The norm on the right is not a new interface: this module proves that the
-- explicit periodic site/axis fold used by the gauge estimate is exactly the
-- existing `physicalSU2BondNormSq`.  The proof uses literal finite-sum Fubini,
-- the four cyclic predecessor reindexings, quaternion norm multiplicativity,
-- and the already checked pointwise factor-sixteen estimate.
--
-- This leaves only the selected-background link-radius theorem and the signed
-- comparison of gauge energies before G-local is closed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact as Variance
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeDefectNormSquaredExact as Pointwise

------------------------------------------------------------------------
-- Monotonicity of the literal nested side-four sums.
------------------------------------------------------------------------

sumIndex4Monotone : ∀ left right →
  (∀ index → left index ≤ right index) →
  Periodic.sumIndex4 left ≤ Periodic.sumIndex4 right
sumIndex4Monotone left right pointwise =
  ℚP.+-mono-≤
    (pointwise Periodic.index0)
    (ℚP.+-mono-≤
      (pointwise Periodic.index1)
      (ℚP.+-mono-≤
        (pointwise Periodic.index2)
        (ℚP.+-mono-≤
          (pointwise Periodic.index3)
          ℚP.≤-refl)))

sumSitesMonotone : ∀ left right →
  (∀ site → left site ≤ right site) →
  Periodic.sumSites left ≤ Periodic.sumSites right
sumSitesMonotone left right pointwise =
  sumIndex4Monotone _ _ (λ x0 →
    sumIndex4Monotone _ _ (λ x1 →
      sumIndex4Monotone _ _ (λ x2 →
        sumIndex4Monotone _ _ (λ x3 →
          pointwise (pair (pair x0 x1) (pair x2 x3))))))

------------------------------------------------------------------------
-- Exact compatibility of the periodic and existing physical norms.
------------------------------------------------------------------------

periodicSumSitesMatchesCoordinateSum4 : ∀ term →
  Periodic.sumSites term ≡ Partition.coordinateSum4 term
periodicSumSitesMatchesCoordinateSum4 term = refl

periodicFieldNormSqMatchesGlobal : ∀ fieldValue →
  Periodic.fieldNormSq fieldValue ≡ Variance.globalNormSq fieldValue
periodicFieldNormSqMatchesGlobal fieldValue =
  trans
    (periodicSumSitesMatchesCoordinateSum4
      (λ site → fieldValue site * fieldValue site))
    (sym
      (Partition.globalSiteSumMatchesCoordinateSum4
        (λ site → fieldValue site * fieldValue site)))

globalFieldNormSqMatchesPeriodic : ∀ fieldValue →
  Variance.globalNormSq fieldValue ≡ Periodic.fieldNormSq fieldValue
globalFieldNormSqMatchesPeriodic fieldValue =
  sym (periodicFieldNormSqMatchesGlobal fieldValue)

insertionNormSqPointwiseExact :
  ∀ fieldValue axis site →
  Norm.normSq (Gauge.insertionQuaternion fieldValue axis site)
  ≡
    fieldValue Coordinates.coordinateX (pair site axis)
      * fieldValue Coordinates.coordinateX (pair site axis)
    + (fieldValue Coordinates.coordinateY (pair site axis)
      * fieldValue Coordinates.coordinateY (pair site axis)
    + fieldValue Coordinates.coordinateZ (pair site axis)
      * fieldValue Coordinates.coordinateZ (pair site axis))
insertionNormSqPointwiseExact fieldValue axis site =
  ℚRing.solve-∀
    (fieldValue Coordinates.coordinateX (pair site axis))
    (fieldValue Coordinates.coordinateY (pair site axis))
    (fieldValue Coordinates.coordinateZ (pair site axis))

axisInsertionNormSq :
  Coordinates.PhysicalSU2BondField4 → Periodic.Axis4 → ℚ
axisInsertionNormSq fieldValue axis =
  Periodic.sumSites
    (λ site → Norm.normSq (Gauge.insertionQuaternion fieldValue axis site))

axisInsertionNormSqExact : ∀ fieldValue axis →
  axisInsertionNormSq fieldValue axis
  ≡ Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateX (pair site axis))
    + (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateY (pair site axis))
    + Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateZ (pair site axis)))
axisInsertionNormSqExact fieldValue axis =
  trans
    (Periodic.sumSitesCong _ _
      (insertionNormSqPointwiseExact fieldValue axis))
    (trans
      (Periodic.sumSitesAdd
        (λ site →
          fieldValue Coordinates.coordinateX (pair site axis)
          * fieldValue Coordinates.coordinateX (pair site axis))
        (λ site →
          fieldValue Coordinates.coordinateY (pair site axis)
            * fieldValue Coordinates.coordinateY (pair site axis)
          + fieldValue Coordinates.coordinateZ (pair site axis)
            * fieldValue Coordinates.coordinateZ (pair site axis)))
      (cong₂ _+_ refl
        (Periodic.sumSitesAdd
          (λ site →
            fieldValue Coordinates.coordinateY (pair site axis)
            * fieldValue Coordinates.coordinateY (pair site axis))
          (λ site →
            fieldValue Coordinates.coordinateZ (pair site axis)
            * fieldValue Coordinates.coordinateZ (pair site axis)))))

coordinatePeriodicBondNormSq :
  Coordinates.PhysicalSU2BondField4 → Coordinates.LieCoordinate3 → ℚ
coordinatePeriodicBondNormSq fieldValue coordinate =
  Periodic.fieldNormSq (λ site → fieldValue coordinate (pair site Periodic.axis0))
  + (Periodic.fieldNormSq (λ site → fieldValue coordinate (pair site Periodic.axis1))
  + (Periodic.fieldNormSq (λ site → fieldValue coordinate (pair site Periodic.axis2))
  + Periodic.fieldNormSq (λ site → fieldValue coordinate (pair site Periodic.axis3))))

coordinateBondNormSqExact : ∀ fieldValue coordinate →
  Hodge.bondNormSq (fieldValue coordinate)
  ≡ coordinatePeriodicBondNormSq fieldValue coordinate
coordinateBondNormSqExact fieldValue coordinate
  rewrite globalFieldNormSqMatchesPeriodic
      (λ site → fieldValue coordinate (pair site Periodic.axis0))
        | globalFieldNormSqMatchesPeriodic
      (λ site → fieldValue coordinate (pair site Periodic.axis1))
        | globalFieldNormSqMatchesPeriodic
      (λ site → fieldValue coordinate (pair site Periodic.axis2))
        | globalFieldNormSqMatchesPeriodic
      (λ site → fieldValue coordinate (pair site Periodic.axis3)) =
  refl

periodicPhysicalBondNormSq : Coordinates.PhysicalSU2BondField4 → ℚ
periodicPhysicalBondNormSq fieldValue =
  axisInsertionNormSq fieldValue Periodic.axis0
  + (axisInsertionNormSq fieldValue Periodic.axis1
  + (axisInsertionNormSq fieldValue Periodic.axis2
  + axisInsertionNormSq fieldValue Periodic.axis3))

periodicPhysicalBondNormSqExact : ∀ fieldValue →
  periodicPhysicalBondNormSq fieldValue
  ≡ Coordinates.physicalSU2BondNormSq fieldValue
periodicPhysicalBondNormSqExact fieldValue
  rewrite axisInsertionNormSqExact fieldValue Periodic.axis0
        | axisInsertionNormSqExact fieldValue Periodic.axis1
        | axisInsertionNormSqExact fieldValue Periodic.axis2
        | axisInsertionNormSqExact fieldValue Periodic.axis3
        | coordinateBondNormSqExact fieldValue Coordinates.coordinateX
        | coordinateBondNormSqExact fieldValue Coordinates.coordinateY
        | coordinateBondNormSqExact fieldValue Coordinates.coordinateZ =
  ℚRing.solve-∀
    (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateX (pair site Periodic.axis0)))
    (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateX (pair site Periodic.axis1)))
    (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateX (pair site Periodic.axis2)))
    (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateX (pair site Periodic.axis3)))
    (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateY (pair site Periodic.axis0)))
    (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateY (pair site Periodic.axis1)))
    (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateY (pair site Periodic.axis2)))
    (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateY (pair site Periodic.axis3)))
    (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateZ (pair site Periodic.axis0)))
    (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateZ (pair site Periodic.axis1)))
    (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateZ (pair site Periodic.axis2)))
    (Periodic.fieldNormSq
      (λ site → fieldValue Coordinates.coordinateZ (pair site Periodic.axis3)))

------------------------------------------------------------------------
-- Global gauge-derivative defect and uniform inverse-link radius.
------------------------------------------------------------------------

globalGaugeDerivativeDefectEnergy :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → ℚ
globalGaugeDerivativeDefectEnergy background fieldValue =
  Periodic.sumSites
    (Pointwise.pointwiseGaugeDefectEnergy background fieldValue)

globalGaugeLinkDefectCharge :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → ℚ
globalGaugeLinkDefectCharge background fieldValue =
  Periodic.sumSites
    (Pointwise.pointwiseGaugeLinkDefectCharge background fieldValue)

globalGaugeDerivativeDefectBelowLinkCharge :
  ∀ background fieldValue →
  globalGaugeDerivativeDefectEnergy background fieldValue
  ≤ (+ 16 / 1) * globalGaugeLinkDefectCharge background fieldValue
globalGaugeDerivativeDefectBelowLinkCharge background fieldValue =
  let
    raw :
      Periodic.sumSites
        (Pointwise.pointwiseGaugeDefectEnergy background fieldValue)
      ≤ Periodic.sumSites
          (λ site →
            (+ 16 / 1)
            * Pointwise.pointwiseGaugeLinkDefectCharge
                background fieldValue site)
    raw =
      sumSitesMonotone _ _
        (Pointwise.pointwiseGaugeDefectNormSqBound background fieldValue)
  in
  subst
    (λ upper →
      globalGaugeDerivativeDefectEnergy background fieldValue ≤ upper)
    (Periodic.sumSitesScale (+ 16 / 1)
      (Pointwise.pointwiseGaugeLinkDefectCharge background fieldValue))
    raw

UniformInverseLinkDefectSq :
  Physical.RationalSU2Background4 → ℚ → Set
UniformInverseLinkDefectSq background delta =
  ∀ bond →
    Norm.normSq
      (Telescope._-q_ (Physical.inverseLink background bond) Q.oneQ)
    ≤ delta

axisLinkDefectChargeBelow :
  ∀ background fieldValue delta axis site →
  0ℚ ≤ delta →
  UniformInverseLinkDefectSq background delta →
  Pointwise.axisLinkDefectCharge background fieldValue axis site
  ≤ delta
      * Norm.normSq
          (Gauge.insertionQuaternion fieldValue axis
            (Periodic.shiftBackward axis site))
axisLinkDefectChargeBelow
    background fieldValue delta axis site deltaNonnegative radius =
  let
    previousSite = Periodic.shiftBackward axis site
    bond = pair previousSite axis
    insertionNorm =
      Norm.normSq (Gauge.insertionQuaternion fieldValue axis previousSite)

    insertionNonnegative : 0ℚ ≤ insertionNorm
    insertionNonnegative =
      Norm.normSqNonnegative
        (Gauge.insertionQuaternion fieldValue axis previousSite)

    scaled :
      insertionNorm
        * Norm.normSq
            (Telescope._-q_
              (Physical.inverseLink background bond) Q.oneQ)
      ≤ insertionNorm * delta
    scaled =
      Norm.scaleNonnegative insertionNorm insertionNonnegative
        (radius bond)
  in
  subst
    (λ lower → lower ≤ delta * insertionNorm)
    (ℚRing.solve-∀
      (Norm.normSq
        (Telescope._-q_
          (Physical.inverseLink background bond) Q.oneQ))
      insertionNorm)
    (subst
      (λ upper →
        insertionNorm
          * Norm.normSq
              (Telescope._-q_
                (Physical.inverseLink background bond) Q.oneQ)
        ≤ upper)
      (ℚRing.solve-∀ insertionNorm delta)
      scaled)

previousInsertionNormSq :
  Coordinates.PhysicalSU2BondField4 → Periodic.Site4 → ℚ
previousInsertionNormSq fieldValue site =
  Norm.normSq
    (Gauge.insertionQuaternion fieldValue Periodic.axis0
      (Periodic.shiftBackward Periodic.axis0 site))
  + (Norm.normSq
    (Gauge.insertionQuaternion fieldValue Periodic.axis1
      (Periodic.shiftBackward Periodic.axis1 site))
  + (Norm.normSq
    (Gauge.insertionQuaternion fieldValue Periodic.axis2
      (Periodic.shiftBackward Periodic.axis2 site))
  + Norm.normSq
    (Gauge.insertionQuaternion fieldValue Periodic.axis3
      (Periodic.shiftBackward Periodic.axis3 site))))

pointwiseGaugeLinkChargeBelowUniform :
  ∀ background fieldValue delta site →
  0ℚ ≤ delta →
  UniformInverseLinkDefectSq background delta →
  Pointwise.pointwiseGaugeLinkDefectCharge background fieldValue site
  ≤ delta * previousInsertionNormSq fieldValue site
pointwiseGaugeLinkChargeBelowUniform
    background fieldValue delta site deltaNonnegative radius =
  let
    bound0 = axisLinkDefectChargeBelow
      background fieldValue delta Periodic.axis0 site deltaNonnegative radius
    bound1 = axisLinkDefectChargeBelow
      background fieldValue delta Periodic.axis1 site deltaNonnegative radius
    bound2 = axisLinkDefectChargeBelow
      background fieldValue delta Periodic.axis2 site deltaNonnegative radius
    bound3 = axisLinkDefectChargeBelow
      background fieldValue delta Periodic.axis3 site deltaNonnegative radius

    combined =
      ℚP.+-mono-≤ bound0
        (ℚP.+-mono-≤ bound1
          (ℚP.+-mono-≤ bound2 bound3))
  in
  subst
    (λ upper →
      Pointwise.pointwiseGaugeLinkDefectCharge background fieldValue site
      ≤ upper)
    (ℚRing.solve-∀ delta
      (Norm.normSq
        (Gauge.insertionQuaternion fieldValue Periodic.axis0
          (Periodic.shiftBackward Periodic.axis0 site)))
      (Norm.normSq
        (Gauge.insertionQuaternion fieldValue Periodic.axis1
          (Periodic.shiftBackward Periodic.axis1 site)))
      (Norm.normSq
        (Gauge.insertionQuaternion fieldValue Periodic.axis2
          (Periodic.shiftBackward Periodic.axis2 site)))
      (Norm.normSq
        (Gauge.insertionQuaternion fieldValue Periodic.axis3
          (Periodic.shiftBackward Periodic.axis3 site))))
    combined

sumPreviousInsertionNormSqExact : ∀ fieldValue →
  Periodic.sumSites (previousInsertionNormSq fieldValue)
  ≡ periodicPhysicalBondNormSq fieldValue
sumPreviousInsertionNormSqExact fieldValue =
  let
    term0 = λ site →
      Norm.normSq
        (Gauge.insertionQuaternion fieldValue Periodic.axis0 site)
    term1 = λ site →
      Norm.normSq
        (Gauge.insertionQuaternion fieldValue Periodic.axis1 site)
    term2 = λ site →
      Norm.normSq
        (Gauge.insertionQuaternion fieldValue Periodic.axis2 site)
    term3 = λ site →
      Norm.normSq
        (Gauge.insertionQuaternion fieldValue Periodic.axis3 site)
  in
  trans
    (Periodic.sumSitesAdd
      (λ site → term0 (Periodic.shiftBackward Periodic.axis0 site))
      (λ site →
        term1 (Periodic.shiftBackward Periodic.axis1 site)
        + (term2 (Periodic.shiftBackward Periodic.axis2 site)
        + term3 (Periodic.shiftBackward Periodic.axis3 site))))
    (cong₂ _+_
      (Periodic.sumSitesBackwardInvariant term0 Periodic.axis0)
      (trans
        (Periodic.sumSitesAdd
          (λ site → term1 (Periodic.shiftBackward Periodic.axis1 site))
          (λ site →
            term2 (Periodic.shiftBackward Periodic.axis2 site)
            + term3 (Periodic.shiftBackward Periodic.axis3 site)))
        (cong₂ _+_
          (Periodic.sumSitesBackwardInvariant term1 Periodic.axis1)
          (trans
            (Periodic.sumSitesAdd
              (λ site → term2 (Periodic.shiftBackward Periodic.axis2 site))
              (λ site → term3 (Periodic.shiftBackward Periodic.axis3 site)))
            (cong₂ _+_
              (Periodic.sumSitesBackwardInvariant term2 Periodic.axis2)
              (Periodic.sumSitesBackwardInvariant term3 Periodic.axis3))))))

globalGaugeLinkChargeBelowUniform :
  ∀ background fieldValue delta →
  0ℚ ≤ delta →
  UniformInverseLinkDefectSq background delta →
  globalGaugeLinkDefectCharge background fieldValue
  ≤ delta * Coordinates.physicalSU2BondNormSq fieldValue
globalGaugeLinkChargeBelowUniform
    background fieldValue delta deltaNonnegative radius =
  let
    raw :
      Periodic.sumSites
        (Pointwise.pointwiseGaugeLinkDefectCharge background fieldValue)
      ≤ Periodic.sumSites
          (λ site → delta * previousInsertionNormSq fieldValue site)
    raw =
      sumSitesMonotone _ _
        (λ site →
          pointwiseGaugeLinkChargeBelowUniform
            background fieldValue delta site deltaNonnegative radius)

    scaled :
      Periodic.sumSites
        (λ site → delta * previousInsertionNormSq fieldValue site)
      ≡ delta * periodicPhysicalBondNormSq fieldValue
    scaled =
      trans
        (Periodic.sumSitesScale delta (previousInsertionNormSq fieldValue))
        (cong (delta *_) (sumPreviousInsertionNormSqExact fieldValue))

    physicalScaled :
      delta * periodicPhysicalBondNormSq fieldValue
      ≡ delta * Coordinates.physicalSU2BondNormSq fieldValue
    physicalScaled =
      cong (delta *_) (periodicPhysicalBondNormSqExact fieldValue)
  in
  subst
    (λ upper →
      globalGaugeLinkDefectCharge background fieldValue ≤ upper)
    (trans scaled physicalScaled)
    raw

globalGaugeDerivativeDefectUniformBound :
  ∀ background fieldValue delta →
  0ℚ ≤ delta →
  UniformInverseLinkDefectSq background delta →
  globalGaugeDerivativeDefectEnergy background fieldValue
  ≤ (+ 16 / 1) * delta
      * Coordinates.physicalSU2BondNormSq fieldValue
globalGaugeDerivativeDefectUniformBound
    background fieldValue delta deltaNonnegative radius =
  let
    first = globalGaugeDerivativeDefectBelowLinkCharge background fieldValue
    second = globalGaugeLinkChargeBelowUniform
      background fieldValue delta deltaNonnegative radius

    scaledSecond :
      (+ 16 / 1) * globalGaugeLinkDefectCharge background fieldValue
      ≤ (+ 16 / 1)
          * (delta * Coordinates.physicalSU2BondNormSq fieldValue)
    scaledSecond =
      Norm.scaleNonnegative (+ 16 / 1)
        (ℚP.nonNegative⁻¹ (+ 16 / 1)) second

    combined = ℚP.≤-trans first scaledSecond
  in
  subst
    (λ upper →
      globalGaugeDerivativeDefectEnergy background fieldValue ≤ upper)
    (ℚRing.solve-∀ delta (Coordinates.physicalSU2BondNormSq fieldValue))
    combined

physicalPeriodicGaugeNormCompatibilityLevel : ProofLevel
physicalPeriodicGaugeNormCompatibilityLevel = machineChecked

physicalBackgroundGaugeGlobalDefectLevel : ProofLevel
physicalBackgroundGaugeGlobalDefectLevel = machineChecked

physicalSelectedBackgroundInverseLinkRadiusLevel : ProofLevel
physicalSelectedBackgroundInverseLinkRadiusLevel = conditional
