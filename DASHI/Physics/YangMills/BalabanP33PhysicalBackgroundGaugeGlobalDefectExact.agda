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

periodicFieldNormSqMatchesGlobal : ∀ field →
  Periodic.fieldNormSq field ≡ Variance.globalNormSq field
periodicFieldNormSqMatchesGlobal field =
  trans
    (periodicSumSitesMatchesCoordinateSum4
      (λ site → field site * field site))
    (sym
      (Partition.globalSiteSumMatchesCoordinateSum4
        (λ site → field site * field site)))

globalFieldNormSqMatchesPeriodic : ∀ field →
  Variance.globalNormSq field ≡ Periodic.fieldNormSq field
globalFieldNormSqMatchesPeriodic field =
  sym (periodicFieldNormSqMatchesGlobal field)

insertionNormSqPointwiseExact :
  ∀ field axis site →
  Norm.normSq (Gauge.insertionQuaternion field axis site)
  ≡
    field Coordinates.coordinateX (pair site axis)
      * field Coordinates.coordinateX (pair site axis)
    + (field Coordinates.coordinateY (pair site axis)
      * field Coordinates.coordinateY (pair site axis)
    + field Coordinates.coordinateZ (pair site axis)
      * field Coordinates.coordinateZ (pair site axis))
insertionNormSqPointwiseExact field axis site =
  ℚRing.solve-∀
    (field Coordinates.coordinateX (pair site axis))
    (field Coordinates.coordinateY (pair site axis))
    (field Coordinates.coordinateZ (pair site axis))

axisInsertionNormSq :
  Coordinates.PhysicalSU2BondField4 → Periodic.Axis4 → ℚ
axisInsertionNormSq field axis =
  Periodic.sumSites
    (λ site → Norm.normSq (Gauge.insertionQuaternion field axis site))

axisInsertionNormSqExact : ∀ field axis →
  axisInsertionNormSq field axis
  ≡ Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateX (pair site axis))
    + (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateY (pair site axis))
    + Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateZ (pair site axis)))
axisInsertionNormSqExact field axis =
  trans
    (Periodic.sumSitesCong _ _
      (insertionNormSqPointwiseExact field axis))
    (trans
      (Periodic.sumSitesAdd
        (λ site →
          field Coordinates.coordinateX (pair site axis)
          * field Coordinates.coordinateX (pair site axis))
        (λ site →
          field Coordinates.coordinateY (pair site axis)
            * field Coordinates.coordinateY (pair site axis)
          + field Coordinates.coordinateZ (pair site axis)
            * field Coordinates.coordinateZ (pair site axis)))
      (cong₂ _+_ refl
        (Periodic.sumSitesAdd
          (λ site →
            field Coordinates.coordinateY (pair site axis)
            * field Coordinates.coordinateY (pair site axis))
          (λ site →
            field Coordinates.coordinateZ (pair site axis)
            * field Coordinates.coordinateZ (pair site axis)))))

coordinatePeriodicBondNormSq :
  Coordinates.PhysicalSU2BondField4 → Coordinates.LieCoordinate3 → ℚ
coordinatePeriodicBondNormSq field coordinate =
  Periodic.fieldNormSq (λ site → field coordinate (pair site Periodic.axis0))
  + (Periodic.fieldNormSq (λ site → field coordinate (pair site Periodic.axis1))
  + (Periodic.fieldNormSq (λ site → field coordinate (pair site Periodic.axis2))
  + Periodic.fieldNormSq (λ site → field coordinate (pair site Periodic.axis3))))

coordinateBondNormSqExact : ∀ field coordinate →
  Hodge.bondNormSq (field coordinate)
  ≡ coordinatePeriodicBondNormSq field coordinate
coordinateBondNormSqExact field coordinate
  rewrite globalFieldNormSqMatchesPeriodic
      (λ site → field coordinate (pair site Periodic.axis0))
        | globalFieldNormSqMatchesPeriodic
      (λ site → field coordinate (pair site Periodic.axis1))
        | globalFieldNormSqMatchesPeriodic
      (λ site → field coordinate (pair site Periodic.axis2))
        | globalFieldNormSqMatchesPeriodic
      (λ site → field coordinate (pair site Periodic.axis3)) =
  refl

periodicPhysicalBondNormSq : Coordinates.PhysicalSU2BondField4 → ℚ
periodicPhysicalBondNormSq field =
  axisInsertionNormSq field Periodic.axis0
  + (axisInsertionNormSq field Periodic.axis1
  + (axisInsertionNormSq field Periodic.axis2
  + axisInsertionNormSq field Periodic.axis3))

periodicPhysicalBondNormSqExact : ∀ field →
  periodicPhysicalBondNormSq field
  ≡ Coordinates.physicalSU2BondNormSq field
periodicPhysicalBondNormSqExact field
  rewrite axisInsertionNormSqExact field Periodic.axis0
        | axisInsertionNormSqExact field Periodic.axis1
        | axisInsertionNormSqExact field Periodic.axis2
        | axisInsertionNormSqExact field Periodic.axis3
        | coordinateBondNormSqExact field Coordinates.coordinateX
        | coordinateBondNormSqExact field Coordinates.coordinateY
        | coordinateBondNormSqExact field Coordinates.coordinateZ =
  ℚRing.solve-∀
    (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateX (pair site Periodic.axis0)))
    (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateX (pair site Periodic.axis1)))
    (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateX (pair site Periodic.axis2)))
    (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateX (pair site Periodic.axis3)))
    (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateY (pair site Periodic.axis0)))
    (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateY (pair site Periodic.axis1)))
    (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateY (pair site Periodic.axis2)))
    (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateY (pair site Periodic.axis3)))
    (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateZ (pair site Periodic.axis0)))
    (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateZ (pair site Periodic.axis1)))
    (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateZ (pair site Periodic.axis2)))
    (Periodic.fieldNormSq
      (λ site → field Coordinates.coordinateZ (pair site Periodic.axis3)))

------------------------------------------------------------------------
-- Global gauge-derivative defect and uniform inverse-link radius.
------------------------------------------------------------------------

globalGaugeDerivativeDefectEnergy :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → ℚ
globalGaugeDerivativeDefectEnergy background field =
  Periodic.sumSites
    (Pointwise.pointwiseGaugeDefectEnergy background field)

globalGaugeLinkDefectCharge :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 → ℚ
globalGaugeLinkDefectCharge background field =
  Periodic.sumSites
    (Pointwise.pointwiseGaugeLinkDefectCharge background field)

globalGaugeDerivativeDefectBelowLinkCharge :
  ∀ background field →
  globalGaugeDerivativeDefectEnergy background field
  ≤ (+ 16 / 1) * globalGaugeLinkDefectCharge background field
globalGaugeDerivativeDefectBelowLinkCharge background field =
  let
    raw :
      Periodic.sumSites
        (Pointwise.pointwiseGaugeDefectEnergy background field)
      ≤ Periodic.sumSites
          (λ site →
            (+ 16 / 1)
            * Pointwise.pointwiseGaugeLinkDefectCharge
                background field site)
    raw =
      sumSitesMonotone _ _
        (Pointwise.pointwiseGaugeDefectNormSqBound background field)
  in
  subst
    (λ upper →
      globalGaugeDerivativeDefectEnergy background field ≤ upper)
    (Periodic.sumSitesScale (+ 16 / 1)
      (Pointwise.pointwiseGaugeLinkDefectCharge background field))
    raw

UniformInverseLinkDefectSq :
  Physical.RationalSU2Background4 → ℚ → Set
UniformInverseLinkDefectSq background delta =
  ∀ bond →
    Norm.normSq
      (Telescope._-q_ (Physical.inverseLink background bond) Q.oneQ)
    ≤ delta

axisLinkDefectChargeBelow :
  ∀ background field delta axis site →
  0ℚ ≤ delta →
  UniformInverseLinkDefectSq background delta →
  Pointwise.axisLinkDefectCharge background field axis site
  ≤ delta
      * Norm.normSq
          (Gauge.insertionQuaternion field axis
            (Periodic.shiftBackward axis site))
axisLinkDefectChargeBelow
    background field delta axis site deltaNonnegative radius =
  let
    previousSite = Periodic.shiftBackward axis site
    bond = pair previousSite axis
    insertionNorm =
      Norm.normSq (Gauge.insertionQuaternion field axis previousSite)

    insertionNonnegative : 0ℚ ≤ insertionNorm
    insertionNonnegative =
      Norm.normSqNonnegative
        (Gauge.insertionQuaternion field axis previousSite)

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
previousInsertionNormSq field site =
  Norm.normSq
    (Gauge.insertionQuaternion field Periodic.axis0
      (Periodic.shiftBackward Periodic.axis0 site))
  + (Norm.normSq
    (Gauge.insertionQuaternion field Periodic.axis1
      (Periodic.shiftBackward Periodic.axis1 site))
  + (Norm.normSq
    (Gauge.insertionQuaternion field Periodic.axis2
      (Periodic.shiftBackward Periodic.axis2 site))
  + Norm.normSq
    (Gauge.insertionQuaternion field Periodic.axis3
      (Periodic.shiftBackward Periodic.axis3 site))))

pointwiseGaugeLinkChargeBelowUniform :
  ∀ background field delta site →
  0ℚ ≤ delta →
  UniformInverseLinkDefectSq background delta →
  Pointwise.pointwiseGaugeLinkDefectCharge background field site
  ≤ delta * previousInsertionNormSq field site
pointwiseGaugeLinkChargeBelowUniform
    background field delta site deltaNonnegative radius =
  let
    bound0 = axisLinkDefectChargeBelow
      background field delta Periodic.axis0 site deltaNonnegative radius
    bound1 = axisLinkDefectChargeBelow
      background field delta Periodic.axis1 site deltaNonnegative radius
    bound2 = axisLinkDefectChargeBelow
      background field delta Periodic.axis2 site deltaNonnegative radius
    bound3 = axisLinkDefectChargeBelow
      background field delta Periodic.axis3 site deltaNonnegative radius

    combined =
      ℚP.+-mono-≤ bound0
        (ℚP.+-mono-≤ bound1
          (ℚP.+-mono-≤ bound2 bound3))
  in
  subst
    (λ upper →
      Pointwise.pointwiseGaugeLinkDefectCharge background field site
      ≤ upper)
    (ℚRing.solve-∀ delta
      (Norm.normSq
        (Gauge.insertionQuaternion field Periodic.axis0
          (Periodic.shiftBackward Periodic.axis0 site)))
      (Norm.normSq
        (Gauge.insertionQuaternion field Periodic.axis1
          (Periodic.shiftBackward Periodic.axis1 site)))
      (Norm.normSq
        (Gauge.insertionQuaternion field Periodic.axis2
          (Periodic.shiftBackward Periodic.axis2 site)))
      (Norm.normSq
        (Gauge.insertionQuaternion field Periodic.axis3
          (Periodic.shiftBackward Periodic.axis3 site))))
    combined

sumPreviousInsertionNormSqExact : ∀ field →
  Periodic.sumSites (previousInsertionNormSq field)
  ≡ periodicPhysicalBondNormSq field
sumPreviousInsertionNormSqExact field =
  let
    term0 = λ site →
      Norm.normSq
        (Gauge.insertionQuaternion field Periodic.axis0 site)
    term1 = λ site →
      Norm.normSq
        (Gauge.insertionQuaternion field Periodic.axis1 site)
    term2 = λ site →
      Norm.normSq
        (Gauge.insertionQuaternion field Periodic.axis2 site)
    term3 = λ site →
      Norm.normSq
        (Gauge.insertionQuaternion field Periodic.axis3 site)
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
  ∀ background field delta →
  0ℚ ≤ delta →
  UniformInverseLinkDefectSq background delta →
  globalGaugeLinkDefectCharge background field
  ≤ delta * Coordinates.physicalSU2BondNormSq field
globalGaugeLinkChargeBelowUniform
    background field delta deltaNonnegative radius =
  let
    raw :
      Periodic.sumSites
        (Pointwise.pointwiseGaugeLinkDefectCharge background field)
      ≤ Periodic.sumSites
          (λ site → delta * previousInsertionNormSq field site)
    raw =
      sumSitesMonotone _ _
        (λ site →
          pointwiseGaugeLinkChargeBelowUniform
            background field delta site deltaNonnegative radius)

    scaled :
      Periodic.sumSites
        (λ site → delta * previousInsertionNormSq field site)
      ≡ delta * periodicPhysicalBondNormSq field
    scaled =
      trans
        (Periodic.sumSitesScale delta (previousInsertionNormSq field))
        (cong (delta *_) (sumPreviousInsertionNormSqExact field))

    physicalScaled :
      delta * periodicPhysicalBondNormSq field
      ≡ delta * Coordinates.physicalSU2BondNormSq field
    physicalScaled =
      cong (delta *_) (periodicPhysicalBondNormSqExact field)
  in
  subst
    (λ upper →
      globalGaugeLinkDefectCharge background field ≤ upper)
    (trans scaled physicalScaled)
    raw

globalGaugeDerivativeDefectUniformBound :
  ∀ background field delta →
  0ℚ ≤ delta →
  UniformInverseLinkDefectSq background delta →
  globalGaugeDerivativeDefectEnergy background field
  ≤ (+ 16 / 1) * delta
      * Coordinates.physicalSU2BondNormSq field
globalGaugeDerivativeDefectUniformBound
    background field delta deltaNonnegative radius =
  let
    first = globalGaugeDerivativeDefectBelowLinkCharge background field
    second = globalGaugeLinkChargeBelowUniform
      background field delta deltaNonnegative radius

    scaledSecond :
      (+ 16 / 1) * globalGaugeLinkDefectCharge background field
      ≤ (+ 16 / 1)
          * (delta * Coordinates.physicalSU2BondNormSq field)
    scaledSecond =
      Norm.scaleNonnegative (+ 16 / 1)
        (ℚP.nonNegative⁻¹ (+ 16 / 1)) second

    combined = ℚP.≤-trans first scaledSecond
  in
  subst
    (λ upper →
      globalGaugeDerivativeDefectEnergy background field ≤ upper)
    (ℚRing.solve-∀ delta (Coordinates.physicalSU2BondNormSq field))
    combined

physicalPeriodicGaugeNormCompatibilityLevel : ProofLevel
physicalPeriodicGaugeNormCompatibilityLevel = machineChecked

physicalBackgroundGaugeGlobalDefectLevel : ProofLevel
physicalBackgroundGaugeGlobalDefectLevel = machineChecked

physicalSelectedBackgroundInverseLinkRadiusLevel : ProofLevel
physicalSelectedBackgroundInverseLinkRadiusLevel = conditional
