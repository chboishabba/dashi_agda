module DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact where

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
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Construct the literal covariant backward-divergence first derivative on the
-- side-four physical SU(2) field:
--
--   D F_A[h](x)
--     = sum_mu (h_mu(x)
--       - Ad_{U_mu(x-mu)^-1} h_mu(x-mu)).
--
-- At the identity background this reduces definitionally, after exact
-- quaternion arithmetic, to the already-proved periodic flat divergence.
-- For a general background the difference from the flat derivative is exactly
-- the negative sum of four concrete adjoint defects.  Combined with
-- BalabanP33QuaternionAdjointPerturbationExact, every such defect is already
-- split into two explicit link-difference products.
--
-- The remaining G-local task is quantitative: prove the norm estimate for
-- these terms and its global incidence constant.  The derivative itself is no
-- longer an abstract producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatWilsonCurlIdentificationExact as FlatField
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope

axes4 : List Periodic.Axis4
axes4 =
  Periodic.axis0 ∷ Periodic.axis1 ∷
  Periodic.axis2 ∷ Periodic.axis3 ∷ []

quaternionCoordinate :
  Coordinates.LieCoordinate3 → Q.RationalQuaternion → ℚ
quaternionCoordinate Coordinates.coordinateX value = Q.q1 value
quaternionCoordinate Coordinates.coordinateY value = Q.q2 value
quaternionCoordinate Coordinates.coordinateZ value = Q.q3 value

quaternionCoordinateSubtractExact :
  ∀ coordinate left right →
  quaternionCoordinate coordinate (Telescope._-q_ left right)
  ≡ quaternionCoordinate coordinate left
    - quaternionCoordinate coordinate right
quaternionCoordinateSubtractExact
    Coordinates.coordinateX
    (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3) =
  ℚRing.solve-∀ a1 b1
quaternionCoordinateSubtractExact
    Coordinates.coordinateY
    (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3) =
  ℚRing.solve-∀ a2 b2
quaternionCoordinateSubtractExact
    Coordinates.coordinateZ
    (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3) =
  ℚRing.solve-∀ a3 b3

insertionQuaternion :
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Site4 →
  Q.RationalQuaternion
insertionQuaternion field axis site =
  Q.pureQuaternion (FlatField.insertionAt field axis site)

insertionQuaternionCoordinateExact :
  ∀ field coordinate axis site →
  quaternionCoordinate coordinate (insertionQuaternion field axis site)
  ≡ field coordinate (pair site axis)
insertionQuaternionCoordinateExact field Coordinates.coordinateX axis site = refl
insertionQuaternionCoordinateExact field Coordinates.coordinateY axis site = refl
insertionQuaternionCoordinateExact field Coordinates.coordinateZ axis site = refl

backwardTransportUnit :
  Physical.RationalSU2Background4 →
  Periodic.Axis4 → Periodic.Site4 →
  Q.RationalQuaternion
backwardTransportUnit background axis site =
  Physical.inverseLink background
    (pair (Periodic.shiftBackward axis site) axis)

transportedPreviousInsertion :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Site4 →
  Q.RationalQuaternion
transportedPreviousInsertion background field axis site =
  Adjoint.adjointTransport
    (backwardTransportUnit background axis site)
    (insertionQuaternion field axis
      (Periodic.shiftBackward axis site))

backgroundBackwardTerm :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Coordinates.LieCoordinate3 →
  Periodic.Axis4 → Periodic.Site4 → ℚ
backgroundBackwardTerm background field coordinate axis site =
  field coordinate (pair site axis)
  - quaternionCoordinate coordinate
      (transportedPreviousInsertion background field axis site)

flatBackwardTerm :
  Coordinates.PhysicalSU2BondField4 →
  Coordinates.LieCoordinate3 →
  Periodic.Axis4 → Periodic.Site4 → ℚ
flatBackwardTerm field coordinate axis site =
  field coordinate (pair site axis)
  - field coordinate
      (pair (Periodic.shiftBackward axis site) axis)

backgroundGaugeFirst :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  FlatGauge.GaugeCoordinate4 → ℚ
backgroundGaugeFirst background field (pair coordinate site) =
  Sums.sumRational axes4
    (λ axis →
      backgroundBackwardTerm background field coordinate axis site)

flatGaugeFirstFromAxes :
  Coordinates.PhysicalSU2BondField4 →
  FlatGauge.GaugeCoordinate4 → ℚ
flatGaugeFirstFromAxes field (pair coordinate site) =
  Sums.sumRational axes4
    (λ axis → flatBackwardTerm field coordinate axis site)

flatGaugeFirstFromAxesIsPeriodicDivergence :
  ∀ field coordinate site →
  flatGaugeFirstFromAxes field (pair coordinate site)
  ≡ FlatGauge.flatGaugeFirst field (pair coordinate site)
flatGaugeFirstFromAxesIsPeriodicDivergence field coordinate site =
  ℚRing.solve-∀
    (field coordinate (pair site Periodic.axis0))
    (field coordinate
      (pair (Periodic.shiftBackward Periodic.axis0 site) Periodic.axis0))
    (field coordinate (pair site Periodic.axis1))
    (field coordinate
      (pair (Periodic.shiftBackward Periodic.axis1 site) Periodic.axis1))
    (field coordinate (pair site Periodic.axis2))
    (field coordinate
      (pair (Periodic.shiftBackward Periodic.axis2 site) Periodic.axis2))
    (field coordinate (pair site Periodic.axis3))
    (field coordinate
      (pair (Periodic.shiftBackward Periodic.axis3 site) Periodic.axis3))

identityAdjointCoordinateExact :
  ∀ coordinate value →
  quaternionCoordinate coordinate
    (Adjoint.adjointTransport Q.oneQ value)
  ≡ quaternionCoordinate coordinate value
identityAdjointCoordinateExact Coordinates.coordinateX
    (Q.quat x0 x1 x2 x3) =
  ℚRing.solve-∀ x0 x1 x2 x3
identityAdjointCoordinateExact Coordinates.coordinateY
    (Q.quat x0 x1 x2 x3) =
  ℚRing.solve-∀ x0 x1 x2 x3
identityAdjointCoordinateExact Coordinates.coordinateZ
    (Q.quat x0 x1 x2 x3) =
  ℚRing.solve-∀ x0 x1 x2 x3

identityBackgroundBackwardTermExact :
  ∀ field coordinate axis site →
  backgroundBackwardTerm
    Physical.identityBackground field coordinate axis site
  ≡ flatBackwardTerm field coordinate axis site
identityBackgroundBackwardTermExact field coordinate axis site =
  let
    previousSite = Periodic.shiftBackward axis site
    previousInsertion = insertionQuaternion field axis previousSite

    transportedExact :
      quaternionCoordinate coordinate
        (Adjoint.adjointTransport Q.oneQ previousInsertion)
      ≡ field coordinate (pair previousSite axis)
    transportedExact =
      trans
        (identityAdjointCoordinateExact coordinate previousInsertion)
        (insertionQuaternionCoordinateExact
          field coordinate axis previousSite)
  in
  cong
    (field coordinate (pair site axis) -_)
    transportedExact

identityBackgroundGaugeFirstIsFlatAxes :
  ∀ field coordinate site →
  backgroundGaugeFirst
    Physical.identityBackground field (pair coordinate site)
  ≡ flatGaugeFirstFromAxes field (pair coordinate site)
identityBackgroundGaugeFirstIsFlatAxes field coordinate site =
  Sums.sumRationalCong
    axes4
    (λ axis →
      backgroundBackwardTerm
        Physical.identityBackground field coordinate axis site)
    (λ axis → flatBackwardTerm field coordinate axis site)
    (λ axis →
      identityBackgroundBackwardTermExact
        field coordinate axis site)

identityBackgroundGaugeFirstIsPeriodicDivergence :
  ∀ field coordinate site →
  backgroundGaugeFirst
    Physical.identityBackground field (pair coordinate site)
  ≡ FlatGauge.flatGaugeFirst field (pair coordinate site)
identityBackgroundGaugeFirstIsPeriodicDivergence field coordinate site =
  trans
    (identityBackgroundGaugeFirstIsFlatAxes field coordinate site)
    (flatGaugeFirstFromAxesIsPeriodicDivergence field coordinate site)

axisAdjointDefect :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Periodic.Axis4 → Periodic.Site4 →
  Q.RationalQuaternion
axisAdjointDefect background field axis site =
  Adjoint.adjointDefect
    (backwardTransportUnit background axis site)
    (insertionQuaternion field axis
      (Periodic.shiftBackward axis site))

axisAdjointDefectFactorizationExact :
  ∀ background field axis site →
  axisAdjointDefect background field axis site
  ≡ Adjoint.adjointDefectFactorization
      (backwardTransportUnit background axis site)
      (insertionQuaternion field axis
        (Periodic.shiftBackward axis site))
axisAdjointDefectFactorizationExact background field axis site =
  Adjoint.adjointDefectFactorizationExact
    (backwardTransportUnit background axis site)
    (insertionQuaternion field axis
      (Periodic.shiftBackward axis site))

axisAdjointDefectCoordinate :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Coordinates.LieCoordinate3 →
  Periodic.Axis4 → Periodic.Site4 → ℚ
axisAdjointDefectCoordinate background field coordinate axis site =
  quaternionCoordinate coordinate
    (axisAdjointDefect background field axis site)

backgroundMinusFlatAxisExact :
  ∀ background field coordinate axis site →
  backgroundBackwardTerm background field coordinate axis site
    - flatBackwardTerm field coordinate axis site
  ≡ - axisAdjointDefectCoordinate
      background field coordinate axis site
backgroundMinusFlatAxisExact background field coordinate axis site =
  let
    previousSite = Periodic.shiftBackward axis site
    unit = backwardTransportUnit background axis site
    previousInsertion = insertionQuaternion field axis previousSite
    transported = Adjoint.adjointTransport unit previousInsertion

    defectCoordinateExact :
      axisAdjointDefectCoordinate background field coordinate axis site
      ≡ quaternionCoordinate coordinate transported
        - field coordinate (pair previousSite axis)
    defectCoordinateExact =
      trans
        (quaternionCoordinateSubtractExact
          coordinate transported previousInsertion)
        (cong
          (quaternionCoordinate coordinate transported -_)
          (insertionQuaternionCoordinateExact
            field coordinate axis previousSite))
  in
  subst
    (λ defectValue →
      backgroundBackwardTerm background field coordinate axis site
        - flatBackwardTerm field coordinate axis site
      ≡ - defectValue)
    (sym defectCoordinateExact)
    (ℚRing.solve-∀
      (field coordinate (pair site axis))
      (quaternionCoordinate coordinate transported)
      (field coordinate (pair previousSite axis)))

backgroundGaugeFirstMinusFlatExact :
  ∀ background field coordinate site →
  backgroundGaugeFirst background field (pair coordinate site)
    - flatGaugeFirstFromAxes field (pair coordinate site)
  ≡ -
    Sums.sumRational axes4
      (λ axis →
        axisAdjointDefectCoordinate
          background field coordinate axis site)
backgroundGaugeFirstMinusFlatExact
    background field coordinate site =
  let
    backgroundTerm =
      λ axis →
        backgroundBackwardTerm background field coordinate axis site
    flatTerm =
      λ axis → flatBackwardTerm field coordinate axis site
    defectTerm =
      λ axis →
        axisAdjointDefectCoordinate
          background field coordinate axis site

    distributeDifference :
      backgroundGaugeFirst background field (pair coordinate site)
        - flatGaugeFirstFromAxes field (pair coordinate site)
      ≡ Sums.sumRational axes4
          (λ axis → backgroundTerm axis - flatTerm axis)
    distributeDifference =
      ℚRing.solve-∀
        (backgroundTerm Periodic.axis0)
        (backgroundTerm Periodic.axis1)
        (backgroundTerm Periodic.axis2)
        (backgroundTerm Periodic.axis3)
        (flatTerm Periodic.axis0)
        (flatTerm Periodic.axis1)
        (flatTerm Periodic.axis2)
        (flatTerm Periodic.axis3)

    pointwiseDefects :
      Sums.sumRational axes4
        (λ axis → backgroundTerm axis - flatTerm axis)
      ≡ Sums.sumRational axes4 (λ axis → - defectTerm axis)
    pointwiseDefects =
      Sums.sumRationalCong
        axes4
        (λ axis → backgroundTerm axis - flatTerm axis)
        (λ axis → - defectTerm axis)
        (λ axis →
          backgroundMinusFlatAxisExact
            background field coordinate axis site)
  in
  trans distributeDifference
    (trans pointwiseDefects
      (Sums.sumRationalNegate axes4 defectTerm))

physicalBackgroundGaugeFirstLevel : ProofLevel
physicalBackgroundGaugeFirstLevel = machineChecked

physicalBackgroundGaugeFlatSpecializationLevel : ProofLevel
physicalBackgroundGaugeFlatSpecializationLevel = machineChecked

physicalBackgroundGaugeDefectFactorizationLevel : ProofLevel
physicalBackgroundGaugeDefectFactorizationLevel = machineChecked

physicalBackgroundGaugeDefectNormLevel : ProofLevel
physicalBackgroundGaugeDefectNormLevel = conditional
