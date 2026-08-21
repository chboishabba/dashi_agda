module DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovDefectFactorizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
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
-- Factor the literal physical background ghost defect before any Taylor or
-- determinant expansion.  With
--
--   M_A = D_A G_A,     M_0 = D_0 G_0,
--
-- exact finite algebra gives
--
--   M_A - M_0
--     = (D_A-D_0) G_A + D_0 (G_A-G_0).
--
-- Both pieces are then identified with explicit SU(2) adjoint defects.  Thus
-- every background dependence entering the reduced trace-log expansion is
-- source-native: no anonymous perturbation operator E_A is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact as FP

forwardOrbitAdjointDefect :
  Physical.RationalSU2Background4 → FP.SiteGaugeParameter4 →
  Periodic.Axis4 → Periodic.Site4 → Q.RationalQuaternion
forwardOrbitAdjointDefect background parameter axis site =
  Adjoint.adjointDefect
    (Physical.link background (pair site axis))
    (FP.parameterQuaternion parameter (Periodic.shiftForward axis site))

forwardOrbitAdjointDefectCoordinate :
  Physical.RationalSU2Background4 → FP.SiteGaugeParameter4 →
  Coordinates.LieCoordinate3 → Periodic.Axis4 → Periodic.Site4 → ℚ
forwardOrbitAdjointDefectCoordinate background parameter coordinate axis site =
  Gauge.quaternionCoordinate coordinate
    (forwardOrbitAdjointDefect background parameter axis site)

backgroundGaugeOrbitMinusFlatExact :
  ∀ background parameter coordinate site axis →
  FP.backgroundGaugeOrbitFirst background parameter coordinate (pair site axis)
    - FP.flatGaugeOrbitFirst parameter coordinate (pair site axis)
  ≡ - forwardOrbitAdjointDefectCoordinate
      background parameter coordinate axis site
backgroundGaugeOrbitMinusFlatExact background parameter coordinate site axis =
  let
    forward = Periodic.shiftForward axis site
    unit = Physical.link background (pair site axis)
    value = FP.parameterQuaternion parameter forward
    transported = Adjoint.adjointTransport unit value

    defectCoordinateExact :
      forwardOrbitAdjointDefectCoordinate
        background parameter coordinate axis site
      ≡ Gauge.quaternionCoordinate coordinate transported
        - parameter (pair coordinate forward)
    defectCoordinateExact =
      trans
        (Gauge.quaternionCoordinateSubtractExact
          coordinate transported value)
        (cong
          (Gauge.quaternionCoordinate coordinate transported -_)
          (FP.parameterQuaternionCoordinateExact parameter coordinate forward))
  in
  trans
    (ℚRing.solve-∀
      (parameter (pair coordinate site))
      (Gauge.quaternionCoordinate coordinate transported)
      (parameter (pair coordinate forward)))
    (cong -_ (sym defectCoordinateExact))

orbitDefectField :
  Physical.RationalSU2Background4 → FP.SiteGaugeParameter4 →
  Coordinates.PhysicalSU2BondField4
orbitDefectField background parameter coordinate (pair site axis) =
  FP.backgroundGaugeOrbitFirst background parameter coordinate (pair site axis)
  - FP.flatGaugeOrbitFirst parameter coordinate (pair site axis)

orbitDefectFieldIsNegativeAdjointDefect :
  ∀ background parameter coordinate site axis →
  orbitDefectField background parameter coordinate (pair site axis)
  ≡ - forwardOrbitAdjointDefectCoordinate
      background parameter coordinate axis site
orbitDefectFieldIsNegativeAdjointDefect = backgroundGaugeOrbitMinusFlatExact

flatGaugeFirstDifferenceExact :
  ∀ left right coordinate site →
  Gauge.flatGaugeFirstFromAxes left (pair coordinate site)
    - Gauge.flatGaugeFirstFromAxes right (pair coordinate site)
  ≡ Gauge.flatGaugeFirstFromAxes
      (λ selected bond → left selected bond - right selected bond)
      (pair coordinate site)
flatGaugeFirstDifferenceExact left right coordinate site =
  ℚRing.solve-∀
    (left coordinate (pair site Periodic.axis0))
    (left coordinate
      (pair (Periodic.shiftBackward Periodic.axis0 site) Periodic.axis0))
    (left coordinate (pair site Periodic.axis1))
    (left coordinate
      (pair (Periodic.shiftBackward Periodic.axis1 site) Periodic.axis1))
    (left coordinate (pair site Periodic.axis2))
    (left coordinate
      (pair (Periodic.shiftBackward Periodic.axis2 site) Periodic.axis2))
    (left coordinate (pair site Periodic.axis3))
    (left coordinate
      (pair (Periodic.shiftBackward Periodic.axis3 site) Periodic.axis3))
    (right coordinate (pair site Periodic.axis0))
    (right coordinate
      (pair (Periodic.shiftBackward Periodic.axis0 site) Periodic.axis0))
    (right coordinate (pair site Periodic.axis1))
    (right coordinate
      (pair (Periodic.shiftBackward Periodic.axis1 site) Periodic.axis1))
    (right coordinate (pair site Periodic.axis2))
    (right coordinate
      (pair (Periodic.shiftBackward Periodic.axis2 site) Periodic.axis2))
    (right coordinate (pair site Periodic.axis3))
    (right coordinate
      (pair (Periodic.shiftBackward Periodic.axis3 site) Periodic.axis3))

faddeevPopovDefectFirstPiece :
  Physical.RationalSU2Background4 → FP.SiteGaugeParameter4 →
  Coordinates.LieCoordinate3 → Periodic.Site4 → ℚ
faddeevPopovDefectFirstPiece background parameter coordinate site =
  - Sums.sumRational Gauge.axes4
      (λ axis →
        Gauge.axisAdjointDefectCoordinate
          background
          (FP.backgroundGaugeOrbitFirst background parameter)
          coordinate axis site)

faddeevPopovDefectSecondPiece :
  Physical.RationalSU2Background4 → FP.SiteGaugeParameter4 →
  Coordinates.LieCoordinate3 → Periodic.Site4 → ℚ
faddeevPopovDefectSecondPiece background parameter coordinate site =
  Gauge.flatGaugeFirstFromAxes
    (orbitDefectField background parameter)
    (pair coordinate site)

faddeevPopovBackgroundMinusFlatExact :
  ∀ background parameter coordinate site →
  FP.faddeevPopovApply background parameter (pair coordinate site)
    - FP.flatFaddeevPopovApply parameter (pair coordinate site)
  ≡ faddeevPopovDefectFirstPiece background parameter coordinate site
    + faddeevPopovDefectSecondPiece background parameter coordinate site
faddeevPopovBackgroundMinusFlatExact background parameter coordinate site =
  let
    GA = FP.backgroundGaugeOrbitFirst background parameter
    G0 = FP.flatGaugeOrbitFirst parameter

    first :
      Gauge.backgroundGaugeFirst background GA (pair coordinate site)
        - Gauge.flatGaugeFirstFromAxes GA (pair coordinate site)
      ≡ faddeevPopovDefectFirstPiece background parameter coordinate site
    first = Gauge.backgroundGaugeFirstMinusFlatExact
      background GA coordinate site

    second :
      Gauge.flatGaugeFirstFromAxes GA (pair coordinate site)
        - Gauge.flatGaugeFirstFromAxes G0 (pair coordinate site)
      ≡ faddeevPopovDefectSecondPiece background parameter coordinate site
    second = flatGaugeFirstDifferenceExact GA G0 coordinate site
  in
  trans
    (ℚRing.solve-∀
      (Gauge.backgroundGaugeFirst background GA (pair coordinate site))
      (Gauge.flatGaugeFirstFromAxes GA (pair coordinate site))
      (Gauge.flatGaugeFirstFromAxes G0 (pair coordinate site)))
    (cong₂ _+_ first second)

physicalFaddeevPopovDefectTwoTermFactorizationLevel : ProofLevel
physicalFaddeevPopovDefectTwoTermFactorizationLevel = machineChecked

physicalFaddeevPopovOrbitAdjointDefectLevel : ProofLevel
physicalFaddeevPopovOrbitAdjointDefectLevel = machineChecked
