module DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field",
-- Physics Letters B 25 (1967), 29--30.
-- DOI: 10.1016/0370-2693(67)90067-6.
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
-- Construct the literal finite background Faddeev--Popov operator on the same
-- side-four SU(2) carrier already used by the Wilson/KKT development.
--
-- The existing background gauge derivative is the covariant backward
-- divergence
--
--   D_A h(x) = sum_mu [ h_mu(x)
--     - Ad_{U_mu(x-mu)^-1} h_mu(x-mu) ].
--
-- Here we construct the matching infinitesimal gauge-orbit derivative
--
--   (G_A omega)_mu(x)
--     = omega(x) - Ad_{U_mu(x)} omega(x+mu)
--
-- and define the actual finite ghost operator
--
--   M_A omega = D_A (G_A omega).
--
-- At the identity background this specializes exactly to the periodic lattice
-- Laplacian/divergence-of-forward-difference operator.  Thus the ghost
-- quadratic operator is no longer an abstract B1 receipt; determinant/log-det
-- evaluation and its one-loop colour/orbit contribution remain later work.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _-_; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge

------------------------------------------------------------------------
-- Site Lie-algebra parameter and its literal quaternion realization.
------------------------------------------------------------------------

SiteGaugeParameter4 : Set
SiteGaugeParameter4 = Gauge.GaugeCoordinate4 → ℚ

parameterQuaternion :
  SiteGaugeParameter4 → Periodic.Site4 → Q.RationalQuaternion
parameterQuaternion parameter site =
  Q.quat 0ℚ
    (parameter (pair Coordinates.coordinateX site))
    (parameter (pair Coordinates.coordinateY site))
    (parameter (pair Coordinates.coordinateZ site))

parameterQuaternionCoordinateExact :
  ∀ parameter coordinate site →
  Gauge.quaternionCoordinate coordinate (parameterQuaternion parameter site)
  ≡ parameter (pair coordinate site)
parameterQuaternionCoordinateExact parameter Coordinates.coordinateX site = refl
parameterQuaternionCoordinateExact parameter Coordinates.coordinateY site = refl
parameterQuaternionCoordinateExact parameter Coordinates.coordinateZ site = refl

forwardTransportedParameter :
  Physical.RationalSU2Background4 → SiteGaugeParameter4 →
  Periodic.Axis4 → Periodic.Site4 → Q.RationalQuaternion
forwardTransportedParameter background parameter axis site =
  Adjoint.adjointTransport
    (Physical.link background (pair site axis))
    (parameterQuaternion parameter (Periodic.shiftForward axis site))

------------------------------------------------------------------------
-- Literal infinitesimal background gauge-orbit derivative G_A.
------------------------------------------------------------------------

backgroundGaugeOrbitFirst :
  Physical.RationalSU2Background4 → SiteGaugeParameter4 →
  Coordinates.PhysicalSU2BondField4
backgroundGaugeOrbitFirst background parameter coordinate (pair site axis) =
  parameter (pair coordinate site)
  - Gauge.quaternionCoordinate coordinate
      (forwardTransportedParameter background parameter axis site)

flatGaugeOrbitFirst :
  SiteGaugeParameter4 → Coordinates.PhysicalSU2BondField4
flatGaugeOrbitFirst parameter coordinate (pair site axis) =
  parameter (pair coordinate site)
  - parameter (pair coordinate (Periodic.shiftForward axis site))

identityForwardTransportCoordinateExact :
  ∀ parameter coordinate axis site →
  Gauge.quaternionCoordinate coordinate
    (forwardTransportedParameter
      Physical.identityBackground parameter axis site)
  ≡ parameter (pair coordinate (Periodic.shiftForward axis site))
identityForwardTransportCoordinateExact parameter coordinate axis site =
  trans
    (Gauge.identityAdjointCoordinateExact coordinate
      (parameterQuaternion parameter (Periodic.shiftForward axis site)))
    (parameterQuaternionCoordinateExact
      parameter coordinate (Periodic.shiftForward axis site))

identityGaugeOrbitFirstExact :
  ∀ parameter coordinate site axis →
  backgroundGaugeOrbitFirst
    Physical.identityBackground parameter coordinate (pair site axis)
  ≡ flatGaugeOrbitFirst parameter coordinate (pair site axis)
identityGaugeOrbitFirstExact parameter coordinate site axis =
  cong
    (parameter (pair coordinate site) -_)
    (identityForwardTransportCoordinateExact parameter coordinate axis site)

------------------------------------------------------------------------
-- Literal finite Faddeev--Popov operator M_A = D_A G_A.
------------------------------------------------------------------------

faddeevPopovApply :
  Physical.RationalSU2Background4 → SiteGaugeParameter4 →
  Gauge.GaugeCoordinate4 → ℚ
faddeevPopovApply background parameter =
  Gauge.backgroundGaugeFirst background
    (backgroundGaugeOrbitFirst background parameter)

flatFaddeevPopovApply :
  SiteGaugeParameter4 → Gauge.GaugeCoordinate4 → ℚ
flatFaddeevPopovApply parameter =
  Gauge.flatGaugeFirstFromAxes (flatGaugeOrbitFirst parameter)

flatBackwardTermOrbitCong :
  ∀ parameter coordinate axis site →
  Gauge.flatBackwardTerm
    (backgroundGaugeOrbitFirst Physical.identityBackground parameter)
    coordinate axis site
  ≡ Gauge.flatBackwardTerm
      (flatGaugeOrbitFirst parameter) coordinate axis site
flatBackwardTermOrbitCong parameter coordinate axis site =
  let
    currentExact = identityGaugeOrbitFirstExact parameter coordinate site axis
    previousSite = Periodic.shiftBackward axis site
    previousExact =
      identityGaugeOrbitFirstExact parameter coordinate previousSite axis
  in
  subst
    (λ current →
      current
      - backgroundGaugeOrbitFirst
          Physical.identityBackground parameter coordinate
          (pair previousSite axis)
      ≡ Gauge.flatBackwardTerm
          (flatGaugeOrbitFirst parameter) coordinate axis site)
    (sym currentExact)
    (subst
      (λ previous →
        flatGaugeOrbitFirst parameter coordinate (pair site axis)
        - previous
        ≡ Gauge.flatBackwardTerm
            (flatGaugeOrbitFirst parameter) coordinate axis site)
      (sym previousExact)
      refl)

identityFaddeevPopovIsFlat :
  ∀ parameter coordinate site →
  faddeevPopovApply Physical.identityBackground parameter
      (pair coordinate site)
  ≡ flatFaddeevPopovApply parameter (pair coordinate site)
identityFaddeevPopovIsFlat parameter coordinate site =
  trans
    (Gauge.identityBackgroundGaugeFirstIsFlatAxes
      (backgroundGaugeOrbitFirst Physical.identityBackground parameter)
      coordinate site)
    (Sums.sumRationalCong
      Gauge.axes4
      (λ axis →
        Gauge.flatBackwardTerm
          (backgroundGaugeOrbitFirst Physical.identityBackground parameter)
          coordinate axis site)
      (λ axis →
        Gauge.flatBackwardTerm
          (flatGaugeOrbitFirst parameter) coordinate axis site)
      (λ axis → flatBackwardTermOrbitCong parameter coordinate axis site))

------------------------------------------------------------------------
-- Explicit flat nearest-neighbour Laplacian form.
------------------------------------------------------------------------

flatFaddeevPopovAxisTerm :
  SiteGaugeParameter4 → Coordinates.LieCoordinate3 →
  Periodic.Axis4 → Periodic.Site4 → ℚ
flatFaddeevPopovAxisTerm parameter coordinate axis site =
    (parameter (pair coordinate site)
      - parameter (pair coordinate (Periodic.shiftForward axis site)))
  - (parameter (pair coordinate (Periodic.shiftBackward axis site))
      - parameter (pair coordinate site))

flatGaugeBackwardTermIsLaplacianAxis :
  ∀ parameter coordinate axis site →
  Gauge.flatBackwardTerm (flatGaugeOrbitFirst parameter) coordinate axis site
  ≡ flatFaddeevPopovAxisTerm parameter coordinate axis site
flatGaugeBackwardTermIsLaplacianAxis parameter coordinate axis site =
  let
    backward = Periodic.shiftBackward axis site
    forwardBackwardExact = Periodic.shiftForwardBackward axis site
  in
  subst
    (λ selected →
      (parameter (pair coordinate site)
        - parameter (pair coordinate (Periodic.shiftForward axis site)))
      - (parameter (pair coordinate backward)
        - parameter (pair coordinate selected))
      ≡ flatFaddeevPopovAxisTerm parameter coordinate axis site)
    (sym forwardBackwardExact)
    refl

flatFaddeevPopovIsPeriodicLaplacian :
  ∀ parameter coordinate site →
  flatFaddeevPopovApply parameter (pair coordinate site)
  ≡ Sums.sumRational Gauge.axes4
      (λ axis → flatFaddeevPopovAxisTerm parameter coordinate axis site)
flatFaddeevPopovIsPeriodicLaplacian parameter coordinate site =
  Sums.sumRationalCong
    Gauge.axes4
    (λ axis →
      Gauge.flatBackwardTerm (flatGaugeOrbitFirst parameter)
        coordinate axis site)
    (λ axis → flatFaddeevPopovAxisTerm parameter coordinate axis site)
    (λ axis →
      flatGaugeBackwardTermIsLaplacianAxis parameter coordinate axis site)

physicalBackgroundGaugeOrbitFirstLevel : ProofLevel
physicalBackgroundGaugeOrbitFirstLevel = machineChecked

physicalFaddeevPopovOperatorLevel : ProofLevel
physicalFaddeevPopovOperatorLevel = machineChecked

flatFaddeevPopovPeriodicLaplacianLevel : ProofLevel
flatFaddeevPopovPeriodicLaplacianLevel = machineChecked

-- Still open for B1: determinant/log-det expansion of this SAME operator,
-- combination with the Wilson gauge-field Hessian and Haar/Jacobian factor,
-- and the physical colour contraction into C_A times the universal orbit sum.
literalFaddeevPopovDeterminantOneLoopContributionLevel : ProofLevel
literalFaddeevPopovDeterminantOneLoopContributionLevel = conditional
