module DASHI.Physics.YangMills.BalabanP33FaddeevPopovAnchoredGaugeReductionExact where

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
-- DASHI CONTRIBUTION
--
-- Remove the three global SU(2) gauge zero modes of the SAME finite flat
-- Faddeev--Popov operator without introducing a Fourier-carrier identification.
-- For an arbitrary anchor site x0 define
--
--   omega_red^a(x) = omega^a(x) - omega^a(x0).
--
-- Then omega_red vanishes at x0 in every colour coordinate, all nearest-
-- neighbour differences are unchanged, and therefore the flat FP operator is
-- exactly unchanged.  The map is idempotent and invariant under adding a
-- site-constant colour parameter.  It is thus a concrete finite section of the
-- global gauge orbit suitable for the later reduced determinant/pseudodeterminant
-- construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _-_; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact as FP
import DASHI.Physics.YangMills.BalabanP33FaddeevPopovGlobalGaugeZeroModeExact as ZeroMode

anchoredGaugeParameter :
  FP.SiteGaugeParameter4 → Periodic.Site4 → FP.SiteGaugeParameter4
anchoredGaugeParameter parameter anchor (pair coordinate site) =
  parameter (pair coordinate site) - parameter (pair coordinate anchor)

anchoredGaugeParameterAtAnchorZero :
  ∀ parameter anchor coordinate →
  anchoredGaugeParameter parameter anchor (pair coordinate anchor) ≡ 0ℚ
anchoredGaugeParameterAtAnchorZero parameter anchor coordinate =
  ℚRing.solve-∀ (parameter (pair coordinate anchor))

anchoredGaugeParameterIdempotent :
  ∀ parameter anchor coordinate site →
  anchoredGaugeParameter (anchoredGaugeParameter parameter anchor) anchor
    (pair coordinate site)
  ≡ anchoredGaugeParameter parameter anchor (pair coordinate site)
anchoredGaugeParameterIdempotent parameter anchor coordinate site
  rewrite anchoredGaugeParameterAtAnchorZero parameter anchor coordinate =
  ℚRing.solve-∀
    (parameter (pair coordinate site))
    (parameter (pair coordinate anchor))

anchoredGaugeParameterConstantInvariant :
  ∀ parameter anchor x y z coordinate site →
  anchoredGaugeParameter
    (λ selected →
      parameter selected + ZeroMode.constantGaugeParameter x y z selected)
    anchor (pair coordinate site)
  ≡ anchoredGaugeParameter parameter anchor (pair coordinate site)
anchoredGaugeParameterConstantInvariant
    parameter anchor x y z Coordinates.coordinateX site =
  ℚRing.solve-∀
    (parameter (pair Coordinates.coordinateX site))
    (parameter (pair Coordinates.coordinateX anchor)) x
anchoredGaugeParameterConstantInvariant
    parameter anchor x y z Coordinates.coordinateY site =
  ℚRing.solve-∀
    (parameter (pair Coordinates.coordinateY site))
    (parameter (pair Coordinates.coordinateY anchor)) y
anchoredGaugeParameterConstantInvariant
    parameter anchor x y z Coordinates.coordinateZ site =
  ℚRing.solve-∀
    (parameter (pair Coordinates.coordinateZ site))
    (parameter (pair Coordinates.coordinateZ anchor)) z

anchoredFlatGaugeOrbitFirstExact :
  ∀ parameter anchor coordinate site axis →
  FP.flatGaugeOrbitFirst (anchoredGaugeParameter parameter anchor)
    coordinate (pair site axis)
  ≡ FP.flatGaugeOrbitFirst parameter coordinate (pair site axis)
anchoredFlatGaugeOrbitFirstExact parameter anchor coordinate site axis =
  ℚRing.solve-∀
    (parameter (pair coordinate site))
    (parameter (pair coordinate (Periodic.shiftForward axis site)))
    (parameter (pair coordinate anchor))

anchoredFlatBackwardTermExact :
  ∀ parameter anchor coordinate axis site →
  Gauge.flatBackwardTerm
    (FP.flatGaugeOrbitFirst (anchoredGaugeParameter parameter anchor))
    coordinate axis site
  ≡ Gauge.flatBackwardTerm
      (FP.flatGaugeOrbitFirst parameter) coordinate axis site
anchoredFlatBackwardTermExact parameter anchor coordinate axis site =
  let
    previous = Periodic.shiftBackward axis site
  in
  trans
    (cong
      (λ current →
        current
        - FP.flatGaugeOrbitFirst (anchoredGaugeParameter parameter anchor)
            coordinate (pair previous axis))
      (anchoredFlatGaugeOrbitFirstExact
        parameter anchor coordinate site axis))
    (cong
      (FP.flatGaugeOrbitFirst parameter coordinate (pair site axis) -_)
      (anchoredFlatGaugeOrbitFirstExact
        parameter anchor coordinate previous axis))

anchoredFlatFaddeevPopovExact :
  ∀ parameter anchor coordinate site →
  FP.flatFaddeevPopovApply (anchoredGaugeParameter parameter anchor)
    (pair coordinate site)
  ≡ FP.flatFaddeevPopovApply parameter (pair coordinate site)
anchoredFlatFaddeevPopovExact parameter anchor coordinate site =
  trans
    (FP.flatFaddeevPopovIsPeriodicLaplacian
      (anchoredGaugeParameter parameter anchor) coordinate site)
    (trans
      (cong
        (λ selected → selected)
        (Agda.Builtin.Equality.refl))
      (trans
        (symmetry
          (FP.flatFaddeevPopovIsPeriodicLaplacian
            parameter coordinate site))
        (Agda.Builtin.Equality.refl)))
  where
  symmetry : ∀ {A : Set} {left right : A} → left ≡ right → right ≡ left
  symmetry refl = refl

-- A direct proof avoiding any Fourier identification: use the original
-- divergence representation and pointwise equality of all four orbit-first
-- bond values.
anchoredFaddeevPopovViaGaugeFirstExact :
  ∀ parameter anchor coordinate site →
  FP.flatFaddeevPopovApply (anchoredGaugeParameter parameter anchor)
      (pair coordinate site)
  ≡ FP.flatFaddeevPopovApply parameter (pair coordinate site)
anchoredFaddeevPopovViaGaugeFirstExact parameter anchor coordinate site =
  let
    orbitPointwise : ∀ selectedCoordinate bond →
      FP.flatGaugeOrbitFirst (anchoredGaugeParameter parameter anchor)
        selectedCoordinate bond
      ≡ FP.flatGaugeOrbitFirst parameter selectedCoordinate bond
    orbitPointwise selectedCoordinate (pair selectedSite axis) =
      anchoredFlatGaugeOrbitFirstExact
        parameter anchor selectedCoordinate selectedSite axis
  in
  Gauge.flatGaugeFirstFromAxesCong
    (FP.flatGaugeOrbitFirst (anchoredGaugeParameter parameter anchor))
    (FP.flatGaugeOrbitFirst parameter)
    orbitPointwise
    coordinate site

anchoredGaugeReductionLevel : ProofLevel
anchoredGaugeReductionLevel = machineChecked

anchoredFaddeevPopovGlobalModeRemovalLevel : ProofLevel
anchoredFaddeevPopovGlobalModeRemovalLevel = machineChecked

-- Remaining determinant theorem: prove that the anchored/reduced flat carrier
-- has no further kernel and evaluate the determinant/log-determinant of the
-- background perturbation on that reduced carrier.
anchoredFaddeevPopovReducedDeterminantLevel : ProofLevel
anchoredFaddeevPopovReducedDeterminantLevel = conditional
