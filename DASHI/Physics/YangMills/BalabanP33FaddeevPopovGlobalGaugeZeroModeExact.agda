module DASHI.Physics.YangMills.BalabanP33FaddeevPopovGlobalGaugeZeroModeExact where

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
-- DASHI CONTRIBUTION / B1 GUARD
--
-- The literal flat Faddeev--Popov operator constructed in the companion module
-- is the periodic lattice Laplacian.  Consequently every site-constant Lie
-- algebra gauge parameter is an exact zero mode.  This file proves that fact on
-- the SAME side-four SU(2) carrier and supplies the concrete constant-X mode.
--
-- Therefore the ordinary determinant of the FULL flat ghost operator is
-- singular.  A one-loop ghost determinant/log-determinant must first remove
-- the global gauge orbit (equivalently work on the nonzero-momentum / reduced
-- ghost carrier or use the corresponding pseudodeterminant).  This is a
-- mathematical obstruction, not bookkeeping.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _-_; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact as FP

constantGaugeParameter :
  ℚ → ℚ → ℚ → FP.SiteGaugeParameter4
constantGaugeParameter x y z (pair Coordinates.coordinateX site) = x
constantGaugeParameter x y z (pair Coordinates.coordinateY site) = y
constantGaugeParameter x y z (pair Coordinates.coordinateZ site) = z

constantParameterShiftInvariant :
  ∀ x y z coordinate site axis →
  constantGaugeParameter x y z (pair coordinate (Periodic.shiftForward axis site))
  ≡ constantGaugeParameter x y z (pair coordinate site)
constantParameterShiftInvariant x y z Coordinates.coordinateX site axis = refl
constantParameterShiftInvariant x y z Coordinates.coordinateY site axis = refl
constantParameterShiftInvariant x y z Coordinates.coordinateZ site axis = refl

constantFlatGaugeOrbitFirstZero :
  ∀ x y z coordinate site axis →
  FP.flatGaugeOrbitFirst (constantGaugeParameter x y z)
    coordinate (pair site axis)
  ≡ 0ℚ
constantFlatGaugeOrbitFirstZero x y z coordinate site axis
  rewrite constantParameterShiftInvariant x y z coordinate site axis =
  ℚRing.solve []

constantFlatBackwardTermZero :
  ∀ x y z coordinate axis site →
  Gauge.flatBackwardTerm
    (FP.flatGaugeOrbitFirst (constantGaugeParameter x y z))
    coordinate axis site
  ≡ 0ℚ
constantFlatBackwardTermZero x y z coordinate axis site =
  let previous = Periodic.shiftBackward axis site
  in trans
    (cong
      (λ current →
        current
        - FP.flatGaugeOrbitFirst (constantGaugeParameter x y z)
            coordinate (pair previous axis))
      (constantFlatGaugeOrbitFirst x y z coordinate site axis))
    (trans
      (cong (0ℚ -_)
        (constantFlatGaugeOrbitFirst x y z coordinate previous axis))
      (ℚRing.solve []))

constantFlatFaddeevPopovZero :
  ∀ x y z coordinate site →
  FP.flatFaddeevPopovApply (constantGaugeParameter x y z)
    (pair coordinate site)
  ≡ 0ℚ
constantFlatFaddeevPopovZero x y z coordinate site =
  trans
    (FP.flatFaddeevPopovIsPeriodicLaplacian
      (constantGaugeParameter x y z) coordinate site)
    (trans
      (Sums.sumRationalCong
        Gauge.axes4
        (λ axis →
          FP.flatFaddeevPopovAxisTerm
            (constantGaugeParameter x y z) coordinate axis site)
        (λ _ → 0ℚ)
        (λ axis →
          trans
            (sym
              (FP.flatGaugeBackwardTermIsLaplacianAxis
                (constantGaugeParameter x y z) coordinate axis site))
            (constantFlatBackwardTermZero x y z coordinate axis site)))
      (Sums.sumRationalZero Gauge.axes4))

constantXGaugeParameter : FP.SiteGaugeParameter4
constantXGaugeParameter = constantGaugeParameter (+ 1) 0ℚ 0ℚ

constantXValueExact :
  ∀ site →
  constantXGaugeParameter (pair Coordinates.coordinateX site) ≡ + 1
constantXValueExact site = refl

constantXFlatFaddeevPopovZero :
  ∀ coordinate site →
  FP.flatFaddeevPopovApply constantXGaugeParameter (pair coordinate site) ≡ 0ℚ
constantXFlatFaddeevPopovZero = constantFlatFaddeevPopovZero (+ 1) 0ℚ 0ℚ

flatFaddeevPopovHasGlobalGaugeZeroModeLevel : ProofLevel
flatFaddeevPopovHasGlobalGaugeZeroModeLevel = machineChecked

-- B1 must use a reduced/nonzero-momentum ghost determinant or pseudodeterminant.
fullFlatGhostOrdinaryDeterminantRouteLevel : ProofLevel
fullFlatGhostOrdinaryDeterminantRouteLevel = conditional
