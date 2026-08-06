module DASHI.Physics.YangMills.BalabanP33PhysicalWilsonPlacementNormSquaredExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- John H. Conway and Derek A. Smith,
-- "On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry",
-- A K Peters, 2003. DOI: 10.1201/9781439864180.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Apply the exact quaternion telescope norm theorem to every named physical
-- Wilson placement.  For the actual background and identity plaquette jets,
-- the square of each scalar placement defect is bounded by the explicit sum of
-- four selected-factor defects supplied by the physical selection table.
--
-- This removes the last anonymous norm step between the physical atom and the
-- factor-level small-field estimates.  The remaining W-local task must bound
-- those selected-factor defects by the literal link charge allocations and
-- recover a signed, unsquared lower estimate with constants rho/36 and
-- rho/144.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_; _/_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonPlacementTelescopeExact as PlacementTelescope
import DASHI.Physics.YangMills.BalabanP33QuaternionTelescopeNormSquaredExact as NormTelescope

physicalSelectedFactorDefectWeight :
  Physical.RationalSU2Background4 →
  Coordinates.PhysicalSU2BondField4 →
  Physical.Plaquette4 →
  Placement.PlaquetteSecondVariationPlacement4 → ℚ
physicalSelectedFactorDefectWeight background field plaquette placement =
  let
    backgroundData = Physical.plaquetteJetData background field plaquette
    identityData =
      Physical.plaquetteJetData Physical.identityBackground field plaquette

    a0 = PlacementTelescope.selectedFactor0
      (Jets.link0 backgroundData) placement
    a1 = PlacementTelescope.selectedFactor1
      (Jets.link1 backgroundData) placement
    a2 = PlacementTelescope.selectedFactor2
      (Jets.link2 backgroundData) placement
    a3 = PlacementTelescope.selectedFactor3
      (Jets.link3 backgroundData) placement

    b0 = PlacementTelescope.selectedFactor0
      (Jets.link0 identityData) placement
    b1 = PlacementTelescope.selectedFactor1
      (Jets.link1 identityData) placement
    b2 = PlacementTelescope.selectedFactor2
      (Jets.link2 identityData) placement
    b3 = PlacementTelescope.selectedFactor3
      (Jets.link3 identityData) placement
  in
  NormTelescope.weightedFactorDefectSum
    a0 a1 a2 a3 b0 b1 b2 b3

physicalPlacementWilsonScalarDefectSquareBound :
  ∀ background field plaquette placement →
  let defect =
        PlacementTelescope.physicalPlacementWilsonScalarDefect
          background field plaquette placement
  in
  defect * defect
  ≤ (+ 4 / 1)
      * physicalSelectedFactorDefectWeight
          background field plaquette placement
physicalPlacementWilsonScalarDefectSquareBound
    background field plaquette placement
  rewrite PlacementTelescope.namedPlacementAtomIsSelectedProduct
      (Jets.link0 (Physical.plaquetteJetData background field plaquette))
      (Jets.link1 (Physical.plaquetteJetData background field plaquette))
      (Jets.link2 (Physical.plaquetteJetData background field plaquette))
      (Jets.link3 (Physical.plaquetteJetData background field plaquette))
      placement
        | PlacementTelescope.namedPlacementAtomIsSelectedProduct
      (Jets.link0
        (Physical.plaquetteJetData
          Physical.identityBackground field plaquette))
      (Jets.link1
        (Physical.plaquetteJetData
          Physical.identityBackground field plaquette))
      (Jets.link2
        (Physical.plaquetteJetData
          Physical.identityBackground field plaquette))
      (Jets.link3
        (Physical.plaquetteJetData
          Physical.identityBackground field plaquette))
      placement =
  NormTelescope.wilsonScalarDefectSquareBound _ _ _ _ _ _ _ _

physicalWilsonPlacementNormSquaredLevel : ProofLevel
physicalWilsonPlacementNormSquaredLevel = machineChecked

physicalWilsonSelectedFactorChargeLevel : ProofLevel
physicalWilsonSelectedFactorChargeLevel = conditional

physicalWilsonSignedLocalDefectLevel : ProofLevel
physicalWilsonSignedLocalDefectLevel = conditional
