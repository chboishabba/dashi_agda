module DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasQuadraticEndgameExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Package the completed finite-volume Priority-3 implication in the exact
-- language produced by the literal Hessian lane.  Given:
--
--   (1/32)||v||^2 <= <v,Hv>,
--
-- the physical support-graph/row-mass data owned by the same Hessian, and a
-- literal right inverse H G = I, the preceding machine-checked modules derive
--
--   |G(root,target)| <= 64 t^d(root,target).
--
-- No independent squared-coercivity premise and no independent tilted-entry
-- premise remains in this interface.  The open cut is now exactly upstream:
-- produce the literal five-channel 1/32 Hessian theorem and its stencil budget.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (∣_∣; _≤_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact as CT
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasPromotionExact as Promotion
import DASHI.Physics.YangMills.BalabanP33CombesThomasCoercivitySurvivalExact as Survival
import DASHI.Physics.YangMills.BalabanP33PhysicalQuadraticToSquaredCoercivityExact as Quadratic
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasEntryDecayExact as Entry

PhysicalMatrix : Set
PhysicalMatrix = Physical.PhysicalSU2Matrix4

record PhysicalQuadraticCombesThomasData
    (hessian green : PhysicalMatrix) : Set₁ where
  field
    coercivity : Quadratic.PhysicalOriginalQuadraticCoercivity hessian

    hessianGreenRightInverse :
      CT.RightInverse
        Physical.physicalSU2Coordinates4
        Calibration.identityEntry hessian green

open PhysicalQuadraticCombesThomasData public

squaredResolventFromQuadratic :
  ∀ {hessian green} →
  PhysicalQuadraticCombesThomasData hessian green →
  Entry.PhysicalCombesThomasSquaredResolvent hessian green
squaredResolventFromQuadratic data = record
  { coercivity =
      Quadratic.physicalOriginalSquaredCoercivityFromQuadratic
        (coercivity data)
  ; hessianGreenRightInverse = hessianGreenRightInverse data
  }

quadraticGeometry :
  ∀ {hessian green} →
  PhysicalQuadraticCombesThomasData hessian green →
  Promotion.PhysicalCombesThomasGeometry hessian
quadraticGeometry data =
  Entry.squaredGeometry (squaredResolventFromQuadratic data)

physicalGreenKernelDecayFromQuadraticCoercivity :
  ∀ {hessian green}
    (data : PhysicalQuadraticCombesThomasData hessian green)
    target →
  ∣ green (Promotion.root (quadraticGeometry data)) target ∣
  ≤ Survival.p33InverseScale
      * Promotion.physicalWeight (quadraticGeometry data) target
physicalGreenKernelDecayFromQuadraticCoercivity data target =
  Entry.physicalGreenKernelDecayFromSquaredData
    (squaredResolventFromQuadratic data) target

physicalQuadraticCombesThomasEndgameLevel : ProofLevel
physicalQuadraticCombesThomasEndgameLevel = machineChecked

physicalPriorityThreeFiniteVolumeLevel : ProofLevel
physicalPriorityThreeFiniteVolumeLevel = machineChecked
