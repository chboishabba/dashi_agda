module DASHI.Physics.Motors.SmithFilsingerSpaceTimePoyntingTelescopeExact where

-- F10-STOKES: exact FOUR-DIRECTION finite space-time boundary energy law.
-- Reuses Yang-Mills/Ward finite difference telescope for time and the
-- existing 3D open-boundary Poynting Gauss owner for all space axes.
-- No new Maxwell solver, source-energy hypothesis or phantom material work.
--
-- This theorem is exact over a RATIONAL signed finite-difference carrier.
-- Mapping a true Maxwell field / material ADE to these time/face samples
-- is a separate CONTENTFUL physical/analytic obligation.

open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
open import Agda.Primitive using (Level; lsuc)
import Data.Rational.Base as ℚ
import DASHI.Physics.YangMills.YangMillsLatticeStressWardSliceConservationExact as Ward
import DASHI.Physics.Motors.SmithFilsingerOpenBoundaryPoyntingGaussExact as Open
import DASHI.Physics.Plasma.KSW668FullVectorMaxwellJetExact as Vector
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3

-- The local energy identity is an obligation on actual finite-difference
-- variables: it is NOT manufactured by choosing an arbitrary source.
-- All currents, controller work, ionization, material relaxation, radiation
-- and useful receiver work must appear once and with their correct signs.
record FiniteSpaceTimeWindow : Set₁ where
  field
    faces : Open.OpenRectangularPoyntingFaces
    storedEnergy : Nat → ℚ.ℚ
    steps : Nat
    naturalSigned controllerSigned : ℚ.ℚ
    materialAndIonLoss usefulReceiverWork : ℚ.ℚ

    -- Discrete local Poynting / work law on the SAME sampled interval.
    -- Must be justified by the update equations / physical integration.
    finiteDifferenceEnergyLaw :
      ((Ward.differencePartial storedEnergy steps
          ℚ.+ Open.threeAxisFiniteDivergence faces)
        ℚ.+ (materialAndIonLoss ℚ.+ usefulReceiverWork))
        ≡ naturalSigned ℚ.+ controllerSigned

open FiniteSpaceTimeWindow public

-- Exact 4-direction open-domain Stokes/Poynting algebra.
-- NO periodic boundary assumption, stored-energy depletion is explicit.
spaceTimeExteriorEnergyBalance :
  (w : FiniteSpaceTimeWindow) →
  (((storedEnergy w (steps w) ℚ.- storedEnergy w zero)
      ℚ.+ Open.exteriorOrientedPoyntingFlux (faces w))
      ℚ.+ (materialAndIonLoss w ℚ.+ usefulReceiverWork w))
  ≡ naturalSigned w ℚ.+ controllerSigned w
spaceTimeExteriorEnergyBalance w
  rewrite sym (Ward.differencePartialTelescopes
    (storedEnergy w) (steps w))
    | sym (Open.finiteOpenBoundaryPoyntingGauss (faces w)) =
    finiteDifferenceEnergyLaw w

-- The original KSW668 vector jet is a POINTWISE theorem. This
-- record requires an actual field-to-time-grid and field-to-face
-- quadrature map; a single pointwise jet is not a spatial solution.
record SameOriginalSpaceTimeMaxwellAdmission
  {r : Level} {F : C3.RealField r}
  (jet : Vector.FullVectorMaxwellJet F) : Set (lsuc r) where
  field
    window : FiniteSpaceTimeWindow
    originalTrace : Open.OriginalMaxwellOpenFaceTrace jet
    selectedFacesSame :
      Open.OriginalMaxwellOpenFaceTrace.faces originalTrace
        ≡ faces window

    -- Source-to-terminal equality is an actual ORIGINAL physical
    -- measurement/calibration obligation, not a theoretical value.
    actualSignedNaturalSource : ℚ.ℚ
    actualSignedController : ℚ.ℚ
    actualMaterialAndIonLoss : ℚ.ℚ
    actualUsefulReceiverWork : ℚ.ℚ
    sourceIdentified :
      naturalSigned window ≡ actualSignedNaturalSource
    controllerIdentified :
      controllerSigned window ≡ actualSignedController
    materialIdentified :
      materialAndIonLoss window ≡ actualMaterialAndIonLoss
    loadIdentified :
      usefulReceiverWork window ≡ actualUsefulReceiverWork

-- Consume the pointwise KSW668 Maxwell identity via the preexisting
-- original open-boundary trace, then transport the face identity.
sameOriginalSpatialExteriorFlux :
  ∀ {r} {F : C3.RealField r}
  (jet : Vector.FullVectorMaxwellJet F)
  (a : SameOriginalSpaceTimeMaxwellAdmission jet) →
  Open.OriginalMaxwellOpenFaceTrace.integratedSpatialPoyntingDivergence
    (SameOriginalSpaceTimeMaxwellAdmission.originalTrace a)
  ≡ Open.exteriorOrientedPoyntingFlux
    (faces (SameOriginalSpaceTimeMaxwellAdmission.window a))
sameOriginalSpatialExteriorFlux jet a =
  trans
    (Open.originalFullVectorJetOpenBoundaryFlux jet
      (SameOriginalSpaceTimeMaxwellAdmission.originalTrace a))
    (cong Open.exteriorOrientedPoyntingFlux
      (SameOriginalSpaceTimeMaxwellAdmission.selectedFacesSame a))

-- The finite-space-time budget plus source, load and controller
-- identifications is a proved same-window equality, not a separately
-- asserted whole-system equation.
sameOriginalTimeIntegratedPowerBalance :
  ∀ {r} {F : C3.RealField r}
  (jet : Vector.FullVectorMaxwellJet F)
  (a : SameOriginalSpaceTimeMaxwellAdmission jet) →
  (((storedEnergy (SameOriginalSpaceTimeMaxwellAdmission.window a)
      (steps (SameOriginalSpaceTimeMaxwellAdmission.window a))
      ℚ.- storedEnergy (SameOriginalSpaceTimeMaxwellAdmission.window a) zero)
      ℚ.+ Open.exteriorOrientedPoyntingFlux
        (faces (SameOriginalSpaceTimeMaxwellAdmission.window a)))
      ℚ.+ (SameOriginalSpaceTimeMaxwellAdmission.actualMaterialAndIonLoss a
        ℚ.+ SameOriginalSpaceTimeMaxwellAdmission.actualUsefulReceiverWork a))
  ≡ SameOriginalSpaceTimeMaxwellAdmission.actualSignedNaturalSource a
      ℚ.+ SameOriginalSpaceTimeMaxwellAdmission.actualSignedController a
sameOriginalTimeIntegratedPowerBalance jet a
  rewrite
       sym (SameOriginalSpaceTimeMaxwellAdmission.materialIdentified a)
    | sym (SameOriginalSpaceTimeMaxwellAdmission.loadIdentified a)
    | sym (SameOriginalSpaceTimeMaxwellAdmission.sourceIdentified a)
    | sym (SameOriginalSpaceTimeMaxwellAdmission.controllerIdentified a) =
  spaceTimeExteriorEnergyBalance (SameOriginalSpaceTimeMaxwellAdmission.window a)

-- Remaining OPEN in physical/analytic sense:
-- 1. Global C¹ / weak Maxwell distribution and actual signed quadrature
--    proving finiteDifferenceEnergyLaw from real E,H,J and materials.
-- 2. Field/face consistency, geometry, units, Hall/Pedersen, ADE/ion.
-- 3. Real original-source V/I including displacement current and return.
-- 4. Replenished solar/magnetospheric natural-work measurement, state
--    restoration and whole-controller / bridge costs.
-- 5. CFL alone never proves the continuum light cone.
