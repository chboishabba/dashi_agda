module DASHI.Physics.Motors.SmithFilsingerSelectedSpaceTimePortWeldExact where

-- F10-STOKES/F13 selected original boundary. The old generic rational
-- Maxwell space-time theorem is consumed rather than replaced.
-- Named original configuration and typed port work remain the SAME b,f.
-- Signed incident-minus-outgoing source work is explicit and cannot
-- be inferred from coherent phase or the existence of a finite field.

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Rational.Base as ℚ
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Plasma.KSW668FullVectorMaxwellJetExact as Vector
import DASHI.Physics.Motors.SmithFilsingerSpaceTimePoyntingTelescopeExact as TimeSpace
import DASHI.Physics.Motors.SmithFilsingerOpenBoundaryPoyntingGaussExact as Open
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Weld
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port

-- This is an actual measurement/geometry correspondence contract, not
-- construction of an original Sun/Earth source. A chosen conversion map
-- from exact energy quanta to the SI-like rational work carrier must
-- be additive and tied to the SAME selected original port receipts.
record SelectedOriginalSpaceTimePort
  {r : Level} {F : C3.RealField r}
  (jet : Vector.FullVectorMaxwellJet F)
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  : Set (lsuc (r ⊔ lsuc (lsuc lzero))) where
  field
    physicalTrace : TimeSpace.SameOriginalSpaceTimeMaxwellAdmission jet
    calibratedWork : Nat → ℚ.ℚ
    calibratedZero : calibratedWork zero ≡ ℚ.0ℚ
    calibratedAdd : ∀ x y →
      calibratedWork (x + y)
        ≡ calibratedWork x ℚ.+ calibratedWork y

    -- Environmental net = separately signed natural INCIDENT minus
    -- OUTGOING on the selected, source-qualified original two-port.
    sourceSignedIsSameOriginal :
      TimeSpace.SameOriginalSpaceTimeMaxwellAdmission.actualSignedNaturalSource
        physicalTrace
        ℚ.+ calibratedWork
          (Port.MidpointTwoPortWorkWindow.naturalOutgoing
            (Weld.FormalFieldToPort.portWindow f))
      ≡ calibratedWork
          (Port.MidpointTwoPortWorkWindow.naturalIncident
            (Weld.FormalFieldToPort.portWindow f))

    controllerSignedIsSameOriginal :
      TimeSpace.SameOriginalSpaceTimeMaxwellAdmission.actualSignedController
        physicalTrace
        ℚ.+ calibratedWork
          (Port.MidpointTwoPortWorkWindow.controllerOutgoing
            (Weld.FormalFieldToPort.portWindow f))
      ≡ calibratedWork
          (Port.MidpointTwoPortWorkWindow.controllerIncident
            (Weld.FormalFieldToPort.portWindow f))

    loadIsSameOriginal :
      TimeSpace.SameOriginalSpaceTimeMaxwellAdmission.actualUsefulReceiverWork
        physicalTrace
      ≡ calibratedWork
        (Port.MidpointTwoPortWorkWindow.usefulWork
          (Weld.FormalFieldToPort.portWindow f))

    initialStoredIsOriginal :
      TimeSpace.storedEnergy
        (TimeSpace.SameOriginalSpaceTimeMaxwellAdmission.window physicalTrace)
        zero
      ≡ calibratedWork
        (Port.MidpointTwoPortWorkWindow.initialStored
          (Weld.FormalFieldToPort.portWindow f))

    finalStoredIsOriginal :
      TimeSpace.storedEnergy
        (TimeSpace.SameOriginalSpaceTimeMaxwellAdmission.window physicalTrace)
        (TimeSpace.steps
          (TimeSpace.SameOriginalSpaceTimeMaxwellAdmission.window physicalTrace))
      ≡ calibratedWork
        (Port.MidpointTwoPortWorkWindow.finalStored
          (Weld.FormalFieldToPort.portWindow f))

-- This is derived from the existing KSW668 pointwise Maxwell owner,
-- finite three-axis Gauss, finite-time Ward telescope, source calibration
-- and actual named original boundary; no independent whole-system
-- conservation premise is added to this consumer.
selectedOriginalSpaceTimeEnergyCloses :
  ∀ {r} {F : C3.RealField r}
  (jet : Vector.FullVectorMaxwellJet F)
  (b : Weld.SelectedBoundary)
  (f : Weld.FormalFieldToPort b)
  (a : SelectedOriginalSpaceTimePort jet b f) →
  let w = TimeSpace.SameOriginalSpaceTimeMaxwellAdmission.window
            (SelectedOriginalSpaceTimePort.physicalTrace a) in
  (((TimeSpace.storedEnergy w (TimeSpace.steps w)
       ℚ.- TimeSpace.storedEnergy w zero)
      ℚ.+ Open.exteriorOrientedPoyntingFlux
        (TimeSpace.faces w))
      ℚ.+ (TimeSpace.SameOriginalSpaceTimeMaxwellAdmission.actualMaterialAndIonLoss
              (SelectedOriginalSpaceTimePort.physicalTrace a)
        ℚ.+ TimeSpace.SameOriginalSpaceTimeMaxwellAdmission.actualUsefulReceiverWork
              (SelectedOriginalSpaceTimePort.physicalTrace a)))
  ≡ TimeSpace.SameOriginalSpaceTimeMaxwellAdmission.actualSignedNaturalSource
       (SelectedOriginalSpaceTimePort.physicalTrace a)
    ℚ.+ TimeSpace.SameOriginalSpaceTimeMaxwellAdmission.actualSignedController
       (SelectedOriginalSpaceTimePort.physicalTrace a)
selectedOriginalSpaceTimeEnergyCloses jet b f a =
  TimeSpace.sameOriginalTimeIntegratedPowerBalance jet
    (SelectedOriginalSpaceTimePort.physicalTrace a)

-- The admitted work calibration and same-original b,f identities
-- are STILL not experimentally populated. Full 3D Maxwell/ADE
-- integration, ionospheric source, replenishment and F15 100x remain open.
