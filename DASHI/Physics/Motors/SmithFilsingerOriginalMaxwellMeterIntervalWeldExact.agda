module DASHI.Physics.Motors.SmithFilsingerOriginalMaxwellMeterIntervalWeldExact where

-- F10/F13 conditional exact ORIGINAL Maxwell-to-meter certificate transport.
-- REUSE ONLY: SelectedSpaceTimePort (original jet/boundary/source/member),
-- the 4D rational Poynting window, and the canonical two-sided meter
-- certificate (which in turn reuses ProofCarryingFiniteSumEnclosure).
--
-- No new field equation, no simulation, no SI value and no fabricated
-- source/terminal measurement. All admissions are contentful data.
-- In particular a certificate for ANY OTHER window cannot inhabit this
-- same-object record by matching a source description string.

open import Agda.Primitive using (Level; lsuc; lzero; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Rational.Base as ℚ

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Plasma.KSW668FullVectorMaxwellJetExact as Vector
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Boundary
import DASHI.Physics.Motors.SmithFilsingerSelectedSpaceTimePortWeldExact as Original
import DASHI.Physics.Motors.SmithFilsingerSpaceTimePoyntingTelescopeExact as SpaceTime
import DASHI.Physics.Motors.SmithFilsingerCertifiedSignedMeterResidualExact as Meter
import DASHI.Physics.Motors.SmithFilsingerCertifiedSignedMeterTwoSidedExact as Bounds
import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port

-- This is a SAME-TYPED original-window receipt. The dependent meter
-- certificate must be constructed on the exact selected physical window,
-- not introduced as a separately chosen time interval.
record OriginalMaxwellMeterIntervalWeld
  {r : Level} {F : C3.RealField r}
  (jet : Vector.FullVectorMaxwellJet F)
  (b : Boundary.SelectedBoundary)
  (f : Boundary.FormalFieldToPort b)
  : Set (lsuc (r ⊔ lsuc (lsuc lzero))) where
  field
    originalPort : Original.SelectedOriginalSpaceTimePort jet b f
    meterCertificate :
      Bounds.TwoSidedMeterCertificate
        (SpaceTime.SameOriginalSpaceTimeMaxwellAdmission.window
          (Original.SelectedOriginalSpaceTimePort.physicalTrace
            originalPort))

open OriginalMaxwellMeterIntervalWeld public

-- Transport a rational inequality through an ACTUAL identification,
-- rather than postulating a second inequality on the physical terminal.
transportLeft :
  (upper : ℚ.ℚ) {a b : ℚ.ℚ} →
  a ≡ b → ℚ._≤_ a upper → ℚ._≤_ b upper
transportLeft upper refl proof = proof

transportRight :
  (lower : ℚ.ℚ) {a b : ℚ.ℚ} →
  a ≡ b → ℚ._≤_ lower a → ℚ._≤_ lower b
transportRight lower refl proof = proof

-- Certified original physical receiver UPPER:
-- the selected Maxwell/constitutive receiver is the SAME value as the
-- original meter's physical source-identified work. All numerical
-- content lives in the signed residual certificate; no guessed watts.
originalMaxwellReceiverUpperFromSignedMeter :
  ∀ {r} {F : C3.RealField r}
  (jet : Vector.FullVectorMaxwellJet F)
  (b : Boundary.SelectedBoundary)
  (f : Boundary.FormalFieldToPort b)
  (a : OriginalMaxwellMeterIntervalWeld jet b f) →
  let physical = Original.SelectedOriginalSpaceTimePort.physicalTrace
                   (originalPort a)
      bound = meterCertificate a in
  ℚ._≤_
    (SpaceTime.SameOriginalSpaceTimeMaxwellAdmission.actualUsefulReceiverWork
      physical)
    (Meter.SelectedOriginalCertifiedMeter.observedNetTerminalWork
       (Bounds.TwoSidedMeterCertificate.original bound)
     ℚ.+ Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
       (Meter.SelectedOriginalCertifiedMeter.upper
         (Bounds.TwoSidedMeterCertificate.original bound)))
originalMaxwellReceiverUpperFromSignedMeter jet b f a =
  transportLeft _
    (SpaceTime.SameOriginalSpaceTimeMaxwellAdmission.loadIdentified
      (Original.SelectedOriginalSpaceTimePort.physicalTrace
        (originalPort a)))
    (Bounds.twoSidedOriginalReceiverUpper
      (SpaceTime.SameOriginalSpaceTimeMaxwellAdmission.window
        (Original.SelectedOriginalSpaceTimePort.physicalTrace
          (originalPort a)))
      (meterCertificate a))

-- Certified original physical receiver LOWER:
-- observation minus the independently certified upper for NEGATED signed
-- residual is below the exact same original Maxwell receiver work.
originalMaxwellReceiverLowerFromSignedMeter :
  ∀ {r} {F : C3.RealField r}
  (jet : Vector.FullVectorMaxwellJet F)
  (b : Boundary.SelectedBoundary)
  (f : Boundary.FormalFieldToPort b)
  (a : OriginalMaxwellMeterIntervalWeld jet b f) →
  let physical = Original.SelectedOriginalSpaceTimePort.physicalTrace
                   (originalPort a)
      bound = meterCertificate a in
  ℚ._≤_
    (Meter.SelectedOriginalCertifiedMeter.observedNetTerminalWork
       (Bounds.TwoSidedMeterCertificate.original bound)
     ℚ.+ (ℚ.- Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
       (Bounds.TwoSidedMeterCertificate.negativeUpper bound)))
    (SpaceTime.SameOriginalSpaceTimeMaxwellAdmission.actualUsefulReceiverWork
      physical)
originalMaxwellReceiverLowerFromSignedMeter jet b f a =
  transportRight _
    (SpaceTime.SameOriginalSpaceTimeMaxwellAdmission.loadIdentified
      (Original.SelectedOriginalSpaceTimePort.physicalTrace
        (originalPort a)))
    (Bounds.twoSidedOriginalReceiverLower
      (SpaceTime.SameOriginalSpaceTimeMaxwellAdmission.window
        (Original.SelectedOriginalSpaceTimePort.physicalTrace
          (originalPort a)))
      (meterCertificate a))

-- A physical receiver bound also applies to the CALIBRATED SAME ORIGINAL
-- named b/f port: the existing selected physical-port equality supplies
-- this last identification; the abstract meter does NOT choose b/f.
originalCalibratedPortUpperFromSignedMeter :
  ∀ {r} {F : C3.RealField r}
  (jet : Vector.FullVectorMaxwellJet F)
  (b : Boundary.SelectedBoundary)
  (f : Boundary.FormalFieldToPort b)
  (a : OriginalMaxwellMeterIntervalWeld jet b f) →
  let physical = Original.SelectedOriginalSpaceTimePort.physicalTrace
                   (originalPort a)
      bound = meterCertificate a in
  ℚ._≤_
    (Original.SelectedOriginalSpaceTimePort.calibratedWork
      (originalPort a)
      (Port.MidpointTwoPortWorkWindow.usefulWork
        (Boundary.FormalFieldToPort.portWindow f)))
    (Meter.SelectedOriginalCertifiedMeter.observedNetTerminalWork
       (Bounds.TwoSidedMeterCertificate.original bound)
     ℚ.+ Cert.ProofCarryingFiniteSumUpperEnclosure.certifiedUpper
       (Meter.SelectedOriginalCertifiedMeter.upper
         (Bounds.TwoSidedMeterCertificate.original bound)))
originalCalibratedPortUpperFromSignedMeter jet b f a =
  transportLeft _
    (Original.SelectedOriginalSpaceTimePort.loadIsSameOriginal
      (originalPort a))
    (originalMaxwellReceiverUpperFromSignedMeter jet b f a)
