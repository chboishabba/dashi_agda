module DASHI.Physics.Closure.ObservablePredictionPackage where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import MDL.Core.Core as OldMDL
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD
open import DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration as SOE
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC

-- Observable boundary for the current 4D shift framework.
-- Important distinction:
-- - proved outputs are already part of the current theorem/evidence stack,
-- - excluded alternatives are eliminations already supported by that stack,
-- - forward predictions remain documented separately until they have a real
--   formal interface; see Docs/MinimalCrediblePhysicsClosure.md.
record ObservablePredictionPackage : Setω where
  field
    provedSignature : CTI.Signature
    provedOrientation : 31 ≡ OSD.OrientationTag OSD.sig31
    provedShell1 : SOE.shell1Derived ≡ OPD.shell1_p3_q1
    provedShell2 : SOE.shell2Derived ≡ OPD.shell2_p3_q1
    provedProfile : OSD.MeasuredProfile ≡ OSD.ProfileOf OSD.sig31
    falsifySig40 : OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig40
    falsifySig22 : OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig22
    falsifyMirror : OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig13
    falsifySig04 : OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig04
    seams : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    lyapunovShift :
      ∀ {m k : Nat} →
      OldMDL.Lyapunov
        {S = RTC.Carrier (m + k)}
        (MDLParts.T (MSI.MDLPartsShift {m} {k}))

open ObservablePredictionPackage public
