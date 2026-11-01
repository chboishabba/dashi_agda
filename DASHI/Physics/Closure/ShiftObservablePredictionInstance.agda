module DASHI.Physics.Closure.ShiftObservablePredictionInstance where

open import Relation.Binary.PropositionalEquality using (_≢_; sym; trans)

open import Data.Empty using (⊥-elim)
open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.ConeArrowIsotropyShiftOrbitEnumeration as SOE
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD
open import DASHI.Physics.Signature31Canonical as S31C
open import DASHI.Physics.Signature31FromShiftOrbitProfile as S31OP
open import DASHI.Physics.Closure.ObservablePredictionPackage as OPP
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC
open import DASHI.Physics.Closure.MDLLyapunovShiftInstance as MDLL

sig40≢sig31 : OSD.sig40 ≢ OSD.sig31
sig40≢sig31 ()

sig22≢sig31 : OSD.sig22 ≢ OSD.sig31
sig22≢sig31 ()

sig04≢sig31 : OSD.sig04 ≢ OSD.sig31
sig04≢sig31 ()

falsifySig40-proof : OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig40
falsifySig40-proof eq =
  sig40≢sig31 (OSD.SignatureFromMeasuredProfileUnique OSD.sig40 eq)

falsifySig22-proof : OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig22
falsifySig22-proof eq =
  sig22≢sig31 (OSD.SignatureFromMeasuredProfileUnique OSD.sig22 eq)

falsifySig04-proof : OSD.MeasuredProfile ≢ OSD.ProfileOf OSD.sig04
falsifySig04-proof eq =
  sig04≢sig31 (OSD.SignatureFromMeasuredProfileUnique OSD.sig04 eq)

shiftObservablePrediction : OPP.ObservablePredictionPackage
shiftObservablePrediction =
  record
    { provedSignature = S31C.signature31
    ; provedOrientation = SOE.orientationTagDerived
    ; provedShell1 = SOE.shiftEnumeration-shell1≡computed
    ; provedShell2 = SOE.shiftEnumeration-shell2≡computed
    ; provedProfile = S31OP.profileEq
    ; falsifySig40 = falsifySig40-proof
    ; falsifySig22 = falsifySig22-proof
    ; falsifyMirror = λ eq →
        OSD.Profile-sig31≢sig13 (trans (sym S31OP.profileEq) eq)
    ; falsifySig04 = falsifySig04-proof
    ; seams = λ {m} {k} → SSC.shiftSeams {m} {k}
    ; lyapunovShift = λ {m} {k} → MDLL.lyapunovShift {m} {k}
    }
