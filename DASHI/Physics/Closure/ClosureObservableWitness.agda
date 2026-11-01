module DASHI.Physics.Closure.ClosureObservableWitness where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)

open import MDL.Core.Core as OldMDL
open import DASHI.MDL.MDLDescentTradeoff as MDL using (MDLParts)
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.Closure.MDLTradeoffShiftInstance as MSI
open import DASHI.Physics.Closure.ShiftSeamCertificates as SSC

record ClosureObservableWitness : Setω where
  field
    realizationLabel : String
    provedSignature : CTI.Signature
    observedOrientationTag : Nat
    observedShell1 : List Nat
    observedShell2 : List Nat
    seams : ∀ {m k : Nat} → SSC.ShiftSeams {m} {k}
    lyapunovShift :
      ∀ {m k : Nat} →
      OldMDL.Lyapunov
        {S = RTC.Carrier (m + k)}
        (MDLParts.T (MSI.MDLPartsShift {m} {k}))

open ClosureObservableWitness public
