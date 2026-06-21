module DASHI.Foundations.SSPPrimeLane369ConsumerRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Core.SuperSSP369Field as Super using
  ( SuperSSP369Field
  ; focusPrimeLane
  )
open import DASHI.Physics.Closure.SSPPrimeLane369BTBridge as BT using
  ( SSPPrimeLane369BTProfile
  ; primeLane369BTProfile
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PAdicBridge as PAdic using
  ( SSPPrimeLane369PAdicBridge
  ; canonicalRootBridgeP3
  ; canonicalRootBridgeP11
  ; canonicalThreeSixNineP7Bridge
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as Phase using
  ( SSPPrimeLane369PhaseBridge
  ; p7SSPPrimeLane369PhaseBridge
  ; p11SSPPrimeLane369PhaseBridge
  )
open import DASHI.Physics.Closure.SSPPrimeLane369ResidueFactorBridge as Residue using
  ( SSPPrimeLane369ResidueFactorBridge
  ; p7SSPPrimeLane369ResidueFactorBridge
  ; p11SSPPrimeLane369ResidueFactorBridge
  )
open import DASHI.TrackedPrimes using (p3; p7; p11)

three : Nat
three = suc (suc (suc zero))

record SSPPrimeLane369ConsumerRegression : Set where
  constructor mkSSPPrimeLane369ConsumerRegression
  field
    p7ResidueFactorReceipt : Residue.SSPPrimeLane369ResidueFactorBridge
    p11ResidueFactorReceipt : Residue.SSPPrimeLane369ResidueFactorBridge
    p7PhaseReceipt : Phase.SSPPrimeLane369PhaseBridge
    p11PhaseReceipt : Phase.SSPPrimeLane369PhaseBridge
    p3RootPAdicReceipt : PAdic.SSPPrimeLane369PAdicBridge
    p7Depth3PAdicReceipt : PAdic.SSPPrimeLane369PAdicBridge
    p11RootPAdicReceipt : PAdic.SSPPrimeLane369PAdicBridge
    p3BTReceipt : BT.SSPPrimeLane369BTProfile
    p7BTReceipt : BT.SSPPrimeLane369BTProfile
    p11BTReceipt : BT.SSPPrimeLane369BTProfile
    rootFieldReceipt : Super.SuperSSP369Field zero
    depth3FieldReceipt : Super.SuperSSP369Field three
    p7ResidueFactorReceiptIsCanonical :
      p7ResidueFactorReceipt ≡ Residue.p7SSPPrimeLane369ResidueFactorBridge
    p11ResidueFactorReceiptIsCanonical :
      p11ResidueFactorReceipt ≡ Residue.p11SSPPrimeLane369ResidueFactorBridge
    p7PhaseReceiptIsCanonical :
      p7PhaseReceipt ≡ Phase.p7SSPPrimeLane369PhaseBridge
    p11PhaseReceiptIsCanonical :
      p11PhaseReceipt ≡ Phase.p11SSPPrimeLane369PhaseBridge
    p3RootPAdicReceiptIsCanonical :
      p3RootPAdicReceipt ≡ PAdic.canonicalRootBridgeP3
    p7Depth3PAdicReceiptIsCanonical :
      p7Depth3PAdicReceipt ≡ PAdic.canonicalThreeSixNineP7Bridge
    p11RootPAdicReceiptIsCanonical :
      p11RootPAdicReceipt ≡ PAdic.canonicalRootBridgeP11
    p3BTReceiptIsCanonical :
      p3BTReceipt ≡ BT.primeLane369BTProfile p3
    p7BTReceiptIsCanonical :
      p7BTReceipt ≡ BT.primeLane369BTProfile p7
    p11BTReceiptIsCanonical :
      p11BTReceipt ≡ BT.primeLane369BTProfile p11
    rootFieldPrimeIsP3 :
      Super.focusPrimeLane rootFieldReceipt ≡ p3
    depth3FieldPrimeIsP7 :
      Super.focusPrimeLane depth3FieldReceipt ≡ p7

open SSPPrimeLane369ConsumerRegression public

canonicalSSPPrimeLane369ConsumerRegression :
  SSPPrimeLane369ConsumerRegression
canonicalSSPPrimeLane369ConsumerRegression =
  mkSSPPrimeLane369ConsumerRegression
    Residue.p7SSPPrimeLane369ResidueFactorBridge
    Residue.p11SSPPrimeLane369ResidueFactorBridge
    Phase.p7SSPPrimeLane369PhaseBridge
    Phase.p11SSPPrimeLane369PhaseBridge
    PAdic.canonicalRootBridgeP3
    PAdic.canonicalThreeSixNineP7Bridge
    PAdic.canonicalRootBridgeP11
    (BT.primeLane369BTProfile p3)
    (BT.primeLane369BTProfile p7)
    (BT.primeLane369BTProfile p11)
    Super.rootField
    Super.depth3Field
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
