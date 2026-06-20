module DASHI.Physics.Closure.NSDeterminantSignRuleReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

------------------------------------------------------------------------
-- Navier-Stokes corrected determinant sign rule receipt.
--
-- This module records the ordered and trace-free strain-eigenvalue assumptions
-- for incompressible 3D flow and the determinant/sign conversion:
-- with lambda1 <= lambda2 <= lambda3 and trace(S)=lambda1+lambda2+lambda3=0,
-- det(S) = lambda1 * lambda2 * lambda3 has the sign pattern
--   det(S) >= 0 ↔ lambda2 <= 0
--   det(S) < 0  ↔ lambda2 > 0
-- and the two set identifications
--   {lambda2 < 0} = {det(S) > 0}
--   {lambda2 > 0} = {det(S) < 0}.
--
-- Fail-closed promotion is recorded explicitly and the route remains blocked.

data NSDeterminantSignRuleStatus : Set where
  correctedDeterminantSignRuleRecorded : NSDeterminantSignRuleStatus

data NSDeterminantSignRuleAssumption : Set where
  orderedStrainEigenvalues :
    NSDeterminantSignRuleAssumption

  incompressibleTracelessStrain :
    NSDeterminantSignRuleAssumption

  determinantProductEncoding :
    NSDeterminantSignRuleAssumption

canonicalNSDeterminantSignRuleAssumptions :
  List NSDeterminantSignRuleAssumption
canonicalNSDeterminantSignRuleAssumptions =
  orderedStrainEigenvalues
  ∷ incompressibleTracelessStrain
  ∷ determinantProductEncoding
  ∷ []

orderedEigenvalueText : String
orderedEigenvalueText =
  "ordered-traceless frame assumption: lambda1 <= lambda2 <= lambda3 and lambda1 + lambda2 + lambda3 = 0"

determinantProductText : String
determinantProductText =
  "determinant encoding: det(S) = lambda1 * lambda2 * lambda3 with incompressibility trace assumption"

incompressibleSignRuleText : String
incompressibleSignRuleText =
  "sign rule under ordered + trace-free assumptions: det(S) >= 0 iff lambda2 <= 0, and det(S) < 0 iff lambda2 > 0."

omegaKNegativeSetText : String
omegaKNegativeSetText =
  "set identification (negative strain side): {lambda2 < 0} = {det(S) > 0}"

omegaKPositiveSetText : String
omegaKPositiveSetText =
  "set identification (positive strain side): {lambda2 > 0} = {det(S) < 0}"

data NSDeterminantSignRuleBlocker : Set where
  noPromotionWithoutFormalLift :
    NSDeterminantSignRuleBlocker
  noClayWithoutIndependentNavierStokesReceipt :
    NSDeterminantSignRuleBlocker
  noTerminalPromotionWithoutFormalTheorem :
    NSDeterminantSignRuleBlocker
  noExternalAuthorityShortcut :
    NSDeterminantSignRuleBlocker

canonicalNSDeterminantSignRuleBlockers :
  List NSDeterminantSignRuleBlocker
canonicalNSDeterminantSignRuleBlockers =
  noPromotionWithoutFormalLift
  ∷ noClayWithoutIndependentNavierStokesReceipt
  ∷ noTerminalPromotionWithoutFormalTheorem
  ∷ noExternalAuthorityShortcut
  ∷ []

record NSDeterminantSignRuleReceiptORCSLPGF : Set where
  constructor mkNSDeterminantSignRuleReceiptORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "O: Worker lane 2 records the corrected NS determinant-sign conversion for strain."

    R : String
    RIsCanonical : R ≡
      "R: Record ordered incompressible eigenvalue assumptions, the product-det sign rule, and the two set identifications."

    C : String
    CIsCanonical : C ≡
      "C: The artifact is a self-contained receipt module; no proofs are promoted, only assumptions, target identities, and blocker flags."

    S : String
    SIsCanonical : S ≡
      "S: assumptions=[ordered lambda1<=lambda2<=lambda3, traceless lambda1+lambda2+lambda3=0, det(S)=lambda1*lambda2*lambda3]; sign rule and set identifications are recorded; all promotion flags are false."

    L : String
    LIsCanonical : L ≡
      "L: Keep this lane as local handoff evidence for corrected determinant-sign geometry; block direct promotion until a formal theorem carrier is added."

    P : String
    PIsCanonical : P ≡
      "P: No determinant-sign theorem or Navier-Stokes closure is promoted from this receipt."

    G : String
    GIsCanonical : G ≡
      "G: No Clay, no external authority shortcut, and no terminal claim are made in this receipt."

    F : String
    FIsCanonical : F ≡
      "F: Promotion flags are explicitly fail-closed and routed through named blockers."

record NSDeterminantSignRuleReceipt : Setω where
  constructor mkNSDeterminantSignRuleReceipt
  field
    status :
      NSDeterminantSignRuleStatus

    statusIsCanonical :
      status ≡ correctedDeterminantSignRuleRecorded

    assumptionLedger :
      List NSDeterminantSignRuleAssumption

    assumptionLedgerIsCanonical :
      assumptionLedger ≡ canonicalNSDeterminantSignRuleAssumptions

    assumptionCount :
      Nat

    assumptionCountIsCanonical :
      assumptionCount ≡ listLength canonicalNSDeterminantSignRuleAssumptions

    blockerLedger :
      List NSDeterminantSignRuleBlocker

    blockerLedgerIsCanonical :
      blockerLedger ≡ canonicalNSDeterminantSignRuleBlockers

    blockerCount :
      Nat

    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSDeterminantSignRuleBlockers

    orderedAssumptionText :
      String

    orderedAssumptionTextIsCanonical :
      orderedAssumptionText ≡ orderedEigenvalueText

    productEncodingText :
      String

    productEncodingTextIsCanonical :
      productEncodingText ≡ determinantProductText

    signRuleText :
      String

    signRuleTextIsCanonical :
      signRuleText ≡ incompressibleSignRuleText

    omegaKNegativeText :
      String

    omegaKNegativeTextIsCanonical :
      omegaKNegativeText ≡ omegaKNegativeSetText

    omegaKPositiveText :
      String

    omegaKPositiveTextIsCanonical :
      omegaKPositiveText ≡ omegaKPositiveSetText

    determinantSignRuleFailClosed :
      Bool

    determinantSignRuleFailClosedIsTrue :
      determinantSignRuleFailClosed ≡ true

    determinantSignRulePromoted :
      Bool

    determinantSignRulePromotedIsFalse :
      determinantSignRulePromoted ≡ false

    nsCarrierToClayPromoted :
      Bool

    nsCarrierToClayPromotedIsFalse :
      nsCarrierToClayPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    externalAuthorityShortcutBlocked :
      Bool

    externalAuthorityShortcutBlockedIsTrue :
      externalAuthorityShortcutBlocked ≡ true

    orcslpgf :
      NSDeterminantSignRuleReceiptORCSLPGF

open NSDeterminantSignRuleReceipt public

canonicalNSDeterminantSignRuleReceiptORCSLPGF :
  NSDeterminantSignRuleReceiptORCSLPGF
canonicalNSDeterminantSignRuleReceiptORCSLPGF =
  mkNSDeterminantSignRuleReceiptORCSLPGF
    "O: Worker lane 2 records the corrected NS determinant-sign conversion for strain."
    refl
    "R: Record ordered incompressible eigenvalue assumptions, the product-det sign rule, and the two set identifications."
    refl
    "C: The artifact is a self-contained receipt module; no proofs are promoted, only assumptions, target identities, and blocker flags."
    refl
    "S: assumptions=[ordered lambda1<=lambda2<=lambda3, traceless lambda1+lambda2+lambda3=0, det(S)=lambda1*lambda2*lambda3]; sign rule and set identifications are recorded; all promotion flags are false."
    refl
    "L: Keep this lane as local handoff evidence for corrected determinant-sign geometry; block direct promotion until a formal theorem carrier is added."
    refl
    "P: No determinant-sign theorem or Navier-Stokes closure is promoted from this receipt."
    refl
    "G: No Clay, no external authority shortcut, and no terminal claim are made in this receipt."
    refl
    "F: Promotion flags are explicitly fail-closed and routed through named blockers."
    refl

canonicalNSDeterminantSignRuleReceipt :
  NSDeterminantSignRuleReceipt
canonicalNSDeterminantSignRuleReceipt =
  mkNSDeterminantSignRuleReceipt
    correctedDeterminantSignRuleRecorded
    refl
    canonicalNSDeterminantSignRuleAssumptions
    refl
    (listLength canonicalNSDeterminantSignRuleAssumptions)
    refl
    canonicalNSDeterminantSignRuleBlockers
    refl
    (listLength canonicalNSDeterminantSignRuleBlockers)
    refl
    orderedEigenvalueText
    refl
    determinantProductText
    refl
    incompressibleSignRuleText
    refl
    omegaKNegativeSetText
    refl
    omegaKPositiveSetText
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    true
    refl
    canonicalNSDeterminantSignRuleReceiptORCSLPGF
