module DASHI.Physics.Closure.NSPressureRieszCompatibilityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- NS pressure/Riesz compatibility receipt.
--
-- Route 1 ledger only.  The canonical content is:
--   -Delta p = h
--   h = ||S||_F^2 - |omega|^2/2
--   integral h = 0 on the torus
--   P11 = <e1, Hess p e1> represented through second-order Riesz
--   transforms of h.
--
-- These are compatibility / representation surfaces, not sign theorems.

data NSPressureRieszCompatibilityStatus : Set where
  route1PressureRieszCompatibilityLedgerRecorded :
    NSPressureRieszCompatibilityStatus

data NSPressureRieszCompatibilityPromotion : Set where

nsPressureRieszCompatibilityPromotionImpossibleHere :
  NSPressureRieszCompatibilityPromotion →
  ⊥
nsPressureRieszCompatibilityPromotionImpossibleHere ()

canonicalO : String
canonicalO =
  "O: route 1 pressure/Riesz compatibility ledger only."

canonicalR : String
canonicalR =
  "R: -Delta p = h and h = ||S||_F^2 - |omega|^2/2 are recorded as the source identities."

canonicalC : String
canonicalC =
  "C: integral h = 0 on the torus is recorded as the zero-mean compatibility surface."

canonicalS : String
canonicalS =
  "S: P11 = <e1, Hess p e1> is represented through second-order Riesz transforms of h."

canonicalL : String
canonicalL =
  "L: the pressure identities are compatibility and representation surfaces, not sign theorems."

canonicalP : String
canonicalP =
  "P: keep the route as a receipt surface only."

canonicalG : String
canonicalG =
  "G: promotion is false; no theorem or sign claim is promoted."

canonicalF : String
canonicalF =
  "F: fail closed on any attempt to upgrade the compatibility ledger to a sign theorem."

canonicalAssumptions : List String
canonicalAssumptions =
  "pressure is treated on the torus"
  ∷ "the source identity -Delta p = h is the ledger input"
  ∷ "h is read as ||S||_F^2 - |omega|^2/2"
  ∷ "integral h = 0 is the compatibility condition"
  ∷ "second-order Riesz transforms are the recorded representation surface"
  ∷ "no sign theorem is imported"
  ∷ []

canonicalStages : List String
canonicalStages =
  "source identity capture"
  ∷ "torus zero-mean compatibility"
  ∷ "pressure-Hessian projection capture"
  ∷ "second-order Riesz representation"
  ∷ "compatibility-only routing"
  ∷ "promotion quarantine"
  ∷ []

canonicalBlockers : List String
canonicalBlockers =
  "no sign theorem is supplied"
  ∷ "no positivity or sign definiteness is claimed"
  ∷ "route 1 remains a representation surface"
  ∷ "compatibility is recorded, not proved here"
  ∷ "promotion stays false"
  ∷ []

receiptBoundary : String
receiptBoundary =
  "Route 1 pressure/Riesz compatibility ledger: -Delta p = h, h = ||S||_F^2 - |omega|^2/2, integral h = 0 on the torus, P11 = <e1, Hess p e1> via second-order Riesz transforms of h, and the surface stays compatibility / representation only."

record NSPressureRieszCompatibilityReceipt : Setω where
  field
    status :
      NSPressureRieszCompatibilityStatus

    statusIsRecorded :
      status ≡ route1PressureRieszCompatibilityLedgerRecorded

    O :
      String

    OIsCanonical :
      O ≡ canonicalO

    R :
      String

    RIsCanonical :
      R ≡ canonicalR

    C :
      String

    CIsCanonical :
      C ≡ canonicalC

    S :
      String

    SIsCanonical :
      S ≡ canonicalS

    L :
      String

    LIsCanonical :
      L ≡ canonicalL

    P :
      String

    PIsCanonical :
      P ≡ canonicalP

    G :
      String

    GIsCanonical :
      G ≡ canonicalG

    F :
      String

    FIsCanonical :
      F ≡ canonicalF

    assumptions :
      List String

    assumptionsAreCanonical :
      assumptions ≡ canonicalAssumptions

    stages :
      List String

    stagesAreCanonical :
      stages ≡ canonicalStages

    blockers :
      List String

    blockersAreCanonical :
      blockers ≡ canonicalBlockers

    minusDeltaPEqualsH :
      Bool

    minusDeltaPEqualsHIsTrue :
      minusDeltaPEqualsH ≡ true

    zeroMeanCompatibilityRecorded :
      Bool

    zeroMeanCompatibilityRecordedIsTrue :
      zeroMeanCompatibilityRecorded ≡ true

    pressureHessianProjectionRecorded :
      Bool

    pressureHessianProjectionRecordedIsTrue :
      pressureHessianProjectionRecorded ≡ true

    rieszRepresentationRecorded :
      Bool

    rieszRepresentationRecordedIsTrue :
      rieszRepresentationRecorded ≡ true

    compatibilitySurfaceOnly :
      Bool

    compatibilitySurfaceOnlyIsTrue :
      compatibilitySurfaceOnly ≡ true

    authority :
      Bool

    authorityIsFalse :
      authority ≡ false

    routePromotion :
      Bool

    routePromotionIsFalse :
      routePromotion ≡ false

    theoremPromotion :
      Bool

    theoremPromotionIsFalse :
      theoremPromotion ≡ false

    signTheoremPromotion :
      Bool

    signTheoremPromotionIsFalse :
      signTheoremPromotion ≡ false

    representationPromotion :
      Bool

    representationPromotionIsFalse :
      representationPromotion ≡ false

    closurePromotion :
      Bool

    closurePromotionIsFalse :
      closurePromotion ≡ false

    promotionFlags :
      List NSPressureRieszCompatibilityPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    summary :
      String

    summaryIsCanonical :
      summary ≡ receiptBoundary

open NSPressureRieszCompatibilityReceipt public

canonicalNSPressureRieszCompatibilityReceipt :
  NSPressureRieszCompatibilityReceipt
canonicalNSPressureRieszCompatibilityReceipt =
  record
    { status =
        route1PressureRieszCompatibilityLedgerRecorded
    ; statusIsRecorded =
        refl
    ; O =
        canonicalO
    ; OIsCanonical =
        refl
    ; R =
        canonicalR
    ; RIsCanonical =
        refl
    ; C =
        canonicalC
    ; CIsCanonical =
        refl
    ; S =
        canonicalS
    ; SIsCanonical =
        refl
    ; L =
        canonicalL
    ; LIsCanonical =
        refl
    ; P =
        canonicalP
    ; PIsCanonical =
        refl
    ; G =
        canonicalG
    ; GIsCanonical =
        refl
    ; F =
        canonicalF
    ; FIsCanonical =
        refl
    ; assumptions =
        canonicalAssumptions
    ; assumptionsAreCanonical =
        refl
    ; stages =
        canonicalStages
    ; stagesAreCanonical =
        refl
    ; blockers =
        canonicalBlockers
    ; blockersAreCanonical =
        refl
    ; minusDeltaPEqualsH =
        true
    ; minusDeltaPEqualsHIsTrue =
        refl
    ; zeroMeanCompatibilityRecorded =
        true
    ; zeroMeanCompatibilityRecordedIsTrue =
        refl
    ; pressureHessianProjectionRecorded =
        true
    ; pressureHessianProjectionRecordedIsTrue =
        refl
    ; rieszRepresentationRecorded =
        true
    ; rieszRepresentationRecordedIsTrue =
        refl
    ; compatibilitySurfaceOnly =
        true
    ; compatibilitySurfaceOnlyIsTrue =
        refl
    ; authority =
        false
    ; authorityIsFalse =
        refl
    ; routePromotion =
        false
    ; routePromotionIsFalse =
        refl
    ; theoremPromotion =
        false
    ; theoremPromotionIsFalse =
        refl
    ; signTheoremPromotion =
        false
    ; signTheoremPromotionIsFalse =
        refl
    ; representationPromotion =
        false
    ; representationPromotionIsFalse =
        refl
    ; closurePromotion =
        false
    ; closurePromotionIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; summary =
        receiptBoundary
    ; summaryIsCanonical =
        refl
    }
