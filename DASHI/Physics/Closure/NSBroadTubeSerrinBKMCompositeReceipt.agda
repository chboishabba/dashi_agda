module DASHI.Physics.Closure.NSBroadTubeSerrinBKMCompositeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSBroadTubeCoareaBridgeReceipt as Coarea
import DASHI.Physics.Closure.NSBroadTubeSerrinLiftReceipt as Serrin
import DASHI.Physics.Closure.NSBroadTubeBKMBridgeReceipt as BKM

------------------------------------------------------------------------
-- Composite receipt for the broad-tube coarea → Serrin-lift → BKM bridge
-- route.
--
-- This module records the chain:
--   broad-tube coarea -> Serrin lift -> BKM bridge -> conditional
--   no-blowup socket
-- and keeps Clay promotion explicitly false.

data NSBroadTubeSerrinBKMCompositeStatus : Set where
  broadTubeSerrinBKMChainRecorded :
    NSBroadTubeSerrinBKMCompositeStatus

compositeChainStatement : String
compositeChainStatement =
  "broadTubeCoarea -> Serrin lift -> BKM bridge -> conditional no-blowup socket"

compositeChainBoundary : String
compositeChainBoundary =
  "This composite links broad-tube coarea, Serrin-lift, and BKM bridge nodes; conditional no-blowup remains, and Clay promotion is explicitly false."

canonicalCompositeGateLabels : List String
canonicalCompositeGateLabels =
  "NSBroadTubeCoareaBridge"
  ∷ "NSBroadTubeSerrinLift"
  ∷ "NSBroadTubeBKMBridge"
  ∷ "conditional no-blowup socket"
  ∷ []

record NSBroadTubeSerrinBKMCompositeReceipt : Setω where
  field
    status :
      NSBroadTubeSerrinBKMCompositeStatus

    statusIsRecorded :
      status ≡ broadTubeSerrinBKMChainRecorded

    coareaGateReceipt :
      Coarea.NSBroadTubeCoareaBridgeReceipt

    serrinLiftReceipt :
      Serrin.NSBroadTubeSerrinLiftReceipt

    bkmBridgeReceipt :
      BKM.NSBroadTubeBKMBridgeReceipt

    compositeGateNames :
      List String

    compositeGateNamesAreCanonical :
      compositeGateNames ≡ canonicalCompositeGateLabels

    compositeBridgeImplemented :
      Bool

    compositeBridgeImplementedIsTrue :
      compositeBridgeImplemented ≡ true

    conditionalNoBlowupSocket :
      Bool

    conditionalNoBlowupSocketIsTrue :
      conditionalNoBlowupSocket ≡ true

    allThreeGatesNamed :
      Bool

    allThreeGatesNamedIsTrue :
      allThreeGatesNamed ≡ true

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ compositeChainStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ compositeChainBoundary

    receiptPath :
      List String

    receiptPathIsCanonical :
      receiptPath ≡
        "broadTubeCoarea"
        ∷ "Serrin lift"
        ∷ "BKM bridge"
        ∷ "conditional no-blowup socket"
        ∷ []

open NSBroadTubeSerrinBKMCompositeReceipt public

canonicalNSBroadTubeSerrinBKMCompositeReceipt :
  NSBroadTubeSerrinBKMCompositeReceipt
canonicalNSBroadTubeSerrinBKMCompositeReceipt =
  record
    { status =
        broadTubeSerrinBKMChainRecorded
    ; statusIsRecorded =
        refl
    ; coareaGateReceipt =
        Coarea.canonicalNSBroadTubeCoareaBridgeReceipt
    ; serrinLiftReceipt =
        Serrin.canonicalNSBroadTubeSerrinLiftReceipt
    ; bkmBridgeReceipt =
        BKM.canonicalNSBroadTubeBKMBridgeReceipt
    ; compositeGateNames =
        canonicalCompositeGateLabels
    ; compositeGateNamesAreCanonical =
        refl
    ; compositeBridgeImplemented =
        true
    ; compositeBridgeImplementedIsTrue =
        refl
    ; conditionalNoBlowupSocket =
        true
    ; conditionalNoBlowupSocketIsTrue =
        BKM.noBlowupSocketIsTrue BKM.canonicalNSBroadTubeBKMBridgeReceipt
    ; allThreeGatesNamed =
        true
    ; allThreeGatesNamedIsTrue =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; statement =
        compositeChainStatement
    ; statementIsCanonical =
        refl
    ; boundary =
        compositeChainBoundary
    ; boundaryIsCanonical =
        refl
    ; receiptPath =
        "broadTubeCoarea"
        ∷ "Serrin lift"
        ∷ "BKM bridge"
        ∷ "conditional no-blowup socket"
        ∷ []
    ; receiptPathIsCanonical =
        refl
    }

canonicalNSBroadTubeSerrinBKMCompositeRecorded :
  compositeBridgeImplemented canonicalNSBroadTubeSerrinBKMCompositeReceipt ≡ true
canonicalNSBroadTubeSerrinBKMCompositeRecorded =
  refl

canonicalNSBroadTubeSerrinBKMCompositeHasConditionalNoBlowup :
  conditionalNoBlowupSocket canonicalNSBroadTubeSerrinBKMCompositeReceipt ≡ true
canonicalNSBroadTubeSerrinBKMCompositeHasConditionalNoBlowup =
  refl

canonicalNSBroadTubeSerrinBKMCompositeKeepsClayClosed :
  clayPromotion canonicalNSBroadTubeSerrinBKMCompositeReceipt ≡ false
canonicalNSBroadTubeSerrinBKMCompositeKeepsClayClosed =
  refl
