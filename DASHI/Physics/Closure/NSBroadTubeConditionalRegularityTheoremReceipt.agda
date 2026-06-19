module DASHI.Physics.Closure.NSBroadTubeConditionalRegularityTheoremReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSBroadTubeNondegenerateGradientReceipt as Grad
import DASHI.Physics.Closure.NSBroadTubeVorticityCoverageReceipt as Vort
import DASHI.Physics.Closure.NSBroadTubeSerrinExponentDischargeReceipt as Exp
import DASHI.Physics.Closure.NSBroadTubeCoareaBridgeReceipt as Coarea
import DASHI.Physics.Closure.NSBroadTubeSerrinLiftReceipt as Serrin
import DASHI.Physics.Closure.NSBroadTubeBKMBridgeReceipt as BKM
import DASHI.Physics.Closure.NSBroadTubeSerrinBKMCompositeReceipt as Composite

------------------------------------------------------------------------
-- Composite conditional regularity socket receipt.
--
-- This file records the route:
--   nondegenerate gradient + vorticity coverage + Serrin exponent discharge
--   + broad-tube coarea/Serrin/BKM composite -> conditional regularity socket.
--
-- The record is import-light and list-led so later worker receipts can be
-- merged with low risk.  It is conditional only: unconditionalClayNS is false,
-- clayPromotion is false, and the conditional regularity socket is constructed
-- while no-promotion remains in force.  The promotion gate is pinned to the
-- imported proof-term receipts themselves, not just to route labels.

data NSBroadTubeConditionalRegularityTheoremStatus : Set where
  conditionalRegularitySocketConstructedConditionally :
    NSBroadTubeConditionalRegularityTheoremStatus

data NSBroadTubeConditionalRegularityTheoremDependency : Set where
  nondegenerateGradientReceiptDependency :
    NSBroadTubeConditionalRegularityTheoremDependency

  vorticityCoverageReceiptDependency :
    NSBroadTubeConditionalRegularityTheoremDependency

  serrinExponentDischargeReceiptDependency :
    NSBroadTubeConditionalRegularityTheoremDependency

  broadTubeCoareaReceiptDependency :
    NSBroadTubeConditionalRegularityTheoremDependency

  broadTubeSerrinReceiptDependency :
    NSBroadTubeConditionalRegularityTheoremDependency

  broadTubeBKMReceiptDependency :
    NSBroadTubeConditionalRegularityTheoremDependency

  broadTubeCompositeReceiptDependency :
    NSBroadTubeConditionalRegularityTheoremDependency

canonicalNSBroadTubeConditionalRegularityTheoremDependencies :
  List NSBroadTubeConditionalRegularityTheoremDependency
canonicalNSBroadTubeConditionalRegularityTheoremDependencies =
  nondegenerateGradientReceiptDependency
  ∷ vorticityCoverageReceiptDependency
  ∷ serrinExponentDischargeReceiptDependency
  ∷ broadTubeCoareaReceiptDependency
  ∷ broadTubeSerrinReceiptDependency
  ∷ broadTubeBKMReceiptDependency
  ∷ broadTubeCompositeReceiptDependency
  ∷ []

canonicalNSBroadTubeConditionalRegularityTheoremDependencyNames :
  List String
canonicalNSBroadTubeConditionalRegularityTheoremDependencyNames =
  "nondegenerate gradient receipt"
  ∷ "vorticity coverage receipt"
  ∷ "Serrin exponent discharge receipt"
  ∷ "broad-tube coarea bridge receipt"
  ∷ "broad-tube Serrin lift receipt"
  ∷ "broad-tube BKM bridge receipt"
  ∷ "broad-tube Serrin/BKM composite receipt"
  ∷ []

data NSBroadTubeConditionalRegularityTheoremStep : Set where
  importNondegenerateGradientReceipt :
    NSBroadTubeConditionalRegularityTheoremStep

  importVorticityCoverageReceipt :
    NSBroadTubeConditionalRegularityTheoremStep

  dischargeSerrinExponent :
    NSBroadTubeConditionalRegularityTheoremStep

  importBroadTubeCoareaBridge :
    NSBroadTubeConditionalRegularityTheoremStep

  importBroadTubeSerrinLift :
    NSBroadTubeConditionalRegularityTheoremStep

  importBroadTubeBKMBridge :
    NSBroadTubeConditionalRegularityTheoremStep

  importBroadTubeSerrinBKMComposite :
    NSBroadTubeConditionalRegularityTheoremStep

  constructConditionalRegularitySocket :
    NSBroadTubeConditionalRegularityTheoremStep

canonicalNSBroadTubeConditionalRegularityTheoremSteps :
  List NSBroadTubeConditionalRegularityTheoremStep
canonicalNSBroadTubeConditionalRegularityTheoremSteps =
  importNondegenerateGradientReceipt
  ∷ importVorticityCoverageReceipt
  ∷ dischargeSerrinExponent
  ∷ importBroadTubeCoareaBridge
  ∷ importBroadTubeSerrinLift
  ∷ importBroadTubeBKMBridge
  ∷ importBroadTubeSerrinBKMComposite
  ∷ constructConditionalRegularitySocket
  ∷ []

data NSBroadTubeConditionalRegularityTheoremOpenBoundary : Set where
  workerReceiptsRemainImportOnly :
    NSBroadTubeConditionalRegularityTheoremOpenBoundary

  conditionalRouteOnly :
    NSBroadTubeConditionalRegularityTheoremOpenBoundary

  unconditionalClayNSNotClaimed :
    NSBroadTubeConditionalRegularityTheoremOpenBoundary

  clayPromotionNotClaimed :
    NSBroadTubeConditionalRegularityTheoremOpenBoundary

  noPromotionBoundaryRetained :
    NSBroadTubeConditionalRegularityTheoremOpenBoundary

canonicalNSBroadTubeConditionalRegularityTheoremOpenBoundaries :
  List NSBroadTubeConditionalRegularityTheoremOpenBoundary
canonicalNSBroadTubeConditionalRegularityTheoremOpenBoundaries =
  workerReceiptsRemainImportOnly
  ∷ conditionalRouteOnly
  ∷ unconditionalClayNSNotClaimed
  ∷ clayPromotionNotClaimed
  ∷ noPromotionBoundaryRetained
  ∷ []

data NSBroadTubeConditionalRegularityTheoremNoPromotion : Set where

noNSBroadTubeConditionalRegularityTheoremPromotion :
  NSBroadTubeConditionalRegularityTheoremNoPromotion →
  ⊥
noNSBroadTubeConditionalRegularityTheoremPromotion ()

routeStatement : String
routeStatement =
  "nondegenerate gradient + vorticity coverage + Serrin exponent discharge + broad-tube coarea/Serrin/BKM composite -> conditional regularity socket"

routeBoundary : String
routeBoundary =
  "Conditional only: unconditionalClayNS is false, clayPromotion is false, the conditional regularity socket is constructed, and no-promotion remains in force."

record NSBroadTubeConditionalRegularityTheoremORCSLPGF : Set where
  constructor mkNSBroadTubeConditionalRegularityTheoremORCSLPGF
  field
    O :
      String
    OIsCanonical :
      O ≡
      "Record a conditional broad-tube regularity route with explicit socket aggregation."

    R :
      String
    RIsCanonical :
      R ≡
      "Record the nondegenerate gradient, vorticity coverage, Serrin exponent discharge, and broad-tube composite route as a receipt."

    C :
      String
    CIsCanonical :
      C ≡
      "Create only NSBroadTubeConditionalRegularityTheoremReceipt.agda."

    S :
      String
    SIsCanonical :
      S ≡
      "nondegenerate gradient, vorticity coverage, Serrin exponent discharge, broad-tube coarea, Serrin lift, BKM bridge, broad-tube composite"

    L :
      String
    LIsCanonical :
      L ≡
      "nondegenerate gradient -> vorticity coverage -> Serrin exponent discharge -> broad-tube coarea/Serrin/BKM composite -> conditional regularity socket"

    P :
      String
    PIsCanonical :
      P ≡
      "nondegenerate gradient receipt; vorticity coverage receipt; Serrin exponent discharge receipt; broad-tube coarea bridge; broad-tube Serrin lift; broad-tube BKM bridge; broad-tube Serrin/BKM composite"

    G :
      String
    GIsCanonical :
      G ≡
      "unconditionalClayNS=false; clayPromotion=false; conditionalRegularitySocketConstructed=true"

    F :
      String
    FIsCanonical :
      F ≡
      "no-promotion boundary retained; the route is conditional only"

open NSBroadTubeConditionalRegularityTheoremORCSLPGF public

canonicalNSBroadTubeConditionalRegularityTheoremORCSLPGF :
  NSBroadTubeConditionalRegularityTheoremORCSLPGF
canonicalNSBroadTubeConditionalRegularityTheoremORCSLPGF =
  mkNSBroadTubeConditionalRegularityTheoremORCSLPGF
    "Record a conditional broad-tube regularity route with explicit socket aggregation."
    refl
    "Record the nondegenerate gradient, vorticity coverage, Serrin exponent discharge, and broad-tube composite route as a receipt."
    refl
    "Create only NSBroadTubeConditionalRegularityTheoremReceipt.agda."
    refl
    "nondegenerate gradient, vorticity coverage, Serrin exponent discharge, broad-tube coarea, Serrin lift, BKM bridge, broad-tube composite"
    refl
    "nondegenerate gradient -> vorticity coverage -> Serrin exponent discharge -> broad-tube coarea/Serrin/BKM composite -> conditional regularity socket"
    refl
    "nondegenerate gradient receipt; vorticity coverage receipt; Serrin exponent discharge receipt; broad-tube coarea bridge; broad-tube Serrin lift; broad-tube BKM bridge; broad-tube Serrin/BKM composite"
    refl
    "unconditionalClayNS=false; clayPromotion=false; conditionalRegularitySocketConstructed=true"
    refl
    "no-promotion boundary retained; the route is conditional only"
    refl

record NSBroadTubeConditionalRegularityTheoremReceipt : Setω where
  field
    status :
      NSBroadTubeConditionalRegularityTheoremStatus

    statusIsCanonical :
      status ≡ conditionalRegularitySocketConstructedConditionally

    dependencies :
      List NSBroadTubeConditionalRegularityTheoremDependency

    dependenciesAreCanonical :
      dependencies ≡
      canonicalNSBroadTubeConditionalRegularityTheoremDependencies

    dependencyNames :
      List String

    dependencyNamesAreCanonical :
      dependencyNames ≡
      canonicalNSBroadTubeConditionalRegularityTheoremDependencyNames

    steps :
      List NSBroadTubeConditionalRegularityTheoremStep

    stepsAreCanonical :
      steps ≡ canonicalNSBroadTubeConditionalRegularityTheoremSteps

    openBoundaries :
      List NSBroadTubeConditionalRegularityTheoremOpenBoundary

    openBoundariesAreCanonical :
      openBoundaries ≡
      canonicalNSBroadTubeConditionalRegularityTheoremOpenBoundaries

    nondegenerateGradientReceipt :
      Grad.NSBroadTubeNondegenerateGradientReceipt

    vorticityCoverageReceipt :
      Vort.NSBroadTubeVorticityCoverageReceipt

    serrinExponentDischargeReceipt :
      Exp.NSBroadTubeSerrinExponentDischargeReceipt

    broadTubeCoareaBridgeReceipt :
      Coarea.NSBroadTubeCoareaBridgeReceipt

    broadTubeSerrinLiftReceipt :
      Serrin.NSBroadTubeSerrinLiftReceipt

    broadTubeBKMBridgeReceipt :
      BKM.NSBroadTubeBKMBridgeReceipt

    broadTubeSerrinBKMCompositeReceipt :
      Composite.NSBroadTubeSerrinBKMCompositeReceipt

    promotionGateSatisfied :
      Bool

    promotionGateSatisfiedIsFalse :
      promotionGateSatisfied ≡ false

    nondegenerateGradientSocketConstructed :
      Bool

    nondegenerateGradientSocketConstructedIsTrue :
      nondegenerateGradientSocketConstructed ≡ true

    vorticityCoverageRecorded :
      Bool

    vorticityCoverageRecordedIsTrue :
      vorticityCoverageRecorded ≡ true

    serrinExponentDischarged :
      Bool

    serrinExponentDischargedIsTrue :
      serrinExponentDischarged ≡ true

    broadTubeCompositeRecorded :
      Bool

    broadTubeCompositeRecordedIsTrue :
      broadTubeCompositeRecorded ≡ true

    conditionalRegularitySocketConstructed :
      Bool

    conditionalRegularitySocketConstructedIsTrue :
      conditionalRegularitySocketConstructed ≡ true

    unconditionalClayNS :
      Bool

    unconditionalClayNSIsFalse :
      unconditionalClayNS ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    promotionBlockers :
      List String

    promotionBlockersAreCanonical :
      promotionBlockers ≡
      "unconditional Clay promotion remains false"
      ∷ "unconditional regularity promotion remains false"
      ∷ "promotion stays conditional on the imported proof-term receipts"
      ∷ []

    statement :
      String

    statementIsCanonical :
      statement ≡ routeStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ routeBoundary

    noPromotionLedger :
      List NSBroadTubeConditionalRegularityTheoremNoPromotion

    noPromotionLedgerIsEmpty :
      noPromotionLedger ≡ []

    orcslpgf :
      NSBroadTubeConditionalRegularityTheoremORCSLPGF

    orcslpgfIsCanonical :
      orcslpgf ≡
      canonicalNSBroadTubeConditionalRegularityTheoremORCSLPGF

open NSBroadTubeConditionalRegularityTheoremReceipt public

canonicalNSBroadTubeConditionalRegularityTheoremReceipt :
  NSBroadTubeConditionalRegularityTheoremReceipt
canonicalNSBroadTubeConditionalRegularityTheoremReceipt =
  record
    { status =
        conditionalRegularitySocketConstructedConditionally
    ; statusIsCanonical =
        refl
    ; dependencies =
        canonicalNSBroadTubeConditionalRegularityTheoremDependencies
    ; dependenciesAreCanonical =
        refl
    ; dependencyNames =
        canonicalNSBroadTubeConditionalRegularityTheoremDependencyNames
    ; dependencyNamesAreCanonical =
        refl
    ; steps =
        canonicalNSBroadTubeConditionalRegularityTheoremSteps
    ; stepsAreCanonical =
        refl
    ; openBoundaries =
        canonicalNSBroadTubeConditionalRegularityTheoremOpenBoundaries
    ; openBoundariesAreCanonical =
        refl
    ; nondegenerateGradientReceipt =
        Grad.canonicalNSBroadTubeNondegenerateGradientReceipt
    ; vorticityCoverageReceipt =
        Vort.canonicalNSBroadTubeVorticityCoverageReceipt
    ; serrinExponentDischargeReceipt =
        Exp.canonicalNSBroadTubeSerrinExponentDischargeReceipt
    ; broadTubeCoareaBridgeReceipt =
        Coarea.canonicalNSBroadTubeCoareaBridgeReceipt
    ; broadTubeSerrinLiftReceipt =
        Serrin.canonicalNSBroadTubeSerrinLiftReceipt
    ; broadTubeBKMBridgeReceipt =
        BKM.canonicalNSBroadTubeBKMBridgeReceipt
    ; broadTubeSerrinBKMCompositeReceipt =
        Composite.canonicalNSBroadTubeSerrinBKMCompositeReceipt
    ; promotionGateSatisfied =
        false
    ; promotionGateSatisfiedIsFalse =
        refl
    ; nondegenerateGradientSocketConstructed =
        true
    ; nondegenerateGradientSocketConstructedIsTrue =
        refl
    ; vorticityCoverageRecorded =
        true
    ; vorticityCoverageRecordedIsTrue =
        refl
    ; serrinExponentDischarged =
        true
    ; serrinExponentDischargedIsTrue =
        refl
    ; broadTubeCompositeRecorded =
        true
    ; broadTubeCompositeRecordedIsTrue =
        refl
    ; conditionalRegularitySocketConstructed =
        true
    ; conditionalRegularitySocketConstructedIsTrue =
        refl
    ; unconditionalClayNS =
        false
    ; unconditionalClayNSIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; promotionBlockers =
        "unconditional Clay promotion remains false"
        ∷ "unconditional regularity promotion remains false"
        ∷ "promotion stays conditional on the imported proof-term receipts"
        ∷ []
    ; promotionBlockersAreCanonical =
        refl
    ; statement =
        routeStatement
    ; statementIsCanonical =
        refl
    ; boundary =
        routeBoundary
    ; boundaryIsCanonical =
        refl
    ; noPromotionLedger =
        []
    ; noPromotionLedgerIsEmpty =
        refl
    ; orcslpgf =
        canonicalNSBroadTubeConditionalRegularityTheoremORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    }
