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
import DASHI.Physics.Closure.NSConditionalQGronwallTheoremGReceipt as TheoremG
import DASHI.Physics.Closure.NSLayerL2VorticityFractionReceipt as Q2
import DASHI.Physics.Closure.NSGD1MinPrincipleNoLambda3CollapseReceipt as GD1

------------------------------------------------------------------------
-- Composite conditional regularity socket receipt (strengthened final-assembly
-- form).
--
-- This file now records an explicit final BKM/Serrin contradiction assembly
-- route, including the BKM criterion requirement of
-- "int ||omega||_infty dt", the reason L8L4 velocity is insufficient, and
-- the required TheoremG/Q2 + GD1 biaxial-carrier contradiction chain.
--
-- The route stays conditional only.  It does not promote Clay, and does not
-- claim unconditional regularity.  promotionGateSatisfied is explicitly false.

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

  theoremGReceiptDependency :
    NSBroadTubeConditionalRegularityTheoremDependency

  q2ReceiptDependency :
    NSBroadTubeConditionalRegularityTheoremDependency

  gd1ReceiptDependency :
    NSBroadTubeConditionalRegularityTheoremDependency

  standardBridgeDependency :
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
  ∷ theoremGReceiptDependency
  ∷ q2ReceiptDependency
  ∷ gd1ReceiptDependency
  ∷ standardBridgeDependency
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
  ∷ "TheoremG conditional receipt"
  ∷ "Q2 (SerrinFromQ2Control) layer-fraction receipt"
  ∷ "GD1 biaxial-carrier minimum-principle receipt"
  ∷ "standard bridge: TheoremG+Q2+GD1 assembly"
  ∷ []

data NSBroadTubeConditionalRegularityTheoremRouteRow : Set where
  finalBKMSSerrinAssemblyShapeRecorded :
    NSBroadTubeConditionalRegularityTheoremRouteRow

  bkmCriterionRequiresVorticityIntegral :
    NSBroadTubeConditionalRegularityTheoremRouteRow

  l84l4VelocityInsufficientForBkm :
    NSBroadTubeConditionalRegularityTheoremRouteRow

  theoremGQ2GD1BiaxialCarrierChainRecorded :
    NSBroadTubeConditionalRegularityTheoremRouteRow

  standardBridgeRecordedConditionally :
    NSBroadTubeConditionalRegularityTheoremRouteRow

  hardLemmasAllConditionallyRecordedRow :
    NSBroadTubeConditionalRegularityTheoremRouteRow

canonicalNSBroadTubeConditionalRegularityTheoremRouteLedger :
  List NSBroadTubeConditionalRegularityTheoremRouteRow
canonicalNSBroadTubeConditionalRegularityTheoremRouteLedger =
  finalBKMSSerrinAssemblyShapeRecorded
  ∷ bkmCriterionRequiresVorticityIntegral
  ∷ l84l4VelocityInsufficientForBkm
  ∷ theoremGQ2GD1BiaxialCarrierChainRecorded
  ∷ standardBridgeRecordedConditionally
  ∷ hardLemmasAllConditionallyRecordedRow
  ∷ []

finalBKMSSerrinAssemblyText : String
finalBKMSSerrinAssemblyText =
  "final BKM/Serrin contradiction assembly: Serrin-admissible (8,4) route + vorticity-time integral continuation"

bkmCriterionRequirementText : String
bkmCriterionRequirementText =
  "BKM criterion requirement remains explicit: int ||omega||_infty dt must be bounded for continuation"

l84L4InsufficiencyText : String
l84L4InsufficiencyText =
  "velocity L8L4 estimate alone is insufficient; it does not yield the BKM continuation gate without stronger vorticity control"

theoremGQ2GD1ChainText : String
theoremGQ2GD1ChainText =
  "actual required contradiction shape: TheoremG + Q2 + GD1 gives a conditional contradiction channel on the biaxial carrier"

standardBridgeConditionalText : String
standardBridgeConditionalText =
  "standard bridge is recorded conditionally and is not promoted to unconditional Clay closure"

theoremGReceiptModule : String
theoremGReceiptModule =
  "DASHI.Physics.Closure.NSConditionalQGronwallTheoremGReceipt"

q2ReceiptModule : String
q2ReceiptModule =
  "DASHI.Physics.Closure.NSLayerL2VorticityFractionReceipt"

gd1ReceiptModule : String
gd1ReceiptModule =
  "DASHI.Physics.Closure.NSGD1MinPrincipleNoLambda3CollapseReceipt"

hardLemmaTexts : List String
hardLemmaTexts =
  "hard lemma: TheoremG required (and recorded conditionally)"
  ∷ "hard lemma: Q2 (SerrinFromQ2Control) required (and recorded conditionally)"
  ∷ "hard lemma: GD1 + biaxial-carrier condition required (and recorded conditionally)"
  ∷ []

canonicalNSBroadTubeConditionalRegularityTheoremRouteLedgerText :
  List String
canonicalNSBroadTubeConditionalRegularityTheoremRouteLedgerText =
  finalBKMSSerrinAssemblyText
  ∷ bkmCriterionRequirementText
  ∷ l84L4InsufficiencyText
  ∷ theoremGQ2GD1ChainText
  ∷ standardBridgeConditionalText
  ∷ "hard lemma: TheoremG required (and recorded conditionally)"
  ∷ "hard lemma: Q2 (SerrinFromQ2Control) required (and recorded conditionally)"
  ∷ "hard lemma: GD1 + biaxial-carrier condition required (and recorded conditionally)"
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

  importTheoremGReceipt :
    NSBroadTubeConditionalRegularityTheoremStep

  importQ2Receipt :
    NSBroadTubeConditionalRegularityTheoremStep

  importGD1Receipt :
    NSBroadTubeConditionalRegularityTheoremStep

  recordStandardBridgeConditionally :
    NSBroadTubeConditionalRegularityTheoremStep

  recordHardLemmasConditionally :
    NSBroadTubeConditionalRegularityTheoremStep

  recordFinalBKMSSerrinAssembly :
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
  ∷ importTheoremGReceipt
  ∷ importQ2Receipt
  ∷ importGD1Receipt
  ∷ recordStandardBridgeConditionally
  ∷ recordHardLemmasConditionally
  ∷ recordFinalBKMSSerrinAssembly
  ∷ constructConditionalRegularitySocket
  ∷ []

data NSBroadTubeConditionalRegularityTheoremHardLemma : Set where
  theoremGRequiredConditionally :
    NSBroadTubeConditionalRegularityTheoremHardLemma

  q2InputRequiredConditionally :
    NSBroadTubeConditionalRegularityTheoremHardLemma

  gd1BiaxialCarrierRequiredConditionally :
    NSBroadTubeConditionalRegularityTheoremHardLemma

canonicalNSBroadTubeConditionalRegularityTheoremHardLemmas :
  List NSBroadTubeConditionalRegularityTheoremHardLemma
canonicalNSBroadTubeConditionalRegularityTheoremHardLemmas =
  theoremGRequiredConditionally
  ∷ q2InputRequiredConditionally
  ∷ gd1BiaxialCarrierRequiredConditionally
  ∷ []

data NSBroadTubeConditionalRegularityTheoremStandardBridge : Set where
  standardBridgeConditionallyRecorded :
    NSBroadTubeConditionalRegularityTheoremStandardBridge

canonicalNSBroadTubeConditionalRegularityTheoremStandardBridge :
  List NSBroadTubeConditionalRegularityTheoremStandardBridge
canonicalNSBroadTubeConditionalRegularityTheoremStandardBridge =
  standardBridgeConditionallyRecorded
  ∷ []

data NSBroadTubeConditionalRegularityTheoremOpenBoundary : Set where
  workerReceiptsRemainImportOnly :
    NSBroadTubeConditionalRegularityTheoremOpenBoundary

  conditionalRouteOnly :
    NSBroadTubeConditionalRegularityTheoremOpenBoundary

  hardLemmasRecordedConditionally :
    NSBroadTubeConditionalRegularityTheoremOpenBoundary

  standardBridgeRecordedConditionally :
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
  ∷ hardLemmasRecordedConditionally
  ∷ standardBridgeRecordedConditionally
  ∷ unconditionalClayNSNotClaimed
  ∷ clayPromotionNotClaimed
  ∷ noPromotionBoundaryRetained
  ∷ []

data NSBroadTubeConditionalRegularityTheoremFinalAssemblyBlocker : Set where
  bkmCriterionIntegralRequirementRecordedAsGate :
    NSBroadTubeConditionalRegularityTheoremFinalAssemblyBlocker

  l84L4GateInsufficient :
    NSBroadTubeConditionalRegularityTheoremFinalAssemblyBlocker

  theoremGQ2GD1ChainConditionallyOpen :
    NSBroadTubeConditionalRegularityTheoremFinalAssemblyBlocker

  standardBridgeNotPromoted :
    NSBroadTubeConditionalRegularityTheoremFinalAssemblyBlocker

canonicalNSBroadTubeConditionalRegularityTheoremFinalAssemblyBlockers :
  List NSBroadTubeConditionalRegularityTheoremFinalAssemblyBlocker
canonicalNSBroadTubeConditionalRegularityTheoremFinalAssemblyBlockers =
  bkmCriterionIntegralRequirementRecordedAsGate
  ∷ l84L4GateInsufficient
  ∷ theoremGQ2GD1ChainConditionallyOpen
  ∷ standardBridgeNotPromoted
  ∷ []

canonicalNSBroadTubeConditionalRegularityTheoremFinalAssemblyBlockerText :
  List String
canonicalNSBroadTubeConditionalRegularityTheoremFinalAssemblyBlockerText =
  "int ||omega||_infty dt is required for BKM continuation"
  ∷ "L8L4 velocity alone cannot close BKM"
  ∷ "TheoremG/Q2 + GD1 contradiction structure is conditional"
  ∷ "standard bridge remains conditional and is not Clay-promoted"
  ∷ []

data NSBroadTubeConditionalRegularityTheoremNoPromotion : Set where

noNSBroadTubeConditionalRegularityTheoremPromotion :
  NSBroadTubeConditionalRegularityTheoremNoPromotion →
  ⊥
noNSBroadTubeConditionalRegularityTheoremPromotion ()

routeStatement : String
routeStatement =
  "nondegenerate gradient + vorticity coverage + Serrin exponent discharge + broad-tube coarea/Serrin/BKM composite + final BKM/Serrin contradiction assembly -> conditional regularity socket"

routeBoundary : String
routeBoundary =
  "Conditional only: promotionGateSatisfied is false, unconditionalClayNS is false, and the conditional regularity socket is assembled from recorded dependencies while hard lemmas and standard bridge remain conditional."

record NSBroadTubeConditionalRegularityTheoremORCSLPGF : Set where
  constructor mkNSBroadTubeConditionalRegularityTheoremORCSLPGF
  field
    O :
      String
    OIsCanonical :
      O ≡
      "Record the final broad-tube conditional regularity composite with an explicit BKM/Serrin final-assembly ledger."

    R :
      String
    RIsCanonical :
      R ≡
      "Compose nondegenerate gradient, vorticity coverage, Serrin exponent discharge, and TheoremG/Q2/GD1 conditional inputs into the final broad-tube regularity route."

    C :
      String
    CIsCanonical :
      C ≡
      "Create only NSBroadTubeConditionalRegularityTheoremReceipt.agda."

    S :
      String
    SIsCanonical :
      S ≡
      "broad-tube gradient/vorticity/serrin/Serrin-BKM nodes + final BKM/Serrin contradiction ledger + conditional hard lemmas + conditional standard bridge"

    L :
      String
    LIsCanonical :
      L ≡
      "route: nondegenerate gradient -> vorticity coverage -> Serrin exponent discharge -> coarea -> Serrin lift -> BKM bridge -> composite -> final BKM/Serrin assembly -> conditional regularity socket"

    P :
      String
    PIsCanonical :
      P ≡
      "construct BKM/Serrin final-assembly shape, record TheoremG/Q2/GD1 conditional inputs, and register L8L4 insufficiency plus int ||omega||_infty dt requirement."

    G :
      String
    GIsCanonical :
      G ≡
      "promotionGateSatisfied=false; unconditionalClayNS=false; hard lemmas and standard bridge are conditional"

    F :
      String
    FIsCanonical :
      F ≡
      "final assembly remains conditional-only; no promoted Clay route is introduced here."

open NSBroadTubeConditionalRegularityTheoremORCSLPGF public

canonicalNSBroadTubeConditionalRegularityTheoremORCSLPGF :
  NSBroadTubeConditionalRegularityTheoremORCSLPGF
canonicalNSBroadTubeConditionalRegularityTheoremORCSLPGF =
  mkNSBroadTubeConditionalRegularityTheoremORCSLPGF
    "Record the final broad-tube conditional regularity composite with an explicit BKM/Serrin final-assembly ledger."
    refl
    "Compose nondegenerate gradient, vorticity coverage, Serrin exponent discharge, and TheoremG/Q2/GD1 conditional inputs into the final broad-tube regularity route."
    refl
    "Create only NSBroadTubeConditionalRegularityTheoremReceipt.agda."
    refl
    "broad-tube gradient/vorticity/serrin/Serrin-BKM nodes + final BKM/Serrin contradiction ledger + conditional hard lemmas + conditional standard bridge"
    refl
    "route: nondegenerate gradient -> vorticity coverage -> Serrin exponent discharge -> coarea -> Serrin lift -> BKM bridge -> composite -> final BKM/Serrin assembly -> conditional regularity socket"
    refl
    "construct BKM/Serrin final-assembly shape, record TheoremG/Q2/GD1 conditional inputs, and register L8L4 insufficiency plus int ||omega||_infty dt requirement."
    refl
    "promotionGateSatisfied=false; unconditionalClayNS=false; hard lemmas and standard bridge are conditional"
    refl
    "final assembly remains conditional-only; no promoted Clay route is introduced here."
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

    routeLedger :
      List NSBroadTubeConditionalRegularityTheoremRouteRow

    routeLedgerAreCanonical :
      routeLedger ≡
      canonicalNSBroadTubeConditionalRegularityTheoremRouteLedger

    routeLedgerText :
      List String

    routeLedgerTextAreCanonical :
      routeLedgerText ≡
      canonicalNSBroadTubeConditionalRegularityTheoremRouteLedgerText

    steps :
      List NSBroadTubeConditionalRegularityTheoremStep

    stepsAreCanonical :
      steps ≡ canonicalNSBroadTubeConditionalRegularityTheoremSteps

    hardLemmas :
      List NSBroadTubeConditionalRegularityTheoremHardLemma

    hardLemmasAreCanonical :
      hardLemmas ≡
      canonicalNSBroadTubeConditionalRegularityTheoremHardLemmas

    hardLemmasConditionallyRecordedFlag :
      Bool

    hardLemmasConditionallyRecordedFlagIsTrue :
      hardLemmasConditionallyRecordedFlag ≡ true

    standardBridgeState :
      List NSBroadTubeConditionalRegularityTheoremStandardBridge

    standardBridgeStateIsCanonical :
      standardBridgeState ≡
      canonicalNSBroadTubeConditionalRegularityTheoremStandardBridge

    standardBridgeConditionallyRecordedFlag :
      Bool

    standardBridgeConditionallyRecordedFlagIsTrue :
      standardBridgeConditionallyRecordedFlag ≡ true

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

    theoremGReceipt :
      String

    theoremGReceiptIsCanonical :
      theoremGReceipt ≡ theoremGReceiptModule

    q2Receipt :
      String

    q2ReceiptIsCanonical :
      q2Receipt ≡ q2ReceiptModule

    gd1Receipt :
      String

    gd1ReceiptIsCanonical :
      gd1Receipt ≡ gd1ReceiptModule

    finalBKMSSerrinAssemblyRecorded :
      Bool

    finalBKMSSerrinAssemblyRecordedIsTrue :
      finalBKMSSerrinAssemblyRecorded ≡ true

    bkmCriterionIntegralRequirementRecorded :
      Bool

    bkmCriterionIntegralRequirementRecordedIsTrue :
      bkmCriterionIntegralRequirementRecorded ≡ true

    l84L4InsufficientRecorded :
      Bool

    l84L4InsufficientRecordedIsTrue :
      l84L4InsufficientRecorded ≡ true

    theoremGQ2GD1ChainRecorded :
      Bool

    theoremGQ2GD1ChainRecordedIsTrue :
      theoremGQ2GD1ChainRecorded ≡ true

    standardBridgeRecorded :
      Bool

    standardBridgeRecordedIsTrue :
      standardBridgeRecorded ≡ true

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

    finalAssemblyBlockers :
      List NSBroadTubeConditionalRegularityTheoremFinalAssemblyBlocker

    finalAssemblyBlockersAreCanonical :
      finalAssemblyBlockers ≡
      canonicalNSBroadTubeConditionalRegularityTheoremFinalAssemblyBlockers

    finalAssemblyBlockerText :
      List String

    finalAssemblyBlockerTextAreCanonical :
      finalAssemblyBlockerText ≡
      canonicalNSBroadTubeConditionalRegularityTheoremFinalAssemblyBlockerText

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
    ; routeLedger =
        canonicalNSBroadTubeConditionalRegularityTheoremRouteLedger
    ; routeLedgerAreCanonical =
        refl
    ; routeLedgerText =
        canonicalNSBroadTubeConditionalRegularityTheoremRouteLedgerText
    ; routeLedgerTextAreCanonical =
        refl
    ; steps =
        canonicalNSBroadTubeConditionalRegularityTheoremSteps
    ; stepsAreCanonical =
        refl
    ; hardLemmas =
        canonicalNSBroadTubeConditionalRegularityTheoremHardLemmas
    ; hardLemmasAreCanonical =
        refl
    ; hardLemmasConditionallyRecordedFlag =
        true
    ; hardLemmasConditionallyRecordedFlagIsTrue =
        refl
    ; standardBridgeState =
        canonicalNSBroadTubeConditionalRegularityTheoremStandardBridge
    ; standardBridgeStateIsCanonical =
        refl
    ; standardBridgeConditionallyRecordedFlag =
        true
    ; standardBridgeConditionallyRecordedFlagIsTrue =
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
    ; theoremGReceipt =
        theoremGReceiptModule
    ; theoremGReceiptIsCanonical =
        refl
    ; q2Receipt =
        q2ReceiptModule
    ; q2ReceiptIsCanonical =
        refl
    ; gd1Receipt =
        gd1ReceiptModule
    ; gd1ReceiptIsCanonical =
        refl
    ; finalBKMSSerrinAssemblyRecorded =
        true
    ; finalBKMSSerrinAssemblyRecordedIsTrue =
        refl
    ; bkmCriterionIntegralRequirementRecorded =
        true
    ; bkmCriterionIntegralRequirementRecordedIsTrue =
        refl
    ; l84L4InsufficientRecorded =
        true
    ; l84L4InsufficientRecordedIsTrue =
        refl
    ; theoremGQ2GD1ChainRecorded =
        true
    ; theoremGQ2GD1ChainRecordedIsTrue =
        refl
    ; standardBridgeRecorded =
        true
    ; standardBridgeRecordedIsTrue =
        refl
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
    ; finalAssemblyBlockers =
        canonicalNSBroadTubeConditionalRegularityTheoremFinalAssemblyBlockers
    ; finalAssemblyBlockersAreCanonical =
        refl
    ; finalAssemblyBlockerText =
        canonicalNSBroadTubeConditionalRegularityTheoremFinalAssemblyBlockerText
    ; finalAssemblyBlockerTextAreCanonical =
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
