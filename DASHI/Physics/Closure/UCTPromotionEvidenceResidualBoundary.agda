module DASHI.Physics.Closure.UCTPromotionEvidenceResidualBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Paper 8 UCT promotion-evidence residual boundary.
--
-- This builtin-only receipt records the live evidence wall:
--
--   UCT.1 overlap residual PDE
--   UCT.2 ellipticity/parabolicity witness
--   UCT.3 Carleman / unique-continuation intake
--   UCT.4 cross-term nullity
--
-- and routes the downstream consumers:
--
--   UCT.5 modulo-null linearity
--   UCT.6 four-point cancellation
--   UCT.7 parallelogram
--   UCT.8 Jordan-von Neumann recovery.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Recorded downstream consumer anchors.

moduloNullLinearityConsumer : String
moduloNullLinearityConsumer =
  "UnificationGluingModuloNullLinearityCompositeBoundary"

fourPointCancellationConsumer : String
fourPointCancellationConsumer =
  "UnificationFourPointCancellationFromCrossTermNullityBoundary"

parallelogramConsumer : String
parallelogramConsumer =
  "UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary"

jordanVonNeumannAdapterConsumer : String
jordanVonNeumannAdapterConsumer =
  "UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary"

canonicalModuloNullTerminalPromotionFalse : String
canonicalModuloNullTerminalPromotionFalse =
  "canonicalModuloNullTerminalPromotionFalse"

canonicalModuloNullClayPromotionFalse : String
canonicalModuloNullClayPromotionFalse =
  "canonicalModuloNullClayPromotionFalse"

canonicalRouteFourPointCancellationStillOpen : String
canonicalRouteFourPointCancellationStillOpen =
  "canonicalRouteFourPointCancellationStillOpen"

canonicalRouteParallelogramStillOpen : String
canonicalRouteParallelogramStillOpen =
  "canonicalRouteParallelogramStillOpen"

canonicalRouteTerminalPromotionFalse : String
canonicalRouteTerminalPromotionFalse =
  "canonicalRouteTerminalPromotionFalse"

provedStillFalse : String
provedStillFalse =
  "provedStillFalse"

record UCTPromotionEvidenceImportedConsumers : Set where
  field
    moduloNullLinearityConsumerRecorded :
      String
    fourPointCancellationConsumerRecorded :
      String
    parallelogramConsumerRecorded :
      String
    jordanVonNeumannAdapterConsumerRecorded :
      String
    moduloNullTerminalPromotionFalseRecorded :
      String
    moduloNullClayPromotionFalseRecorded :
      String
    fourPointCancellationStillOpenRecorded :
      String
    parallelogramStillOpenRecorded :
      String
    routeTerminalPromotionFalseRecorded :
      String
    jvnProvedStillFalseRecorded :
      String

open UCTPromotionEvidenceImportedConsumers public

canonicalUCTPromotionEvidenceImportedConsumers :
  UCTPromotionEvidenceImportedConsumers
canonicalUCTPromotionEvidenceImportedConsumers =
  record
    { moduloNullLinearityConsumerRecorded =
        moduloNullLinearityConsumer
    ; fourPointCancellationConsumerRecorded =
        fourPointCancellationConsumer
    ; parallelogramConsumerRecorded =
        parallelogramConsumer
    ; jordanVonNeumannAdapterConsumerRecorded =
        jordanVonNeumannAdapterConsumer
    ; moduloNullTerminalPromotionFalseRecorded =
        canonicalModuloNullTerminalPromotionFalse
    ; moduloNullClayPromotionFalseRecorded =
        canonicalModuloNullClayPromotionFalse
    ; fourPointCancellationStillOpenRecorded =
        canonicalRouteFourPointCancellationStillOpen
    ; parallelogramStillOpenRecorded =
        canonicalRouteParallelogramStillOpen
    ; routeTerminalPromotionFalseRecorded =
        canonicalRouteTerminalPromotionFalse
    ; jvnProvedStillFalseRecorded =
        provedStillFalse
    }

------------------------------------------------------------------------
-- UCT dependency chain.

data UCTPromotionEvidenceStage : Set where
  uct1OverlapResidualPDE :
    UCTPromotionEvidenceStage
  uct2EllipticityParabolicityWitness :
    UCTPromotionEvidenceStage
  uct3CarlemanUniqueContinuationIntake :
    UCTPromotionEvidenceStage
  uct4CrossTermNullity :
    UCTPromotionEvidenceStage
  uct5ModuloNullLinearity :
    UCTPromotionEvidenceStage
  uct6FourPointCancellation :
    UCTPromotionEvidenceStage
  uct7Parallelogram :
    UCTPromotionEvidenceStage
  uct8JordanVonNeumann :
    UCTPromotionEvidenceStage

data UCTPromotionEvidenceStatus : Set where
  evidenceRecorded :
    UCTPromotionEvidenceStatus
  livePromotionEvidenceWall :
    UCTPromotionEvidenceStatus
  downstreamConsumerLocked :
    UCTPromotionEvidenceStatus
  terminalPromotionHeld :
    UCTPromotionEvidenceStatus

canonicalUCTPromotionEvidenceStatus :
  UCTPromotionEvidenceStage →
  UCTPromotionEvidenceStatus
canonicalUCTPromotionEvidenceStatus uct1OverlapResidualPDE =
  evidenceRecorded
canonicalUCTPromotionEvidenceStatus uct2EllipticityParabolicityWitness =
  evidenceRecorded
canonicalUCTPromotionEvidenceStatus uct3CarlemanUniqueContinuationIntake =
  evidenceRecorded
canonicalUCTPromotionEvidenceStatus uct4CrossTermNullity =
  livePromotionEvidenceWall
canonicalUCTPromotionEvidenceStatus uct5ModuloNullLinearity =
  downstreamConsumerLocked
canonicalUCTPromotionEvidenceStatus uct6FourPointCancellation =
  downstreamConsumerLocked
canonicalUCTPromotionEvidenceStatus uct7Parallelogram =
  downstreamConsumerLocked
canonicalUCTPromotionEvidenceStatus uct8JordanVonNeumann =
  terminalPromotionHeld

data UCTPromotionEvidenceBlocker : Set where
  missingOverlapResidualPDETheorem :
    UCTPromotionEvidenceBlocker
  missingEllipticityParabolicityClassification :
    UCTPromotionEvidenceBlocker
  missingCarlemanUniqueContinuationTheorem :
    UCTPromotionEvidenceBlocker
  missingCrossTermNullityTheorem :
    UCTPromotionEvidenceBlocker
  waitingOnCrossTermNullityForModuloNullLinearity :
    UCTPromotionEvidenceBlocker
  waitingOnModuloNullLinearityForFourPointCancellation :
    UCTPromotionEvidenceBlocker
  waitingOnFourPointCancellationForParallelogram :
    UCTPromotionEvidenceBlocker
  waitingOnParallelogramForJordanVonNeumann :
    UCTPromotionEvidenceBlocker

canonicalUCTPromotionEvidenceBlocker :
  UCTPromotionEvidenceStage →
  UCTPromotionEvidenceBlocker
canonicalUCTPromotionEvidenceBlocker uct1OverlapResidualPDE =
  missingOverlapResidualPDETheorem
canonicalUCTPromotionEvidenceBlocker uct2EllipticityParabolicityWitness =
  missingEllipticityParabolicityClassification
canonicalUCTPromotionEvidenceBlocker uct3CarlemanUniqueContinuationIntake =
  missingCarlemanUniqueContinuationTheorem
canonicalUCTPromotionEvidenceBlocker uct4CrossTermNullity =
  missingCrossTermNullityTheorem
canonicalUCTPromotionEvidenceBlocker uct5ModuloNullLinearity =
  waitingOnCrossTermNullityForModuloNullLinearity
canonicalUCTPromotionEvidenceBlocker uct6FourPointCancellation =
  waitingOnModuloNullLinearityForFourPointCancellation
canonicalUCTPromotionEvidenceBlocker uct7Parallelogram =
  waitingOnFourPointCancellationForParallelogram
canonicalUCTPromotionEvidenceBlocker uct8JordanVonNeumann =
  waitingOnParallelogramForJordanVonNeumann

record UCTPromotionEvidenceRow : Set where
  field
    stage :
      UCTPromotionEvidenceStage
    status :
      UCTPromotionEvidenceStatus
    statusIsCanonical :
      status ≡ canonicalUCTPromotionEvidenceStatus stage
    blocker :
      UCTPromotionEvidenceBlocker
    blockerIsCanonical :
      blocker ≡ canonicalUCTPromotionEvidenceBlocker stage
    dependency :
      String
    evidenceSocket :
      String
    theoremOrPromotionProvedHere :
      Bool
    theoremOrPromotionProvedHereIsFalse :
      theoremOrPromotionProvedHere ≡ false

open UCTPromotionEvidenceRow public

mkUCTPromotionEvidenceRow :
  UCTPromotionEvidenceStage →
  String →
  String →
  UCTPromotionEvidenceRow
mkUCTPromotionEvidenceRow stage dependency evidenceSocket =
  record
    { stage =
        stage
    ; status =
        canonicalUCTPromotionEvidenceStatus stage
    ; statusIsCanonical =
        refl
    ; blocker =
        canonicalUCTPromotionEvidenceBlocker stage
    ; blockerIsCanonical =
        refl
    ; dependency =
        dependency
    ; evidenceSocket =
        evidenceSocket
    ; theoremOrPromotionProvedHere =
        false
    ; theoremOrPromotionProvedHereIsFalse =
        refl
    }

canonicalUCTPromotionEvidenceRows :
  List UCTPromotionEvidenceRow
canonicalUCTPromotionEvidenceRows =
  mkUCTPromotionEvidenceRow
    uct1OverlapResidualPDE
    "UCT.1 records the overlap residual PDE before any analytic promotion"
    "uct1ResidualPDESpecificationRecorded"
  ∷ mkUCTPromotionEvidenceRow
    uct2EllipticityParabolicityWitness
    "UCT.2 consumes UCT.1 and records the ellipticity/parabolicity witness"
    "uct2EllipticityOrParabolicityClassRecorded"
  ∷ mkUCTPromotionEvidenceRow
    uct3CarlemanUniqueContinuationIntake
    "UCT.3 consumes UCT.1 and UCT.2 and records Carleman/unique-continuation intake"
    "uct3CarlemanUniqueContinuationRecorded"
  ∷ mkUCTPromotionEvidenceRow
    uct4CrossTermNullity
    "UCT.4 consumes UCT.1-UCT.3 and remains the live promotion evidence wall"
    "uct4CrossTermNullityLivePromotionEvidenceWall"
  ∷ mkUCTPromotionEvidenceRow
    uct5ModuloNullLinearity
    "UCT.5 consumes UCT.4 through modulo-null gluing linearity"
    "moduloNullLinearityConsumer"
  ∷ mkUCTPromotionEvidenceRow
    uct6FourPointCancellation
    "UCT.6 consumes UCT.4 and UCT.5 through four-point cancellation"
    "fourPointCancellationConsumer"
  ∷ mkUCTPromotionEvidenceRow
    uct7Parallelogram
    "UCT.7 consumes UCT.6 through the parallelogram socket"
    "parallelogramConsumer"
  ∷ mkUCTPromotionEvidenceRow
    uct8JordanVonNeumann
    "UCT.8 consumes UCT.7 through the Jordan-von Neumann recovery socket"
    "jordanVonNeumannAdapterConsumer"
  ∷ []

uctPromotionEvidenceRowCount : Nat
uctPromotionEvidenceRowCount =
  listLength canonicalUCTPromotionEvidenceRows

uctPromotionEvidenceRowCountIs8 :
  uctPromotionEvidenceRowCount ≡ 8
uctPromotionEvidenceRowCountIs8 =
  refl

------------------------------------------------------------------------
-- Evidence recording and fail-closed promotion gates.

uct1ResidualPDESpecificationRecorded : Bool
uct1ResidualPDESpecificationRecorded =
  true

uct2EllipticityOrParabolicityClassRecorded : Bool
uct2EllipticityOrParabolicityClassRecorded =
  true

uct3CarlemanUniqueContinuationRecorded : Bool
uct3CarlemanUniqueContinuationRecorded =
  true

uct4CrossTermNullityLivePromotionEvidenceWall : Bool
uct4CrossTermNullityLivePromotionEvidenceWall =
  true

uct1OverlapResidualPDETheoremProved : Bool
uct1OverlapResidualPDETheoremProved =
  false

uct2EllipticityParabolicityTheoremProved : Bool
uct2EllipticityParabolicityTheoremProved =
  false

uct3CarlemanUniqueContinuationTheoremProved : Bool
uct3CarlemanUniqueContinuationTheoremProved =
  false

uct4CrossTermNullityTheoremProved : Bool
uct4CrossTermNullityTheoremProved =
  false

uctPromoted : Bool
uctPromoted =
  false

terminalPromoted : Bool
terminalPromoted =
  false

clayEligible : Bool
clayEligible =
  false

record UCTPromotionEvidenceResidualBoundary : Set where
  field
    importedConsumers :
      UCTPromotionEvidenceImportedConsumers
    evidenceRows :
      List UCTPromotionEvidenceRow
    evidenceRowCount :
      Nat
    evidenceRowCountIs8 :
      evidenceRowCount ≡ 8
    evidenceRowCountMatchesRows :
      evidenceRowCount ≡ listLength evidenceRows
    uct1Recorded :
      uct1ResidualPDESpecificationRecorded ≡ true
    uct2Recorded :
      uct2EllipticityOrParabolicityClassRecorded ≡ true
    uct3Recorded :
      uct3CarlemanUniqueContinuationRecorded ≡ true
    uct4WallRecorded :
      uct4CrossTermNullityLivePromotionEvidenceWall ≡ true
    uct1TheoremStillOpen :
      uct1OverlapResidualPDETheoremProved ≡ false
    uct2TheoremStillOpen :
      uct2EllipticityParabolicityTheoremProved ≡ false
    uct3TheoremStillOpen :
      uct3CarlemanUniqueContinuationTheoremProved ≡ false
    uct4TheoremStillOpen :
      uct4CrossTermNullityTheoremProved ≡ false
    uctPromotedIsFalse :
      uctPromoted ≡ false
    terminalPromotedIsFalse :
      terminalPromoted ≡ false
    clayEligibleIsFalse :
      clayEligible ≡ false
    notes :
      List String

open UCTPromotionEvidenceResidualBoundary public

canonicalUCTPromotionEvidenceResidualBoundary :
  UCTPromotionEvidenceResidualBoundary
canonicalUCTPromotionEvidenceResidualBoundary =
  record
    { importedConsumers =
        canonicalUCTPromotionEvidenceImportedConsumers
    ; evidenceRows =
        canonicalUCTPromotionEvidenceRows
    ; evidenceRowCount =
        8
    ; evidenceRowCountIs8 =
        refl
    ; evidenceRowCountMatchesRows =
        refl
    ; uct1Recorded =
        refl
    ; uct2Recorded =
        refl
    ; uct3Recorded =
        refl
    ; uct4WallRecorded =
        refl
    ; uct1TheoremStillOpen =
        refl
    ; uct2TheoremStillOpen =
        refl
    ; uct3TheoremStillOpen =
        refl
    ; uct4TheoremStillOpen =
        refl
    ; uctPromotedIsFalse =
        refl
    ; terminalPromotedIsFalse =
        refl
    ; clayEligibleIsFalse =
        refl
    ; notes =
        "O: Paper 8 UCT promotion-evidence residual boundary."
      ∷ "R: UCT.1-UCT.4 record overlap residual PDE, ellipticity/parabolicity witness, Carleman/unique-continuation intake, and cross-term nullity as the live wall."
      ∷ "C: UCT.5-UCT.8 consume the wall through modulo-null linearity, four-point cancellation, parallelogram, and Jordan-von Neumann recovery."
      ∷ "S: The receipt is fail-closed: analytic theorem claims remain false."
      ∷ "L: Dependency order is UCT.1 -> UCT.2 -> UCT.3 -> UCT.4 -> UCT.5 -> UCT.6 -> UCT.7 -> UCT.8."
      ∷ "P: Downstream consumers are sockets only, not promotion authority."
      ∷ "G: uctPromoted, terminalPromoted, and clayEligible are false."
      ∷ "F: Future work is the actual UCT.1-UCT.4 analytic proof package."
      ∷ []
    }

canonicalUCTPromotionEvidenceRowCountIs8 :
  evidenceRowCount canonicalUCTPromotionEvidenceResidualBoundary ≡ 8
canonicalUCTPromotionEvidenceRowCountIs8 =
  refl

canonicalUCT1ResidualPDESpecificationRecorded :
  uct1ResidualPDESpecificationRecorded ≡ true
canonicalUCT1ResidualPDESpecificationRecorded =
  refl

canonicalUCT2EllipticityOrParabolicityClassRecorded :
  uct2EllipticityOrParabolicityClassRecorded ≡ true
canonicalUCT2EllipticityOrParabolicityClassRecorded =
  refl

canonicalUCT3CarlemanUniqueContinuationRecorded :
  uct3CarlemanUniqueContinuationRecorded ≡ true
canonicalUCT3CarlemanUniqueContinuationRecorded =
  refl

canonicalUCT4CrossTermNullityLivePromotionEvidenceWall :
  uct4CrossTermNullityLivePromotionEvidenceWall ≡ true
canonicalUCT4CrossTermNullityLivePromotionEvidenceWall =
  refl

canonicalUCT1OverlapResidualPDETheoremStillOpen :
  uct1OverlapResidualPDETheoremProved ≡ false
canonicalUCT1OverlapResidualPDETheoremStillOpen =
  refl

canonicalUCT2EllipticityParabolicityTheoremStillOpen :
  uct2EllipticityParabolicityTheoremProved ≡ false
canonicalUCT2EllipticityParabolicityTheoremStillOpen =
  refl

canonicalUCT3CarlemanUniqueContinuationTheoremStillOpen :
  uct3CarlemanUniqueContinuationTheoremProved ≡ false
canonicalUCT3CarlemanUniqueContinuationTheoremStillOpen =
  refl

canonicalUCT4CrossTermNullityTheoremStillOpen :
  uct4CrossTermNullityTheoremProved ≡ false
canonicalUCT4CrossTermNullityTheoremStillOpen =
  refl

canonicalUCTPromotedStillFalse :
  uctPromoted ≡ false
canonicalUCTPromotedStillFalse =
  refl

canonicalTerminalPromotedStillFalse :
  terminalPromoted ≡ false
canonicalTerminalPromotedStillFalse =
  refl

canonicalClayEligibleStillFalse :
  clayEligible ≡ false
canonicalClayEligibleStillFalse =
  refl
