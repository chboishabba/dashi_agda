module DASHI.Foundations.SurrealCompactificationProofTermIndex where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.SurrealCompactification as SC
import DASHI.Foundations.SurrealCompactificationBalancedTernaryEmbedding as BTE
import DASHI.Foundations.SurrealCompactificationIntake as Intake
import DASHI.Foundations.SurrealCompactificationOrderedQQBridge as OrderedQQ
import DASHI.Foundations.SurrealCompactificationQQCarrier as QQC
import DASHI.Foundations.SurrealCompactificationRationalBridge as RationalBridge
import DASHI.Foundations.SurrealCompactificationTailBoundBridge as TailBridge

------------------------------------------------------------------------
-- Normalized payload vocabulary.

data ProofTermPayloadShape : Set where
  qqCarrierPayload :
    ProofTermPayloadShape

  balancedEmbeddingPayload :
    ProofTermPayloadShape

  antitoneGaugePayload :
    ProofTermPayloadShape

  kappaTailPayload :
    ProofTermPayloadShape

canonicalPayloadShapes : List ProofTermPayloadShape
canonicalPayloadShapes =
  qqCarrierPayload
  ∷ balancedEmbeddingPayload
  ∷ antitoneGaugePayload
  ∷ kappaTailPayload
  ∷ []

canonicalPayloadVariables : List Intake.BridgeVariable
canonicalPayloadVariables =
  Intake.depthM
  ∷ Intake.depthN
  ∷ Intake.truncationDepthK
  ∷ Intake.kappaTolerance
  ∷ Intake.tailStartN
  ∷ []

data RepoModuleAnchor : Set where
  surrealCompactificationModule :
    RepoModuleAnchor

  surrealCompactificationIntakeModule :
    RepoModuleAnchor

  surrealCompactificationQQCarrierModule :
    RepoModuleAnchor

  surrealCompactificationBalancedTernaryEmbeddingModule :
    RepoModuleAnchor

  surrealCompactificationRationalBridgeModule :
    RepoModuleAnchor

  surrealCompactificationOrderedQQBridgeModule :
    RepoModuleAnchor

  surrealCompactificationTailBoundBridgeModule :
    RepoModuleAnchor

data RepoIdentifierAnchor : Set where
  qqCarrierAuthorityGateIdentifier :
    RepoIdentifierAnchor

  qqCarrierShapeIdentifier :
    RepoIdentifierAnchor

  boundedQQCarrierSurfaceIdentifier :
    RepoIdentifierAnchor

  thirdPowerGaugeIdentifier :
    RepoIdentifierAnchor

  gaugeAntitoneIdentifier :
    RepoIdentifierAnchor

  orderedQQBridgeSurfaceIdentifier :
    RepoIdentifierAnchor

  balancedTernaryEmbeddingShapeReceiptIdentifier :
    RepoIdentifierAnchor

  tritToQQIdentifier :
    RepoIdentifierAnchor

  threeMinusNIdentifier :
    RepoIdentifierAnchor

  embedTowerIdentifier :
    RepoIdentifierAnchor

  balancedTernaryEmbeddingIntakeIdentifier :
    RepoIdentifierAnchor

  balancedTernaryEmbedDigitIdentifier :
    RepoIdentifierAnchor

  finiteTritTowerSymbolicRationalBridgeIdentifier :
    RepoIdentifierAnchor

  orderedQQAntitoneDependencyIdentifier :
    RepoIdentifierAnchor

  antitoneGaugeLemmaIntakeIdentifier :
    RepoIdentifierAnchor

  symbolicThreeMinusNGaugeIntakeIdentifier :
    RepoIdentifierAnchor

  truncationKappaIntakeIdentifier :
    RepoIdentifierAnchor

  kappaTailBoundLawShapeIdentifier :
    RepoIdentifierAnchor

  compactificationTailBoundBridgeSurfaceIdentifier :
    RepoIdentifierAnchor

record ProofTermIndexRow (m n k : Nat) : Set₁ where
  field
    payloadShape :
      ProofTermPayloadShape

    payloadLabel :
      String

    owningModule :
      RepoModuleAnchor

    primaryIdentifier :
      RepoIdentifierAnchor

    supportIdentifiers :
      List RepoIdentifierAnchor

    variables :
      List Intake.BridgeVariable

    checkStatus :
      Intake.IntakeCheckStatus

    authorityRequired :
      Bool

    authorityRequiredIsTrue :
      authorityRequired ≡ true

    constructedHere :
      Bool

    constructedHereIsFalse :
      constructedHere ≡ false

    promotedHere :
      Bool

    promotedHereIsFalse :
      promotedHere ≡ false

open ProofTermIndexRow public

qqCarrierIndexRow :
  (m n k : Nat) →
  ProofTermIndexRow m n k
qqCarrierIndexRow m n k =
  record
    { payloadShape =
        qqCarrierPayload
    ; payloadLabel =
        "QQCarrier"
    ; owningModule =
        surrealCompactificationQQCarrierModule
    ; primaryIdentifier =
        boundedQQCarrierSurfaceIdentifier
    ; supportIdentifiers =
        qqCarrierShapeIdentifier
        ∷ thirdPowerGaugeIdentifier
        ∷ gaugeAntitoneIdentifier
        ∷ qqCarrierAuthorityGateIdentifier
        ∷ orderedQQBridgeSurfaceIdentifier
        ∷ finiteTritTowerSymbolicRationalBridgeIdentifier
        ∷ []
    ; variables =
        canonicalPayloadVariables
    ; checkStatus =
        Intake.externalAuthorityRequiredFailClosed
    ; authorityRequired =
        true
    ; authorityRequiredIsTrue =
        refl
    ; constructedHere =
        false
    ; constructedHereIsFalse =
        refl
    ; promotedHere =
        false
    ; promotedHereIsFalse =
        refl
    }

balancedEmbeddingIndexRow :
  (m n k : Nat) →
  ProofTermIndexRow m n k
balancedEmbeddingIndexRow m n k =
  record
    { payloadShape =
        balancedEmbeddingPayload
    ; payloadLabel =
        "balanced embedding"
    ; owningModule =
        surrealCompactificationBalancedTernaryEmbeddingModule
    ; primaryIdentifier =
        balancedTernaryEmbeddingShapeReceiptIdentifier
    ; supportIdentifiers =
        tritToQQIdentifier
        ∷ threeMinusNIdentifier
        ∷ embedTowerIdentifier
        ∷ balancedTernaryEmbeddingIntakeIdentifier
        ∷ balancedTernaryEmbedDigitIdentifier
        ∷ finiteTritTowerSymbolicRationalBridgeIdentifier
        ∷ []
    ; variables =
        Intake.depthN
        ∷ []
    ; checkStatus =
        Intake.checkedInternal
    ; authorityRequired =
        true
    ; authorityRequiredIsTrue =
        refl
    ; constructedHere =
        false
    ; constructedHereIsFalse =
        refl
    ; promotedHere =
        false
    ; promotedHereIsFalse =
        refl
    }

antitoneGaugeIndexRow :
  (m n k : Nat) →
  ProofTermIndexRow m n k
antitoneGaugeIndexRow m n k =
  record
    { payloadShape =
        antitoneGaugePayload
    ; payloadLabel =
        "antitone/gauge"
    ; owningModule =
        surrealCompactificationOrderedQQBridgeModule
    ; primaryIdentifier =
        orderedQQAntitoneDependencyIdentifier
    ; supportIdentifiers =
        antitoneGaugeLemmaIntakeIdentifier
        ∷ symbolicThreeMinusNGaugeIntakeIdentifier
        ∷ qqCarrierShapeIdentifier
        ∷ []
    ; variables =
        Intake.depthM
        ∷ Intake.depthN
        ∷ []
    ; checkStatus =
        Intake.externalAuthorityRequiredFailClosed
    ; authorityRequired =
        true
    ; authorityRequiredIsTrue =
        refl
    ; constructedHere =
        false
    ; constructedHereIsFalse =
        refl
    ; promotedHere =
        false
    ; promotedHereIsFalse =
        refl
    }

kappaTailIndexRow :
  (m n k : Nat) →
  ProofTermIndexRow m n k
kappaTailIndexRow m n k =
  record
    { payloadShape =
        kappaTailPayload
    ; payloadLabel =
        "kappa/tail"
    ; owningModule =
        surrealCompactificationTailBoundBridgeModule
    ; primaryIdentifier =
        kappaTailBoundLawShapeIdentifier
    ; supportIdentifiers =
        truncationKappaIntakeIdentifier
        ∷ compactificationTailBoundBridgeSurfaceIdentifier
        ∷ symbolicThreeMinusNGaugeIntakeIdentifier
        ∷ []
    ; variables =
        Intake.truncationDepthK
        ∷ Intake.kappaTolerance
        ∷ Intake.tailStartN
        ∷ []
    ; checkStatus =
        Intake.externalAuthorityRequiredFailClosed
    ; authorityRequired =
        true
    ; authorityRequiredIsTrue =
        refl
    ; constructedHere =
        false
    ; constructedHereIsFalse =
        refl
    ; promotedHere =
        false
    ; promotedHereIsFalse =
        refl
    }

canonicalProofTermIndexRows :
  (m n k : Nat) →
  List (ProofTermIndexRow m n k)
canonicalProofTermIndexRows m n k =
  qqCarrierIndexRow m n k
  ∷ balancedEmbeddingIndexRow m n k
  ∷ antitoneGaugeIndexRow m n k
  ∷ kappaTailIndexRow m n k
  ∷ []

------------------------------------------------------------------------
-- Checked mapping to existing proof-term surfaces.

record ProofTermIndexSurface (m n k : Nat) : Set₁ where
  field
    payloadShapes :
      List ProofTermPayloadShape

    payloadShapesAreCanonical :
      payloadShapes ≡ canonicalPayloadShapes

    payloadVariables :
      List Intake.BridgeVariable

    payloadVariablesAreCanonical :
      payloadVariables ≡ canonicalPayloadVariables

    indexRows :
      List (ProofTermIndexRow m n k)

    indexRowsAreCanonical :
      indexRows ≡ canonicalProofTermIndexRows m n k

    qqCarrierGate :
      Intake.CarrierAuthorityGate

    qqCarrierGateIsCanonical :
      qqCarrierGate ≡ Intake.qqCarrierAuthorityGate

    qqCarrierSurface :
      QQC.QQCarrierSurface

    qqCarrierSurfaceIsCanonical :
      qqCarrierSurface ≡ QQC.canonicalQQCarrierSurface

    orderedQQBridge :
      OrderedQQ.OrderedQQBridgeSurface

    orderedQQBridgeIsCanonical :
      orderedQQBridge ≡ OrderedQQ.canonicalOrderedQQBridgeSurface

    rationalBridge :
      RationalBridge.FiniteTritTowerSymbolicRationalBridge

    rationalBridgeIsCanonical :
      rationalBridge
      ≡
      RationalBridge.canonicalFiniteTritTowerSymbolicRationalBridge

    balancedEmbeddingIntake :
      Intake.BalancedTernaryEmbeddingIntake

    balancedEmbeddingIntakeIsCanonical :
      balancedEmbeddingIntake
      ≡
      Intake.canonicalBalancedTernaryEmbeddingIntake

    balancedEmbeddingShape :
      BTE.BalancedTernaryEmbeddingShapeReceipt

    balancedEmbeddingShapeIsCanonical :
      balancedEmbeddingShape
      ≡
      BTE.canonicalBalancedTernaryEmbeddingShapeReceipt

    antitoneDependency :
      OrderedQQ.OrderedQQAntitoneDependency m n

    antitoneDependencyIsCanonical :
      antitoneDependency ≡ OrderedQQ.canonicalOrderedQQAntitoneDependency m n

    antitoneIntake :
      Intake.AntitoneGaugeLemmaIntake m n

    antitoneIntakeIsCanonical :
      antitoneIntake ≡ Intake.canonicalAntitoneGaugeLemmaIntake m n

    gaugeIntake :
      Intake.SymbolicThreeMinusNGaugeIntake n

    gaugeIntakeIsCanonical :
      gaugeIntake ≡ Intake.canonicalSymbolicThreeMinusNGaugeIntake n

    truncationKappaIntake :
      Intake.TruncationKappaIntake k

    truncationKappaIntakeIsCanonical :
      truncationKappaIntake ≡ Intake.canonicalTruncationKappaIntake k

    kappaTailLaw :
      TailBridge.KappaTailBoundLawShape n k

    kappaTailLawIsCanonical :
      kappaTailLaw ≡ TailBridge.kappaTailBound-law n k

    tailBridgeSurface :
      TailBridge.CompactificationTailBoundBridgeSurface n k

    tailBridgeSurfaceIsCanonical :
      tailBridgeSurface ≡ TailBridge.canonicalCompactificationTailBoundBridgeSurface n k

    noPromotionFlags :
      Intake.NoPromotionFlags

    noPromotionFlagsAreCanonical :
      noPromotionFlags ≡ Intake.canonicalNoPromotionFlags

    allAuthorityGatesFailClosed :
      Bool

    allAuthorityGatesFailClosedIsTrue :
      allAuthorityGatesFailClosed ≡ true

    anyPayloadProofPromotedHere :
      Bool

    anyPayloadProofPromotedHereIsFalse :
      anyPayloadProofPromotedHere ≡ false

open ProofTermIndexSurface public

canonicalProofTermIndexSurface :
  (m n k : Nat) →
  ProofTermIndexSurface m n k
canonicalProofTermIndexSurface m n k =
  record
    { payloadShapes =
        canonicalPayloadShapes
    ; payloadShapesAreCanonical =
        refl
    ; payloadVariables =
        canonicalPayloadVariables
    ; payloadVariablesAreCanonical =
        refl
    ; indexRows =
        canonicalProofTermIndexRows m n k
    ; indexRowsAreCanonical =
        refl
    ; qqCarrierGate =
        Intake.qqCarrierAuthorityGate
    ; qqCarrierGateIsCanonical =
        refl
    ; qqCarrierSurface =
        QQC.canonicalQQCarrierSurface
    ; qqCarrierSurfaceIsCanonical =
        refl
    ; orderedQQBridge =
        OrderedQQ.canonicalOrderedQQBridgeSurface
    ; orderedQQBridgeIsCanonical =
        refl
    ; rationalBridge =
        RationalBridge.canonicalFiniteTritTowerSymbolicRationalBridge
    ; rationalBridgeIsCanonical =
        refl
    ; balancedEmbeddingIntake =
        Intake.canonicalBalancedTernaryEmbeddingIntake
    ; balancedEmbeddingIntakeIsCanonical =
        refl
    ; balancedEmbeddingShape =
        BTE.canonicalBalancedTernaryEmbeddingShapeReceipt
    ; balancedEmbeddingShapeIsCanonical =
        refl
    ; antitoneDependency =
        OrderedQQ.canonicalOrderedQQAntitoneDependency m n
    ; antitoneDependencyIsCanonical =
        refl
    ; antitoneIntake =
        Intake.canonicalAntitoneGaugeLemmaIntake m n
    ; antitoneIntakeIsCanonical =
        refl
    ; gaugeIntake =
        Intake.canonicalSymbolicThreeMinusNGaugeIntake n
    ; gaugeIntakeIsCanonical =
        refl
    ; truncationKappaIntake =
        Intake.canonicalTruncationKappaIntake k
    ; truncationKappaIntakeIsCanonical =
        refl
    ; kappaTailLaw =
        TailBridge.kappaTailBound-law n k
    ; kappaTailLawIsCanonical =
        refl
    ; tailBridgeSurface =
        TailBridge.canonicalCompactificationTailBoundBridgeSurface n k
    ; tailBridgeSurfaceIsCanonical =
        refl
    ; noPromotionFlags =
        Intake.canonicalNoPromotionFlags
    ; noPromotionFlagsAreCanonical =
        refl
    ; allAuthorityGatesFailClosed =
        true
    ; allAuthorityGatesFailClosedIsTrue =
        refl
    ; anyPayloadProofPromotedHere =
        false
    ; anyPayloadProofPromotedHereIsFalse =
        refl
    }

canonicalProofTermIndexFailClosed :
  (m n k : Nat) →
  allAuthorityGatesFailClosed (canonicalProofTermIndexSurface m n k) ≡ true
canonicalProofTermIndexFailClosed m n k =
  refl

canonicalProofTermIndexDoesNotPromote :
  (m n k : Nat) →
  anyPayloadProofPromotedHere (canonicalProofTermIndexSurface m n k) ≡ false
canonicalProofTermIndexDoesNotPromote m n k =
  refl

canonicalProofTermIndexKappaTailFailsClosed :
  (m n k : Nat) →
  TailBridge.kappaAnalyticProofStatus
    (kappaTailLaw (canonicalProofTermIndexSurface m n k))
  ≡
  Intake.externalAuthorityRequiredFailClosed
canonicalProofTermIndexKappaTailFailsClosed m n k =
  refl

canonicalProofTermIndexAntitoneDoesNotPromote :
  (m n k : Nat) →
  OrderedQQ.antitoneLemmaPromotedHere
    (antitoneDependency (canonicalProofTermIndexSurface m n k))
  ≡
  false
canonicalProofTermIndexAntitoneDoesNotPromote m n k =
  refl

canonicalProofTermIndexQQCarrierDoesNotPromote :
  (m n k : Nat) →
  QQC.completeQQClaimed
    (QQC.failClosedFlags
      (qqCarrierSurface (canonicalProofTermIndexSurface m n k)))
  ≡
  false
canonicalProofTermIndexQQCarrierDoesNotPromote m n k =
  refl

canonicalProofTermIndexQQCarrierExternalAuthorityFalse :
  (m n k : Nat) →
  QQC.externalQQCarrierAuthorityAccepted
    (QQC.failClosedFlags
      (qqCarrierSurface (canonicalProofTermIndexSurface m n k)))
  ≡
  false
canonicalProofTermIndexQQCarrierExternalAuthorityFalse m n k =
  refl

canonicalProofTermIndexBalancedEmbeddingDigit :
  (m n k : Nat) →
  Intake.digitEmbedding
    (balancedEmbeddingIntake (canonicalProofTermIndexSurface m n k))
  ≡
  Intake.balancedTernaryEmbedDigit
canonicalProofTermIndexBalancedEmbeddingDigit m n k =
  refl

canonicalProofTermIndexBalancedEmbeddingIsStructuralOnly :
  (m n k : Nat) →
  BTE.intervalReceiptsAreStructuralOnly
    (balancedEmbeddingShape (canonicalProofTermIndexSurface m n k))
  ≡
  true
canonicalProofTermIndexBalancedEmbeddingIsStructuralOnly m n k =
  refl

canonicalProofTermIndexBalancedEmbeddingDoesNotPromoteInterval :
  (m n k : Nat) →
  BTE.analyticIntervalProofPromotedHere
    (balancedEmbeddingShape (canonicalProofTermIndexSurface m n k))
  ≡
  false
canonicalProofTermIndexBalancedEmbeddingDoesNotPromoteInterval m n k =
  refl
