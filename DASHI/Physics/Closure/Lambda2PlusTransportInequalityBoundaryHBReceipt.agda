module DASHI.Physics.Closure.Lambda2PlusTransportInequalityBoundaryHBReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Candidate-only receipt surface for the lambda2plus transport inequality
-- shape and the BoundaryHB assembly blockers.
--
-- The transport side records the symbolic shape with nu, C_NS, t1, t2,
-- lambda2+, L2, and L3 tokens.  The BoundaryHB side records the missing
-- KornLevelSet input, the layer-energy lower bound, and the continuity/
-- Harnack steps that would be needed to upgrade an integral estimate to
-- pointwise b0.  No theorem promotion is claimed here.

data Lambda2PlusTransportInequalityStatus : Set where
  lambda2PlusTransportShapeRecordedCandidateOnly :
    Lambda2PlusTransportInequalityStatus

data Lambda2PlusTransportInequalityToken : Set where
  nuToken :
    Lambda2PlusTransportInequalityToken

  cNSToken :
    Lambda2PlusTransportInequalityToken

  t1Token :
    Lambda2PlusTransportInequalityToken

  t2Token :
    Lambda2PlusTransportInequalityToken

  lambda2PlusToken :
    Lambda2PlusTransportInequalityToken

  l2Token :
    Lambda2PlusTransportInequalityToken

  l3Token :
    Lambda2PlusTransportInequalityToken

canonicalLambda2PlusTransportInequalityTokens :
  List Lambda2PlusTransportInequalityToken
canonicalLambda2PlusTransportInequalityTokens =
  nuToken
  ∷ cNSToken
  ∷ t1Token
  ∷ t2Token
  ∷ lambda2PlusToken
  ∷ l2Token
  ∷ l3Token
  ∷ []

data Lambda2PlusTransportInequalityPromotion : Set where

lambda2PlusTransportInequalityPromotionImpossibleHere :
  Lambda2PlusTransportInequalityPromotion →
  ⊥
lambda2PlusTransportInequalityPromotionImpossibleHere ()

lambda2PlusTransportInequalityStatement : String
lambda2PlusTransportInequalityStatement =
  "candidate-only transport inequality shape: nu, C_NS, t1, t2, lambda2+, L2, and L3 terms are recorded, but no theorem promotion is claimed"

data BoundaryHBAssemblyStatus : Set where
  boundaryHBAssemblyBlockedCandidateOnly :
    BoundaryHBAssemblyStatus

data BoundaryHBAssemblyBlocker : Set where
  kornLevelSetMissing :
    BoundaryHBAssemblyBlocker

  layerEnergyLowerBoundMissing :
    BoundaryHBAssemblyBlocker

  continuityMissing :
    BoundaryHBAssemblyBlocker

  harnackMissing :
    BoundaryHBAssemblyBlocker

  integralToPointwiseB0UpgradeMissing :
    BoundaryHBAssemblyBlocker

canonicalBoundaryHBAssemblyBlockers :
  List BoundaryHBAssemblyBlocker
canonicalBoundaryHBAssemblyBlockers =
  kornLevelSetMissing
  ∷ layerEnergyLowerBoundMissing
  ∷ continuityMissing
  ∷ harnackMissing
  ∷ integralToPointwiseB0UpgradeMissing
  ∷ []

data BoundaryHBAssemblyPromotion : Set where

boundaryHBAssemblyPromotionImpossibleHere :
  BoundaryHBAssemblyPromotion →
  ⊥
boundaryHBAssemblyPromotionImpossibleHere ()

boundaryHBAssemblyStatementText : String
boundaryHBAssemblyStatementText =
  "BoundaryHB assembly stays blocked until KornLevelSet, the layer energy lower bound, and continuity/Harnack inputs are supplied so the integral estimate can be upgraded to pointwise b0."

record Lambda2PlusTransportInequalityReceipt : Setω where
  field
    status :
      Lambda2PlusTransportInequalityStatus

    statusIsCanonical :
      status ≡ lambda2PlusTransportShapeRecordedCandidateOnly

    tokens :
      List Lambda2PlusTransportInequalityToken

    tokensAreCanonical :
      tokens ≡ canonicalLambda2PlusTransportInequalityTokens

    transportInequalityStatement :
      String

    transportInequalityStatementIsCanonical :
      transportInequalityStatement ≡ lambda2PlusTransportInequalityStatement

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    promotionFlags :
      List Lambda2PlusTransportInequalityPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

record BoundaryHBAssemblyReceipt : Setω where
  field
    status :
      BoundaryHBAssemblyStatus

    statusIsCanonical :
      status ≡ boundaryHBAssemblyBlockedCandidateOnly

    blockers :
      List BoundaryHBAssemblyBlocker

    blockersAreCanonical :
      blockers ≡ canonicalBoundaryHBAssemblyBlockers

    kornLevelSetRequired :
      Bool

    kornLevelSetRequiredIsTrue :
      kornLevelSetRequired ≡ true

    layerEnergyLowerBoundRequired :
      Bool

    layerEnergyLowerBoundRequiredIsTrue :
      layerEnergyLowerBoundRequired ≡ true

    continuityRequired :
      Bool

    continuityRequiredIsTrue :
      continuityRequired ≡ true

    harnackRequired :
      Bool

    harnackRequiredIsTrue :
      harnackRequired ≡ true

    integralToPointwiseB0UpgradeRequired :
      Bool

    integralToPointwiseB0UpgradeRequiredIsTrue :
      integralToPointwiseB0UpgradeRequired ≡ true

    boundaryHBPointwiseB0Proved :
      Bool

    boundaryHBPointwiseB0ProvedIsFalse :
      boundaryHBPointwiseB0Proved ≡ false

    boundaryHBPromoted :
      Bool

    boundaryHBPromotedIsFalse :
      boundaryHBPromoted ≡ false

    boundaryHBAssemblyStatement :
      String

    boundaryHBAssemblyStatementIsCanonical :
      boundaryHBAssemblyStatement ≡ boundaryHBAssemblyStatementText

    promotionFlags :
      List BoundaryHBAssemblyPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Lambda2PlusTransportInequalityReceipt public
open BoundaryHBAssemblyReceipt public

canonicalLambda2PlusTransportInequalityReceipt :
  Lambda2PlusTransportInequalityReceipt
canonicalLambda2PlusTransportInequalityReceipt =
  record
    { status =
        lambda2PlusTransportShapeRecordedCandidateOnly
    ; statusIsCanonical =
        refl
    ; tokens =
        canonicalLambda2PlusTransportInequalityTokens
    ; tokensAreCanonical =
        refl
    ; transportInequalityStatement =
        lambda2PlusTransportInequalityStatement
    ; transportInequalityStatementIsCanonical =
        refl
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; theoremPromoted =
        false
    ; theoremPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "nu, C_NS, t1, t2, lambda2+, L2, and L3 are recorded as a symbolic transport-inequality shape"
        ∷ "No transport theorem is promoted here"
        ∷ "The receipt stays candidate-only by construction"
        ∷ []
    }

canonicalBoundaryHBAssemblyReceipt :
  BoundaryHBAssemblyReceipt
canonicalBoundaryHBAssemblyReceipt =
  record
    { status =
        boundaryHBAssemblyBlockedCandidateOnly
    ; statusIsCanonical =
        refl
    ; blockers =
        canonicalBoundaryHBAssemblyBlockers
    ; blockersAreCanonical =
        refl
    ; kornLevelSetRequired =
        true
    ; kornLevelSetRequiredIsTrue =
        refl
    ; layerEnergyLowerBoundRequired =
        true
    ; layerEnergyLowerBoundRequiredIsTrue =
        refl
    ; continuityRequired =
        true
    ; continuityRequiredIsTrue =
        refl
    ; harnackRequired =
        true
    ; harnackRequiredIsTrue =
        refl
    ; integralToPointwiseB0UpgradeRequired =
        true
    ; integralToPointwiseB0UpgradeRequiredIsTrue =
        refl
    ; boundaryHBPointwiseB0Proved =
        false
    ; boundaryHBPointwiseB0ProvedIsFalse =
        refl
    ; boundaryHBPromoted =
        false
    ; boundaryHBPromotedIsFalse =
        refl
    ; boundaryHBAssemblyStatement =
        boundaryHBAssemblyStatementText
    ; boundaryHBAssemblyStatementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "KornLevelSet remains required"
        ∷ "The layer-energy lower bound remains required"
        ∷ "Continuity and Harnack inputs remain required for the pointwise upgrade"
        ∷ "Integral control has not yet been upgraded to pointwise b0"
        ∷ "BoundaryHB stays candidate-only and blocked"
        ∷ []
    }
