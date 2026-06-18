module DASHI.Physics.Closure.CorrectedCoareaGradientBoundReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate-only receipt for the corrected coarea gradient bound package.
--
-- The corrected bound shape is recorded with the exact r-exponent fixed at
-- r^1, not r^(7/2).  This module is a governance receipt only: it records
-- the candidate variables C_geo/C_iso/r/K/f=lambda2+, the proof-route
-- ledger, and the non-promotion boundary, but it does not prove any
-- analytic coarea estimate.

data CorrectedCoareaGradientBoundStatus : Set where
  candidateOnlyFailClosed :
    CorrectedCoareaGradientBoundStatus

data CorrectedCoareaGradientBoundProofRouteStep : Set where
  routeGeometryConstant :
    CorrectedCoareaGradientBoundProofRouteStep
  routeIsoperimetricConstant :
    CorrectedCoareaGradientBoundProofRouteStep
  routeCoareaExtraction :
    CorrectedCoareaGradientBoundProofRouteStep
  routeLambda2PlusFunctional :
    CorrectedCoareaGradientBoundProofRouteStep
  routeExponentOne :
    CorrectedCoareaGradientBoundProofRouteStep
  routeGovernanceNonPromotion :
    CorrectedCoareaGradientBoundProofRouteStep

canonicalCorrectedCoareaGradientBoundProofRouteSteps :
  List CorrectedCoareaGradientBoundProofRouteStep
canonicalCorrectedCoareaGradientBoundProofRouteSteps =
  routeGeometryConstant
  ∷ routeIsoperimetricConstant
  ∷ routeCoareaExtraction
  ∷ routeLambda2PlusFunctional
  ∷ routeExponentOne
  ∷ routeGovernanceNonPromotion
  ∷ []

data CorrectedCoareaGradientBoundGovernance : Set where
  candidateOnly :
    CorrectedCoareaGradientBoundGovernance
  noTheoremPromotion :
    CorrectedCoareaGradientBoundGovernance
  noClayPromotion :
    CorrectedCoareaGradientBoundGovernance
  noTerminalPromotion :
    CorrectedCoareaGradientBoundGovernance
  exactExponentRecorded :
    CorrectedCoareaGradientBoundGovernance
  rSevenHalvesRejected :
    CorrectedCoareaGradientBoundGovernance

canonicalCorrectedCoareaGradientBoundGovernance :
  List CorrectedCoareaGradientBoundGovernance
canonicalCorrectedCoareaGradientBoundGovernance =
  candidateOnly
  ∷ noTheoremPromotion
  ∷ noClayPromotion
  ∷ noTerminalPromotion
  ∷ exactExponentRecorded
  ∷ rSevenHalvesRejected
  ∷ []

data CorrectedCoareaGradientBoundNonPromotion : Set where
  theoremPromotionFalse :
    CorrectedCoareaGradientBoundNonPromotion
  clayPromotionFalse :
    CorrectedCoareaGradientBoundNonPromotion
  terminalPromotionFalse :
    CorrectedCoareaGradientBoundNonPromotion
  proofPackageCandidateOnly :
    CorrectedCoareaGradientBoundNonPromotion

canonicalCorrectedCoareaGradientBoundNonPromotion :
  List CorrectedCoareaGradientBoundNonPromotion
canonicalCorrectedCoareaGradientBoundNonPromotion =
  theoremPromotionFalse
  ∷ clayPromotionFalse
  ∷ terminalPromotionFalse
  ∷ proofPackageCandidateOnly
  ∷ []

record CorrectedCoareaGradientBoundShape : Set where
  constructor mkCorrectedCoareaGradientBoundShape
  field
    C_geo :
      String
    C_geoIsCanonical :
      C_geo ≡ "C_geo"

    C_iso :
      String
    C_isoIsCanonical :
      C_iso ≡ "C_iso"

    r :
      String
    rIsCanonical :
      r ≡ "r"

    K :
      String
    KIsCanonical :
      K ≡ "K"

    fLambda2Plus :
      String
    fLambda2PlusIsCanonical :
      fLambda2Plus ≡ "lambda2+"

    correctedExponentOfR :
      String
    correctedExponentOfRIsCanonical :
      correctedExponentOfR ≡ "r^1"

    correctedBoundShape :
      String
    correctedBoundShapeIsCanonical :
      correctedBoundShape
        ≡ "C_geo * C_iso * r^1 / K with f=lambda2+"

    proofRouteSteps :
      List CorrectedCoareaGradientBoundProofRouteStep
    proofRouteStepsIsCanonical :
      proofRouteSteps ≡ canonicalCorrectedCoareaGradientBoundProofRouteSteps

    boundaryText :
      String
    boundaryTextIsCanonical :
      boundaryText
        ≡ "Candidate-only corrected coarea gradient bound shape recorded with r^1, not r^(7/2)."

canonicalCorrectedCoareaGradientBoundShape :
  CorrectedCoareaGradientBoundShape
canonicalCorrectedCoareaGradientBoundShape =
  mkCorrectedCoareaGradientBoundShape
    "C_geo"
    refl
    "C_iso"
    refl
    "r"
    refl
    "K"
    refl
    "lambda2+"
    refl
    "r^1"
    refl
    "C_geo * C_iso * r^1 / K with f=lambda2+"
    refl
    canonicalCorrectedCoareaGradientBoundProofRouteSteps
    refl
    "Candidate-only corrected coarea gradient bound shape recorded with r^1, not r^(7/2)."
    refl

record CorrectedCoareaGradientBoundReceipt : Set where
  constructor mkCorrectedCoareaGradientBoundReceipt
  field
    status :
      CorrectedCoareaGradientBoundStatus
    statusIsCanonical :
      status ≡ candidateOnlyFailClosed

    shape :
      CorrectedCoareaGradientBoundShape
    shapeIsCanonical :
      shape ≡ canonicalCorrectedCoareaGradientBoundShape

    governance :
      List CorrectedCoareaGradientBoundGovernance
    governanceIsCanonical :
      governance ≡ canonicalCorrectedCoareaGradientBoundGovernance

    nonPromotion :
      List CorrectedCoareaGradientBoundNonPromotion
    nonPromotionIsCanonical :
      nonPromotion ≡ canonicalCorrectedCoareaGradientBoundNonPromotion

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalPromoted :
      Bool
    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    receiptBoundary :
      String
    receiptBoundaryIsCanonical :
      receiptBoundary
        ≡ "Governance-only candidate receipt; no theorem, Clay, or terminal promotion is supplied."

canonicalCorrectedCoareaGradientBoundReceipt :
  CorrectedCoareaGradientBoundReceipt
canonicalCorrectedCoareaGradientBoundReceipt =
  mkCorrectedCoareaGradientBoundReceipt
    candidateOnlyFailClosed
    refl
    canonicalCorrectedCoareaGradientBoundShape
    refl
    canonicalCorrectedCoareaGradientBoundGovernance
    refl
    canonicalCorrectedCoareaGradientBoundNonPromotion
    refl
    false
    refl
    false
    refl
    false
    refl
    "Governance-only candidate receipt; no theorem, Clay, or terminal promotion is supplied."
    refl

open CorrectedCoareaGradientBoundReceipt public
open CorrectedCoareaGradientBoundShape public
