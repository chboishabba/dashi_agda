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
-- the candidate variables C_geo/C_iso/r/K/G/f=lambda2+, the proof-route
-- ledger, the Calc 11 correction, and the non-promotion boundary, but it
-- does not prove any analytic coarea estimate.

data CorrectedCoareaGradientBoundStatus : Set where
  candidateOnlyFailClosed :
    CorrectedCoareaGradientBoundStatus

data CorrectedCoareaGradientBoundProofRouteStep : Set where
  routeLayerCake :
    CorrectedCoareaGradientBoundProofRouteStep
  routeCoareaReverse :
    CorrectedCoareaGradientBoundProofRouteStep
  routeIsoperimetric :
    CorrectedCoareaGradientBoundProofRouteStep
  routeHolder :
    CorrectedCoareaGradientBoundProofRouteStep
  routeCalc11ExponentOne :
    CorrectedCoareaGradientBoundProofRouteStep
  routeVariablesCgeoCisoRGK :
    CorrectedCoareaGradientBoundProofRouteStep
  routeLambda2PlusFunctional :
    CorrectedCoareaGradientBoundProofRouteStep
  routeGovernanceNonPromotion :
    CorrectedCoareaGradientBoundProofRouteStep

canonicalCorrectedCoareaGradientBoundProofRouteSteps :
  List CorrectedCoareaGradientBoundProofRouteStep
canonicalCorrectedCoareaGradientBoundProofRouteSteps =
  routeLayerCake
  ∷ routeCoareaReverse
  ∷ routeIsoperimetric
  ∷ routeHolder
  ∷ routeCalc11ExponentOne
  ∷ routeVariablesCgeoCisoRGK
  ∷ routeLambda2PlusFunctional
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
  calc11LocksExponentAtOne :
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
  ∷ calc11LocksExponentAtOne
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

    G :
      String
    GIsCanonical :
      G ≡ "G"

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
        ≡ "sup_B |grad lambda2+| >= K/(C_geo*r)"

    proofPackageSummary :
      String
    proofPackageSummaryIsCanonical :
      proofPackageSummary
        ≡ "layer-cake -> coarea reverse -> isoperimetric -> Holder; Calc 11 fixes r^1 with C_geo/C_iso/r/K/G tracked"

    proofRouteSteps :
      List CorrectedCoareaGradientBoundProofRouteStep
    proofRouteStepsIsCanonical :
      proofRouteSteps ≡ canonicalCorrectedCoareaGradientBoundProofRouteSteps

    conclusionText :
      String
    conclusionTextIsCanonical :
      conclusionText
        ≡ "sup_B |grad lambda2+| >= K/(C_geo*r)"

    boundaryText :
      String
    boundaryTextIsCanonical :
      boundaryText
        ≡ "Candidate-only corrected coarea gradient bound receipt: theorem and Clay promotion remain false."

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
    "G"
    refl
    "lambda2+"
    refl
    "r^1"
    refl
    "sup_B |grad lambda2+| >= K/(C_geo*r)"
    refl
    "layer-cake -> coarea reverse -> isoperimetric -> Holder; Calc 11 fixes r^1 with C_geo/C_iso/r/K/G tracked"
    refl
    canonicalCorrectedCoareaGradientBoundProofRouteSteps
    refl
    "sup_B |grad lambda2+| >= K/(C_geo*r)"
    refl
    "Candidate-only corrected coarea gradient bound receipt: theorem and Clay promotion remain false."
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
        ≡ "Governance-only candidate receipt; theorem and Clay promotion remain false."

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
    "Governance-only candidate receipt; theorem and Clay promotion remain false."
    refl

open CorrectedCoareaGradientBoundReceipt public
open CorrectedCoareaGradientBoundShape public
