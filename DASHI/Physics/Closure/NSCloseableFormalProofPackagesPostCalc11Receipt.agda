module DASHI.Physics.Closure.NSCloseableFormalProofPackagesPostCalc11Receipt where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate-only receipt for the closeable post-Calc-11 proof packages.
--
-- This is a checked label ledger only.  It records the seven closeable
-- post-Calc-11 proof packages together with the exact vars/shapes the lane
-- asked for.  No theorem promotion or Clay promotion flags appear here.

data NSCloseableFormalProofPackagesPostCalc11Status : Set where
  candidateOnlyCloseablePackagesRecorded :
    NSCloseableFormalProofPackagesPostCalc11Status

closeablePackageRowsText : List String
closeablePackageRowsText =
  "millerToH5 | vars=(E0,Csob,Cint)"
  ∷ "GD3 two-gap | vars=(M,delta0,delta1,Cemb)"
  ∷ "coareaGradientBound exponent r^1 | vars=(Cgeo,r,K)"
  ∷ "LocalConcentration | vars=(tail/L3 weak)"
  ∷ "pigeon_concentration | vars=(h_fin,Nmax,K/Nmax^(1/3))"
  ∷ "StepA_PerComponent | vars=(d0,tau0,r/local L3)"
  ∷ "BoundaryHB_Correct via pointwise kornBiaxialBound | vars=(lambda_min,eta,b0)"
  ∷ []

receiptBoundaryText : List String
receiptBoundaryText =
  "Candidate-only ledger for the seven closeable post-Calc-11 proof packages."
  ∷ "The exact vars/shapes are recorded as string labels only."
  ∷ "No theorem promotion flag is present."
  ∷ "No Clay promotion flag is present."
  ∷ []

record NSCloseableFormalProofPackagesPostCalc11ORCSLPGF : Set where
  constructor mkNSCloseableFormalProofPackagesPostCalc11ORCSLPGF
  field
    O :
      String
    OIsCanonical :
      O ≡
      "Worker 3 owns the closeable post-Calc-11 proof-package receipt only."

    R :
      String
    RIsCanonical :
      R ≡
      "Record the seven closeable post-Calc-11 proof packages and their exact vars/shapes as a candidate-only ledger."

    C :
      String
    CIsCanonical :
      C ≡
      "Create only NSCloseableFormalProofPackagesPostCalc11Receipt.agda."

    S :
      String
    SIsCanonical :
      S ≡
      "millerToH5, GD3 two-gap, coareaGradientBound, LocalConcentration, pigeon_concentration, StepA_PerComponent, BoundaryHB_Correct."

    L :
      String
    LIsCanonical :
      L ≡
      "millerToH5 -> GD3 two-gap -> coareaGradientBound -> LocalConcentration -> pigeon_concentration -> StepA_PerComponent -> BoundaryHB_Correct"

    P :
      String
    PIsCanonical :
      P ≡
      "millerToH5 (E0,Csob,Cint); GD3 two-gap (M,delta0,delta1,Cemb); coareaGradientBound r^1 (Cgeo,r,K); LocalConcentration (tail/L3 weak); pigeon_concentration (h_fin,Nmax,K/Nmax^(1/3)); StepA_PerComponent (d0,tau0,r/local L3); BoundaryHB_Correct via pointwise kornBiaxialBound (lambda_min,eta,b0)"

    G :
      String
    GIsCanonical :
      G ≡
      "Candidate-only; no theorem promotion or Clay promotion flags."

    F :
      String
    FIsCanonical :
      F ≡
      "Receipt surface only; the seven package rows are recorded as string labels."

open NSCloseableFormalProofPackagesPostCalc11ORCSLPGF public

canonicalNSCloseableFormalProofPackagesPostCalc11ORCSLPGF :
  NSCloseableFormalProofPackagesPostCalc11ORCSLPGF
canonicalNSCloseableFormalProofPackagesPostCalc11ORCSLPGF =
  mkNSCloseableFormalProofPackagesPostCalc11ORCSLPGF
    "Worker 3 owns the closeable post-Calc-11 proof-package receipt only."
    refl
    "Record the seven closeable post-Calc-11 proof packages and their exact vars/shapes as a candidate-only ledger."
    refl
    "Create only NSCloseableFormalProofPackagesPostCalc11Receipt.agda."
    refl
    "millerToH5, GD3 two-gap, coareaGradientBound, LocalConcentration, pigeon_concentration, StepA_PerComponent, BoundaryHB_Correct."
    refl
    "millerToH5 -> GD3 two-gap -> coareaGradientBound -> LocalConcentration -> pigeon_concentration -> StepA_PerComponent -> BoundaryHB_Correct"
    refl
    "millerToH5 (E0,Csob,Cint); GD3 two-gap (M,delta0,delta1,Cemb); coareaGradientBound r^1 (Cgeo,r,K); LocalConcentration (tail/L3 weak); pigeon_concentration (h_fin,Nmax,K/Nmax^(1/3)); StepA_PerComponent (d0,tau0,r/local L3); BoundaryHB_Correct via pointwise kornBiaxialBound (lambda_min,eta,b0)"
    refl
    "Candidate-only; no theorem promotion or Clay promotion flags."
    refl
    "Receipt surface only; the seven package rows are recorded as string labels."
    refl

record NSCloseableFormalProofPackagesPostCalc11Receipt : Set where
  field
    status :
      NSCloseableFormalProofPackagesPostCalc11Status

    statusIsCanonical :
      status ≡ candidateOnlyCloseablePackagesRecorded

    closeablePackageRows :
      List String

    closeablePackageRowsAreCanonical :
      closeablePackageRows ≡ closeablePackageRowsText

    orcslpgf :
      NSCloseableFormalProofPackagesPostCalc11ORCSLPGF

    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSCloseableFormalProofPackagesPostCalc11ORCSLPGF

    receiptBoundary :
      List String

    receiptBoundaryAreCanonical :
      receiptBoundary ≡ receiptBoundaryText

open NSCloseableFormalProofPackagesPostCalc11Receipt public

canonicalNSCloseableFormalProofPackagesPostCalc11Receipt :
  NSCloseableFormalProofPackagesPostCalc11Receipt
canonicalNSCloseableFormalProofPackagesPostCalc11Receipt =
  record
    { status =
        candidateOnlyCloseablePackagesRecorded
    ; statusIsCanonical =
        refl
    ; closeablePackageRows =
        closeablePackageRowsText
    ; closeablePackageRowsAreCanonical =
        refl
    ; orcslpgf =
        canonicalNSCloseableFormalProofPackagesPostCalc11ORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    ; receiptBoundary =
        receiptBoundaryText
    ; receiptBoundaryAreCanonical =
        refl
    }
