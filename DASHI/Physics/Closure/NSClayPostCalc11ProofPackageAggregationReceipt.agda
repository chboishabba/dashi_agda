module DASHI.Physics.Closure.NSClayPostCalc11ProofPackageAggregationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Candidate-only aggregation receipt for the post-Calc-11 proof-package
-- surface.
--
-- This module is a string-label ledger only.  It names the current
-- canonical pipeline as labels:
--
--   Calc11 complete/no_special_alignment
--   -> seven closeable proof packages
--   -> optional Calc12 non-blocking route-selector
--   -> hard walls exactly KornLevelSet and collapseImpossible
--   -> Clay false
--
-- No worker-authored modules are imported here.

data NSClayPostCalc11ProofPackageAggregationStatus : Set where
  candidateOnlyStringLabelAggregationChecked :
    NSClayPostCalc11ProofPackageAggregationStatus

data NSClayPostCalc11ProofPackageAggregationPromotion : Set where

nsClayPostCalc11ProofPackageAggregationPromotionImpossibleHere :
  NSClayPostCalc11ProofPackageAggregationPromotion →
  ⊥
nsClayPostCalc11ProofPackageAggregationPromotionImpossibleHere ()

sourceSurfaceLabels : List String
sourceSurfaceLabels =
  "Calc11 result complete/no_special_alignment"
  ∷ "millerToH5 | vars=(E0,Csob,Cint)"
  ∷ "GD3 two-gap | vars=(M,delta0,delta1,Cemb)"
  ∷ "coareaGradientBound exponent r^1 | vars=(Cgeo,r,K)"
  ∷ "LocalConcentration | vars=(tail/L3 weak)"
  ∷ "pigeon_concentration | vars=(h_fin,Nmax,K/Nmax^(1/3))"
  ∷ "StepA_PerComponent | vars=(d0,tau0,r/local L3)"
  ∷ "BoundaryHB_Correct via pointwise kornBiaxialBound | vars=(lambda_min,eta,b0)"
  ∷ "NSCalc12ParametricOmegaE2ScalingReceipt"
  ∷ "KornLevelSet"
  ∷ "collapseImpossible"
  ∷ "Clay false"
  ∷ []

data NSClayPostCalc11ProofPackageAggregationLatticeStep : Set where
  calc11CompleteNoSpecialAlignment :
    NSClayPostCalc11ProofPackageAggregationLatticeStep

  sevenCloseableProofPackages :
    NSClayPostCalc11ProofPackageAggregationLatticeStep

  optionalCalc12NonBlockingRouteSelector :
    NSClayPostCalc11ProofPackageAggregationLatticeStep

  hardWallsExactlyKornLevelSetAndCollapseImpossible :
    NSClayPostCalc11ProofPackageAggregationLatticeStep

  clayFalse :
    NSClayPostCalc11ProofPackageAggregationLatticeStep

canonicalNSClayPostCalc11ProofPackageAggregationLatticeSteps :
  List NSClayPostCalc11ProofPackageAggregationLatticeStep
canonicalNSClayPostCalc11ProofPackageAggregationLatticeSteps =
  calc11CompleteNoSpecialAlignment
  ∷ sevenCloseableProofPackages
  ∷ optionalCalc12NonBlockingRouteSelector
  ∷ hardWallsExactlyKornLevelSetAndCollapseImpossible
  ∷ clayFalse
  ∷ []

proofPackageAggregationStatementText : String
proofPackageAggregationStatementText =
  "Calc11 is complete with no_special_alignment; seven closeable packages are recorded; the optional Calc12 route-selector is non-blocking; the hard walls are exactly KornLevelSet and collapseImpossible; Clay stays false."

aggregationBoundaryText : String
aggregationBoundaryText =
  "This is a string-label aggregation receipt only.  It names the current canonical pipeline, keeps the optional Calc12 route-selector as a label only, and avoids import coupling."

record NSClayPostCalc11ProofPackageAggregationORCSLPGF : Set where
  constructor mkNSClayPostCalc11ProofPackageAggregationORCSLPGF
  field
    O :
      String
    OIsCanonical :
      O ≡
      "Worker 6 owns the post-Calc-11 proof-package aggregation receipt only."

    R :
      String
    RIsCanonical :
      R ≡
      "Record the current canonical pipeline as string labels, keep the optional Calc12 route-selector non-blocking, and keep Clay false."

    C :
      String
    CIsCanonical :
      C ≡
      "NSClayPostCalc11ProofPackageAggregationReceipt.agda is a local ledger surface only; it imports no worker-authored modules."

    S :
      String
    SIsCanonical :
      S ≡
      "Calc11 result complete/no_special_alignment, the seven closeable package rows, the optional Calc12 non-blocking route-selector label, KornLevelSet, collapseImpossible, and Clay false are the canonical source labels."

    L :
      String
    LIsCanonical :
      L ≡
      "Calc11 complete/no_special_alignment -> seven closeable packages -> optional Calc12 non-blocking route-selector -> hard walls exactly KornLevelSet and collapseImpossible -> Clay false"

    P :
      String
    PIsCanonical :
      P ≡
      "Use string-label aggregation only; do not import the named surfaces; keep the seven closeable packages and optional Calc12 route-selector as labels."

    G :
      String
    GIsCanonical :
      G ≡
      "Fail closed on Clay promotion; the evidence remains read-only labels and the optional Calc12 route-selector is non-blocking only."

    F :
      String
    FIsCanonical :
      F ≡
      "KornLevelSet and collapseImpossible remain the hard walls."

open NSClayPostCalc11ProofPackageAggregationORCSLPGF public

canonicalNSClayPostCalc11ProofPackageAggregationORCSLPGF :
  NSClayPostCalc11ProofPackageAggregationORCSLPGF
canonicalNSClayPostCalc11ProofPackageAggregationORCSLPGF =
  mkNSClayPostCalc11ProofPackageAggregationORCSLPGF
    "Worker 6 owns the post-Calc-11 proof-package aggregation receipt only."
    refl
    "Record the current canonical pipeline as string labels, keep the optional Calc12 route-selector non-blocking, and keep Clay false."
    refl
    "NSClayPostCalc11ProofPackageAggregationReceipt.agda is a local ledger surface only; it imports no worker-authored modules."
    refl
    "Calc11 result complete/no_special_alignment, the seven closeable package rows, the optional Calc12 non-blocking route-selector label, KornLevelSet, collapseImpossible, and Clay false are the canonical source labels."
    refl
    "Calc11 complete/no_special_alignment -> seven closeable packages -> optional Calc12 non-blocking route-selector -> hard walls exactly KornLevelSet and collapseImpossible -> Clay false"
    refl
    "Use string-label aggregation only; do not import the named surfaces; keep the seven closeable packages and optional Calc12 route-selector as labels."
    refl
    "Fail closed on Clay promotion; the evidence remains read-only labels and the optional Calc12 route-selector is non-blocking only."
    refl
    "KornLevelSet and collapseImpossible remain the hard walls."
    refl

record NSClayPostCalc11ProofPackageAggregationReceipt : Setω where
  field
    status :
      NSClayPostCalc11ProofPackageAggregationStatus

    statusIsCanonical :
      status ≡ candidateOnlyStringLabelAggregationChecked

    sourceSurfaces :
      List String

    sourceSurfacesAreCanonical :
      sourceSurfaces ≡ sourceSurfaceLabels

    lattice :
      List NSClayPostCalc11ProofPackageAggregationLatticeStep

    latticeAreCanonical :
      lattice ≡ canonicalNSClayPostCalc11ProofPackageAggregationLatticeSteps

    proofPackageAggregationStatement :
      String

    proofPackageAggregationStatementIsCanonical :
      proofPackageAggregationStatement ≡ proofPackageAggregationStatementText

    aggregationBoundary :
      String

    aggregationBoundaryIsCanonical :
      aggregationBoundary ≡ aggregationBoundaryText

    orcslpgf :
      NSClayPostCalc11ProofPackageAggregationORCSLPGF

    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSClayPostCalc11ProofPackageAggregationORCSLPGF

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotionFlags :
      List NSClayPostCalc11ProofPackageAggregationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

    receiptBoundaryAreCanonical :
      receiptBoundary ≡
      ( "calc11 complete"
        ∷ "no_special_alignment"
        ∷ "seven closeable packages"
        ∷ "optional Calc12 non-blocking route-selector"
        ∷ "hard walls exactly KornLevelSet and collapseImpossible"
        ∷ "Clay false"
        ∷ [] )

open NSClayPostCalc11ProofPackageAggregationReceipt public

canonicalNSClayPostCalc11ProofPackageAggregationReceipt :
  NSClayPostCalc11ProofPackageAggregationReceipt
canonicalNSClayPostCalc11ProofPackageAggregationReceipt =
  record
    { status =
        candidateOnlyStringLabelAggregationChecked
    ; statusIsCanonical =
        refl
    ; sourceSurfaces =
        sourceSurfaceLabels
    ; sourceSurfacesAreCanonical =
        refl
    ; lattice =
        canonicalNSClayPostCalc11ProofPackageAggregationLatticeSteps
    ; latticeAreCanonical =
        refl
    ; proofPackageAggregationStatement =
        proofPackageAggregationStatementText
    ; proofPackageAggregationStatementIsCanonical =
        refl
    ; aggregationBoundary =
        aggregationBoundaryText
    ; aggregationBoundaryIsCanonical =
        refl
    ; orcslpgf =
        canonicalNSClayPostCalc11ProofPackageAggregationORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "calc11 complete"
        ∷ "no_special_alignment"
        ∷ "seven closeable packages"
        ∷ "optional Calc12 non-blocking route-selector"
        ∷ "hard walls exactly KornLevelSet and collapseImpossible"
        ∷ "Clay false"
        ∷ []
    ; receiptBoundaryAreCanonical =
        refl
    }
