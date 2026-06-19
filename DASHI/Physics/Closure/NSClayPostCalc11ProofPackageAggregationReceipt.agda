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
-- This module is a string-label ledger only.  It names the post-Calc-11
-- source surfaces, keeps the two new receipts as labels only when present,
-- and records the lattice:
--
--   calc11 complete -> closeable proof packages -> conditional theorem
--   package -> hard walls KornLevelSet/collapseImpossible -> Clay false
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
  "NSVorticityE2ProjectionCalc11ResultReceipt"
  ∷ "NSCoareaGradientStepAPerComponentReceipt"
  ∷ "LocalConcentrationPigeonConcentrationReceipt"
  ∷ "Lambda2PlusTransportInequalityBoundaryHBReceipt"
  ∷ "NSBoundaryHBCorrectPointwiseReceipt"
  ∷ "NSCollapseImpossibleCalc11TargetReceipt"
  ∷ "NSClayPostCalc11StateAggregationReceipt"
  ∷ "NSClayConcisePathCalc11IntegrationReceipt"
  ∷ "NSClayThreeHardTheoremsDistanceReceipt"
  ∷ []

data NSClayPostCalc11ProofPackageAggregationLatticeStep : Set where
  calc11Complete :
    NSClayPostCalc11ProofPackageAggregationLatticeStep

  closeableProofPackages :
    NSClayPostCalc11ProofPackageAggregationLatticeStep

  conditionalTheoremPackage :
    NSClayPostCalc11ProofPackageAggregationLatticeStep

  hardWallsKornLevelSetCollapseImpossible :
    NSClayPostCalc11ProofPackageAggregationLatticeStep

  clayFalse :
    NSClayPostCalc11ProofPackageAggregationLatticeStep

canonicalNSClayPostCalc11ProofPackageAggregationLatticeSteps :
  List NSClayPostCalc11ProofPackageAggregationLatticeStep
canonicalNSClayPostCalc11ProofPackageAggregationLatticeSteps =
  calc11Complete
  ∷ closeableProofPackages
  ∷ conditionalTheoremPackage
  ∷ hardWallsKornLevelSetCollapseImpossible
  ∷ clayFalse
  ∷ []

proofPackageAggregationStatementText : String
proofPackageAggregationStatementText =
  "Calc 11 is complete; closeable proof packages are recorded as labels only; the conditional theorem package is recorded next; the hard walls remain KornLevelSet/collapseImpossible; Clay stays false."

aggregationBoundaryText : String
aggregationBoundaryText =
  "This is a string-label aggregation receipt only.  It names the post-Calc-11 source surfaces, keeps the two new receipts as labels only, and avoids import coupling."

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
      "Name the post-Calc-11 source surfaces as string labels, record the lattice, and keep Clay false."

    C :
      String
    CIsCanonical :
      C ≡
      "NSClayPostCalc11ProofPackageAggregationReceipt.agda is a local ledger surface only; it imports no worker-authored modules."

    S :
      String
    SIsCanonical :
      S ≡
      "NSVorticityE2ProjectionCalc11ResultReceipt, NSCoareaGradientStepAPerComponentReceipt, LocalConcentrationPigeonConcentrationReceipt, Lambda2PlusTransportInequalityBoundaryHBReceipt, NSBoundaryHBCorrectPointwiseReceipt, NSCollapseImpossibleCalc11TargetReceipt, NSClayPostCalc11StateAggregationReceipt, NSClayConcisePathCalc11IntegrationReceipt, and NSClayThreeHardTheoremsDistanceReceipt are the named post-Calc-11 source surfaces."

    L :
      String
    LIsCanonical :
      L ≡
      "calc11 complete -> closeable proof packages -> conditional theorem package -> hard walls KornLevelSet/collapseImpossible -> Clay false"

    P :
      String
    PIsCanonical :
      P ≡
      "Use string-label aggregation only; do not import the named surfaces; keep the closeable proof-package and conditional theorem-package lattice as labels."

    G :
      String
    GIsCanonical :
      G ≡
      "Fail closed on Clay promotion; the evidence remains read-only labels."

    F :
      String
    FIsCanonical :
      F ≡
      "KornLevelSet/collapseImpossible remains the hard wall."

open NSClayPostCalc11ProofPackageAggregationORCSLPGF public

canonicalNSClayPostCalc11ProofPackageAggregationORCSLPGF :
  NSClayPostCalc11ProofPackageAggregationORCSLPGF
canonicalNSClayPostCalc11ProofPackageAggregationORCSLPGF =
  mkNSClayPostCalc11ProofPackageAggregationORCSLPGF
    "Worker 6 owns the post-Calc-11 proof-package aggregation receipt only."
    refl
    "Name the post-Calc-11 source surfaces as string labels, record the lattice, and keep Clay false."
    refl
    "NSClayPostCalc11ProofPackageAggregationReceipt.agda is a local ledger surface only; it imports no worker-authored modules."
    refl
    "NSVorticityE2ProjectionCalc11ResultReceipt, NSCoareaGradientStepAPerComponentReceipt, LocalConcentrationPigeonConcentrationReceipt, Lambda2PlusTransportInequalityBoundaryHBReceipt, NSBoundaryHBCorrectPointwiseReceipt, NSCollapseImpossibleCalc11TargetReceipt, NSClayPostCalc11StateAggregationReceipt, NSClayConcisePathCalc11IntegrationReceipt, and NSClayThreeHardTheoremsDistanceReceipt are the named post-Calc-11 source surfaces."
    refl
    "calc11 complete -> closeable proof packages -> conditional theorem package -> hard walls KornLevelSet/collapseImpossible -> Clay false"
    refl
    "Use string-label aggregation only; do not import the named surfaces; keep the closeable proof-package and conditional theorem-package lattice as labels."
    refl
    "Fail closed on Clay promotion; the evidence remains read-only labels."
    refl
    "KornLevelSet/collapseImpossible remains the hard wall."
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
        ∷ "closeable proof packages"
        ∷ "conditional theorem package"
        ∷ "hard walls KornLevelSet/collapseImpossible"
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
        ∷ "closeable proof packages"
        ∷ "conditional theorem package"
        ∷ "hard walls KornLevelSet/collapseImpossible"
        ∷ "Clay false"
        ∷ []
    ; receiptBoundaryAreCanonical =
        refl
    }
