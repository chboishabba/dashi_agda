module DASHI.Physics.Closure.NSTriadNegativeFrameOperatorBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- NS triad negative-frame operator boundary.
--
-- This receipt is intentionally fail-closed.  It records the Hessian / signed
-- phase Laplacian surface
--
--   L_N = B^T W B
--
-- together with the positive/negative split that produces the negative-frame
-- operator K_N.  The stratum-orthogonality and determinant-expansion walls are
-- recorded as open rows only.  No theorem, full-NS, or Clay promotion is made
-- here, and the uniform operator-norm criterion
--
--   sup_N ||K_N||_op <= 1 - eps
--
-- is explicitly not proved.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSTriadNegativeFrameOperatorBoundaryRow : Set where
  hessianSignedPhaseLaplacianSurfaceRecorded :
    NSTriadNegativeFrameOperatorBoundaryRow
  positiveNegativeSplitRecorded :
    NSTriadNegativeFrameOperatorBoundaryRow
  negativeFrameOperatorCriterionRecordedCandidateOnly :
    NSTriadNegativeFrameOperatorBoundaryRow
  stratumOrthogonalityWallRecorded :
    NSTriadNegativeFrameOperatorBoundaryRow
  determinantExpansionWallRecorded :
    NSTriadNegativeFrameOperatorBoundaryRow
  failClosedPromotionWallRecorded :
    NSTriadNegativeFrameOperatorBoundaryRow

canonicalNSTriadNegativeFrameOperatorBoundaryRows :
  List NSTriadNegativeFrameOperatorBoundaryRow
canonicalNSTriadNegativeFrameOperatorBoundaryRows =
  hessianSignedPhaseLaplacianSurfaceRecorded
  ∷ positiveNegativeSplitRecorded
  ∷ negativeFrameOperatorCriterionRecordedCandidateOnly
  ∷ stratumOrthogonalityWallRecorded
  ∷ determinantExpansionWallRecorded
  ∷ failClosedPromotionWallRecorded
  ∷ []

nstriadNegativeFrameOperatorBoundaryRowCount : Nat
nstriadNegativeFrameOperatorBoundaryRowCount =
  listLength canonicalNSTriadNegativeFrameOperatorBoundaryRows

nstriadNegativeFrameOperatorBoundaryRowCountIs6 :
  nstriadNegativeFrameOperatorBoundaryRowCount ≡ 6
nstriadNegativeFrameOperatorBoundaryRowCountIs6 =
  refl

data NSTriadNegativeFrameOperatorBoundaryGap : Set where
  positiveBackboneNegativeFrameCriterionUnproved :
    NSTriadNegativeFrameOperatorBoundaryGap
  uniformInNOperatorNormBoundMissing :
    NSTriadNegativeFrameOperatorBoundaryGap
  stratumOrthogonalityProofMissing :
    NSTriadNegativeFrameOperatorBoundaryGap
  determinantExpansionProofMissing :
    NSTriadNegativeFrameOperatorBoundaryGap
  theoremFullNSClayPromotionClosed :
    NSTriadNegativeFrameOperatorBoundaryGap

canonicalNSTriadNegativeFrameOperatorBoundaryGaps :
  List NSTriadNegativeFrameOperatorBoundaryGap
canonicalNSTriadNegativeFrameOperatorBoundaryGaps =
  positiveBackboneNegativeFrameCriterionUnproved
  ∷ uniformInNOperatorNormBoundMissing
  ∷ stratumOrthogonalityProofMissing
  ∷ determinantExpansionProofMissing
  ∷ theoremFullNSClayPromotionClosed
  ∷ []

nstriadNegativeFrameOperatorBoundaryGapCount : Nat
nstriadNegativeFrameOperatorBoundaryGapCount =
  listLength canonicalNSTriadNegativeFrameOperatorBoundaryGaps

nstriadNegativeFrameOperatorBoundaryGapCountIs5 :
  nstriadNegativeFrameOperatorBoundaryGapCount ≡ 5
nstriadNegativeFrameOperatorBoundaryGapCountIs5 =
  refl

canonicalWitnessTerm : String
canonicalWitnessTerm =
  "candidate-only witness: L_N = B^T W B and the K_N split are recorded, but sup_N ||K_N||_op <= 1-eps is open"

organizationString : String
organizationString =
  "O: record the triad negative-frame operator wall behind the low-frustration basin analysis."

requirementString : String
requirementString =
  "R: record L_N = B^T W B, the positive/negative split into K_N, the open operator-norm criterion, and the wall rows honestly."

codeArtifactString : String
codeArtifactString =
  "C: export canonical rows, gaps, a compact ORCSLPGF record, false promotion flags, and a canonical witness term in one self-contained receipt."

stateString : String
stateString =
  "S: candidate-only data are recorded; the subunit operator bound sup_N ||K_N||_op <= 1-eps is not proved; theorem/full-NS/Clay flags remain false."

latticeString : String
latticeString =
  "L: Hessian/signed phase Laplacian -> positive/negative split -> K_N operator criterion -> stratum orthogonality wall -> determinant expansion wall -> fail-closed boundary."

proposalString : String
proposalString =
  "P: keep the negative-frame route as a receipt only until the positive-backbone/negative-frame criterion and uniform-in-N bound are analytically established."

governanceString : String
governanceString =
  "G: all promotion flags are false; no theorem, full-NS, or Clay promotion may be inferred from this boundary."

failString : String
failString =
  "F: the missing evidence is the analytic proof of the positive-backbone / negative-frame criterion and its uniform-in-N operator-norm bound."

record NSTriadNegativeFrameOperatorBoundaryORCSLPGF : Set where
  constructor mkNSTriadNegativeFrameOperatorBoundaryORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ failString

open NSTriadNegativeFrameOperatorBoundaryORCSLPGF public

canonicalNSTriadNegativeFrameOperatorBoundaryORCSLPGF :
  NSTriadNegativeFrameOperatorBoundaryORCSLPGF
canonicalNSTriadNegativeFrameOperatorBoundaryORCSLPGF =
  mkNSTriadNegativeFrameOperatorBoundaryORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    failString
    refl

record NSTriadNegativeFrameOperatorBoundary : Setω where
  constructor mkNSTriadNegativeFrameOperatorBoundary
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadNegativeFrameOperatorBoundary"

    witnessTerm :
      String
    witnessTermIsCanonical :
      witnessTerm ≡ canonicalWitnessTerm

    rows :
      List NSTriadNegativeFrameOperatorBoundaryRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadNegativeFrameOperatorBoundaryRows
    rowCount :
      Nat
    rowCountIsCanonical :
      rowCount ≡ nstriadNegativeFrameOperatorBoundaryRowCount

    gaps :
      List NSTriadNegativeFrameOperatorBoundaryGap
    gapsAreCanonical :
      gaps ≡ canonicalNSTriadNegativeFrameOperatorBoundaryGaps
    gapCount :
      Nat
    gapCountIsCanonical :
      gapCount ≡ nstriadNegativeFrameOperatorBoundaryGapCount

    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    failClosed :
      Bool
    failClosedIsTrue :
      failClosed ≡ true

    hessianSignedPhaseLaplacianRecorded :
      Bool
    hessianSignedPhaseLaplacianRecordedIsTrue :
      hessianSignedPhaseLaplacianRecorded ≡ true

    negativeFrameSplitRecorded :
      Bool
    negativeFrameSplitRecordedIsTrue :
      negativeFrameSplitRecorded ≡ true

    negativeFrameOperatorCriterionProved :
      Bool
    negativeFrameOperatorCriterionProvedIsFalse :
      negativeFrameOperatorCriterionProved ≡ false

    stratumOrthogonalityProved :
      Bool
    stratumOrthogonalityProvedIsFalse :
      stratumOrthogonalityProved ≡ false

    determinantExpansionProved :
      Bool
    determinantExpansionProvedIsFalse :
      determinantExpansionProved ≡ false

    subunitOperatorBoundProved :
      Bool
    subunitOperatorBoundProvedIsFalse :
      subunitOperatorBoundProved ≡ false

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted :
      Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    orcslpgf :
      NSTriadNegativeFrameOperatorBoundaryORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadNegativeFrameOperatorBoundaryORCSLPGF

open NSTriadNegativeFrameOperatorBoundary public

canonicalNSTriadNegativeFrameOperatorBoundary :
  NSTriadNegativeFrameOperatorBoundary
canonicalNSTriadNegativeFrameOperatorBoundary =
  mkNSTriadNegativeFrameOperatorBoundary
    "NSTriadNegativeFrameOperatorBoundary"
    refl
    canonicalWitnessTerm
    refl
    canonicalNSTriadNegativeFrameOperatorBoundaryRows
    refl
    nstriadNegativeFrameOperatorBoundaryRowCount
    refl
    canonicalNSTriadNegativeFrameOperatorBoundaryGaps
    refl
    nstriadNegativeFrameOperatorBoundaryGapCount
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    canonicalNSTriadNegativeFrameOperatorBoundaryORCSLPGF
    refl
