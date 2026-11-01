module DASHI.Physics.Closure.NSTriadCycleDefectLowerBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- NS triad cycle-defect quantitative lower-bound receipt.
--
-- This receipt records the exact Wall 1 lower-bound formula shape that is
-- supposed to drive the cocycle-frustration floor:
--
--   F_N(ψ) >= (4 / π²) * Δ_n(ψ)² / Σ_e (n_e² / w_e)
--
-- for any weighted cycle witness n ∈ ker(Bᵀ), with
--
--   Δ_n(ψ) = dist(n · ψ, 2π ℤ).
--
-- The receipt is fail-closed: it records the quantitative law shape and the
-- shell-carrier handoff target, but it does not claim a uniform c0 > 0 floor,
-- a frame gap, full NS regularity, or Clay promotion.

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadCycleDefectLowerBoundRow : Set where
  exactQuadraticLowerBoundFormulaRecorded :
    NSTriadCycleDefectLowerBoundRow
  weightedDualNormDenominatorRecorded :
    NSTriadCycleDefectLowerBoundRow
  cycleDefectDistanceTermRecorded :
    NSTriadCycleDefectLowerBoundRow
  shellCarrierOracleTargetHandoffRecorded :
    NSTriadCycleDefectLowerBoundRow
  floorToFrameGapDependencyRecorded :
    NSTriadCycleDefectLowerBoundRow
  failClosedPromotionWallRecorded :
    NSTriadCycleDefectLowerBoundRow

canonicalNSTriadCycleDefectLowerBoundRows :
  List NSTriadCycleDefectLowerBoundRow
canonicalNSTriadCycleDefectLowerBoundRows =
  exactQuadraticLowerBoundFormulaRecorded
  ∷ weightedDualNormDenominatorRecorded
  ∷ cycleDefectDistanceTermRecorded
  ∷ shellCarrierOracleTargetHandoffRecorded
  ∷ floorToFrameGapDependencyRecorded
  ∷ failClosedPromotionWallRecorded
  ∷ []

nstriadCycleDefectLowerBoundRowCount : Nat
nstriadCycleDefectLowerBoundRowCount =
  listLength canonicalNSTriadCycleDefectLowerBoundRows

nstriadCycleDefectLowerBoundRowCountIs6 :
  nstriadCycleDefectLowerBoundRowCount ≡ 6
nstriadCycleDefectLowerBoundRowCountIs6 = refl

data NSTriadCycleDefectLowerBoundGap : Set where
  shellCarrierTargetCocycleStillModelled :
    NSTriadCycleDefectLowerBoundGap
  enoughIndependentDefectiveCyclesStillMissing :
    NSTriadCycleDefectLowerBoundGap
  uniformCZeroFloorStillOpen :
    NSTriadCycleDefectLowerBoundGap
  floorToFrameDistributedResidualBridgeStillOpen :
    NSTriadCycleDefectLowerBoundGap
  theoremFullNSClayPromotionClosed :
    NSTriadCycleDefectLowerBoundGap

canonicalNSTriadCycleDefectLowerBoundGaps :
  List NSTriadCycleDefectLowerBoundGap
canonicalNSTriadCycleDefectLowerBoundGaps =
  shellCarrierTargetCocycleStillModelled
  ∷ enoughIndependentDefectiveCyclesStillMissing
  ∷ uniformCZeroFloorStillOpen
  ∷ floorToFrameDistributedResidualBridgeStillOpen
  ∷ theoremFullNSClayPromotionClosed
  ∷ []

nstriadCycleDefectLowerBoundGapCount : Nat
nstriadCycleDefectLowerBoundGapCount =
  listLength canonicalNSTriadCycleDefectLowerBoundGaps

nstriadCycleDefectLowerBoundGapCountIs5 :
  nstriadCycleDefectLowerBoundGapCount ≡ 5
nstriadCycleDefectLowerBoundGapCountIs5 = refl

canonicalWitnessTerm : String
canonicalWitnessTerm =
  "candidate-only receipt: the exact quadratic cycle-defect lower-bound law shape is recorded, but its shell-carrier instantiation and uniform floor consequences remain open"

organizationString : String
organizationString =
  "O: record the exact Wall 1 cycle-defect lower-bound law shape as a fail-closed quantitative receipt."

requirementString : String
requirementString =
  "R: expose the Δ_n(ψ)^2 / Σ(n_e^2 / w_e) lower-bound formula and its shell-carrier handoff without promoting Wall 1."

codeArtifactString : String
codeArtifactString =
  "C: export canonical rows, gaps, and ORCSLPGF text for the cycle-defect lower-bound law shape."

stateString : String
stateString =
  "S: the exact inequality is recorded, but the shell-carrier target cocycle and the uniform c0 > 0 floor are still open."

latticeString : String
latticeString =
  "L: exact cycle-defect lower-bound law -> shell-carrier target cocycle -> quantitative cocycle floor -> floor-to-frame bridge -> only then Wall 1 closure."

proposalString : String
proposalString =
  "P: use the exact cycle-defect lower-bound law as the hard quantitative core for Wall 1 instead of adding more proxy-only rhetoric."

governanceString : String
governanceString =
  "G: theorem, full-NS, and Clay promotion remain false."

failString : String
failString =
  "F: the missing evidence is a shell-carrier target cocycle with enough defective cycles to force a uniform floor and then a frame gap."

record NSTriadCycleDefectLowerBoundORCSLPGF : Set where
  constructor mkNSTriadCycleDefectLowerBoundORCSLPGF
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

open NSTriadCycleDefectLowerBoundORCSLPGF public

canonicalNSTriadCycleDefectLowerBoundORCSLPGF :
  NSTriadCycleDefectLowerBoundORCSLPGF
canonicalNSTriadCycleDefectLowerBoundORCSLPGF =
  mkNSTriadCycleDefectLowerBoundORCSLPGF
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

record NSTriadCycleDefectLowerBoundReceipt : Setω where
  constructor mkNSTriadCycleDefectLowerBoundReceipt
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadCycleDefectLowerBoundReceipt"

    witnessTerm :
      String
    witnessTermIsCanonical :
      witnessTerm ≡ canonicalWitnessTerm

    rows :
      List NSTriadCycleDefectLowerBoundRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadCycleDefectLowerBoundRows
    rowCount :
      Nat
    rowCountIsCanonical :
      rowCount ≡ nstriadCycleDefectLowerBoundRowCount

    gaps :
      List NSTriadCycleDefectLowerBoundGap
    gapsAreCanonical :
      gaps ≡ canonicalNSTriadCycleDefectLowerBoundGaps
    gapCount :
      Nat
    gapCountIsCanonical :
      gapCount ≡ nstriadCycleDefectLowerBoundGapCount

    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    failClosed :
      Bool
    failClosedIsTrue :
      failClosed ≡ true

    exactQuadraticLowerBoundLawRecorded :
      Bool
    exactQuadraticLowerBoundLawRecordedIsTrue :
      exactQuadraticLowerBoundLawRecorded ≡ true

    shellCarrierTargetCocycleConstructed :
      Bool
    shellCarrierTargetCocycleConstructedIsFalse :
      shellCarrierTargetCocycleConstructed ≡ false

    uniformCZeroFloorProved :
      Bool
    uniformCZeroFloorProvedIsFalse :
      uniformCZeroFloorProved ≡ false

    floorToFrameGapProved :
      Bool
    floorToFrameGapProvedIsFalse :
      floorToFrameGapProved ≡ false

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
      NSTriadCycleDefectLowerBoundORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadCycleDefectLowerBoundORCSLPGF

    statement :
      String
    statementIsCanonical :
      statement ≡
      "Candidate-only quantitative cycle-defect lower-bound receipt: the exact Δ_n(ψ)^2 / Σ(n_e^2 / w_e) law shape is recorded, but its shell-carrier target cocycle, uniform floor, and floor-to-frame consequences remain unproved."

open NSTriadCycleDefectLowerBoundReceipt public

canonicalNSTriadCycleDefectLowerBoundReceipt :
  NSTriadCycleDefectLowerBoundReceipt
canonicalNSTriadCycleDefectLowerBoundReceipt =
  mkNSTriadCycleDefectLowerBoundReceipt
    "NSTriadCycleDefectLowerBoundReceipt"
    refl
    canonicalWitnessTerm
    refl
    canonicalNSTriadCycleDefectLowerBoundRows
    refl
    nstriadCycleDefectLowerBoundRowCount
    refl
    canonicalNSTriadCycleDefectLowerBoundGaps
    refl
    nstriadCycleDefectLowerBoundGapCount
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
    canonicalNSTriadCycleDefectLowerBoundORCSLPGF
    refl
    "Candidate-only quantitative cycle-defect lower-bound receipt: the exact Δ_n(ψ)^2 / Σ(n_e^2 / w_e) law shape is recorded, but its shell-carrier target cocycle, uniform floor, and floor-to-frame consequences remain unproved."
    refl

cycleDefectLowerBoundReceiptIsCandidateOnly :
  candidateOnly canonicalNSTriadCycleDefectLowerBoundReceipt ≡ true
cycleDefectLowerBoundReceiptIsCandidateOnly = refl

cycleDefectLowerBoundReceiptIsFailClosed :
  failClosed canonicalNSTriadCycleDefectLowerBoundReceipt ≡ true
cycleDefectLowerBoundReceiptIsFailClosed = refl
