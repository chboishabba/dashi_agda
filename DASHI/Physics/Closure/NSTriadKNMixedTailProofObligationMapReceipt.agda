module DASHI.Physics.Closure.NSTriadKNMixedTailProofObligationMapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadKNMixedTailSchurScalingReceipt as Scaling

------------------------------------------------------------------------
-- Candidate-only proof-obligation map for the mixed-tail K_N route.
--
-- The scaling receipt records what was observed.  This receipt records what
-- still has to be proved.  It is intentionally a dependency map only: no
-- analytic lemma, Navier-Stokes theorem, BKM exclusion, or Clay claim is
-- promoted here.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadKNMixedTailProofObligationStatus : Set where
  mixedTailProofObligationMapRecorded :
    NSTriadKNMixedTailProofObligationStatus

data NSTriadKNMixedTailProofObligation : Set where
  mixedTailSchurGapDissipationScaleObligation :
    NSTriadKNMixedTailProofObligation
  tailSubspaceCoercivityObligation :
    NSTriadKNMixedTailProofObligation
  bkmProjectionSmallnessObligation :
    NSTriadKNMixedTailProofObligation
  residenceTimeExclusionObligation :
    NSTriadKNMixedTailProofObligation

obligationInput : NSTriadKNMixedTailProofObligation → String
obligationInput mixedTailSchurGapDissipationScaleObligation =
  "input: finite-shell sparse-Schur telemetry from N=6,8,10,12 top-tail forced rows."
obligationInput tailSubspaceCoercivityObligation =
  "input: R_tail > c0 in the N=6,8,10,12 top-tail sparse-Schur rows."
obligationInput bkmProjectionSmallnessObligation =
  "input: BKM-tail projection squared remains tiny in the sampled mixed-tail rows."
obligationInput residenceTimeExclusionObligation =
  "input: dissipation telemetry D(N), Schur-gap telemetry q_gap(N), and the energy inequality shape nu int D(t) dt <= E0."

obligationTarget : NSTriadKNMixedTailProofObligation → String
obligationTarget mixedTailSchurGapDissipationScaleObligation =
  "target: prove q_gap(N) * D(N) >= c_mix > 0, or q_gap(N) >= N^(-2-epsilon) with D(N) near N^2."
obligationTarget tailSubspaceCoercivityObligation =
  "target: prove a uniform or asymptotic tail-only Rayleigh lower bound R_tail >= c_tail > c0."
obligationTarget bkmProjectionSmallnessObligation =
  "target: prove structural orthogonality or projection smallness for BKM-active stretching against the bad tail component."
obligationTarget residenceTimeExclusionObligation =
  "target: show mixed-tail bad intervals are summable or residence-limited along Navier-Stokes trajectories."

obligationMissingBridge : NSTriadKNMixedTailProofObligation → String
obligationMissingBridge mixedTailSchurGapDissipationScaleObligation =
  "missing: analytic lower bound for the sparse Schur gap, not just finite-shell telemetry."
obligationMissingBridge tailSubspaceCoercivityObligation =
  "missing: tail-only triad-operator geometry proving coercivity beyond the sampled forced-tail rows."
obligationMissingBridge bkmProjectionSmallnessObligation =
  "missing: continuous PDE bridge turning small finite-dimensional BKM proxy projection into a structural estimate."
obligationMissingBridge residenceTimeExclusionObligation =
  "missing: trajectory-level bridge connecting q_gap/D telemetry to BKM-relevant time sets."

record NSTriadKNMixedTailProofObligationRow : Set where
  field
    obligation :
      NSTriadKNMixedTailProofObligation
    input :
      String
    inputIsCanonical :
      input ≡ obligationInput obligation
    target :
      String
    targetIsCanonical :
      target ≡ obligationTarget obligation
    missingBridge :
      String
    missingBridgeIsCanonical :
      missingBridge ≡ obligationMissingBridge obligation

canonicalNSTriadKNMixedTailProofObligationRows :
  List NSTriadKNMixedTailProofObligationRow
canonicalNSTriadKNMixedTailProofObligationRows =
  record
    { obligation = mixedTailSchurGapDissipationScaleObligation
    ; input = obligationInput mixedTailSchurGapDissipationScaleObligation
    ; inputIsCanonical = refl
    ; target = obligationTarget mixedTailSchurGapDissipationScaleObligation
    ; targetIsCanonical = refl
    ; missingBridge = obligationMissingBridge mixedTailSchurGapDissipationScaleObligation
    ; missingBridgeIsCanonical = refl
    }
  ∷ record
    { obligation = tailSubspaceCoercivityObligation
    ; input = obligationInput tailSubspaceCoercivityObligation
    ; inputIsCanonical = refl
    ; target = obligationTarget tailSubspaceCoercivityObligation
    ; targetIsCanonical = refl
    ; missingBridge = obligationMissingBridge tailSubspaceCoercivityObligation
    ; missingBridgeIsCanonical = refl
    }
  ∷ record
    { obligation = bkmProjectionSmallnessObligation
    ; input = obligationInput bkmProjectionSmallnessObligation
    ; inputIsCanonical = refl
    ; target = obligationTarget bkmProjectionSmallnessObligation
    ; targetIsCanonical = refl
    ; missingBridge = obligationMissingBridge bkmProjectionSmallnessObligation
    ; missingBridgeIsCanonical = refl
    }
  ∷ record
    { obligation = residenceTimeExclusionObligation
    ; input = obligationInput residenceTimeExclusionObligation
    ; inputIsCanonical = refl
    ; target = obligationTarget residenceTimeExclusionObligation
    ; targetIsCanonical = refl
    ; missingBridge = obligationMissingBridge residenceTimeExclusionObligation
    ; missingBridgeIsCanonical = refl
    }
  ∷ []

nSTriadKNMixedTailProofObligationRowCount : Nat
nSTriadKNMixedTailProofObligationRowCount =
  listLength canonicalNSTriadKNMixedTailProofObligationRows

nSTriadKNMixedTailProofObligationRowCountIs4 :
  nSTriadKNMixedTailProofObligationRowCount ≡ 4
nSTriadKNMixedTailProofObligationRowCountIs4 =
  refl

data NSTriadKNMixedTailProofObligationOpenGap : Set where
  analyticSchurGapLowerBoundOpen :
    NSTriadKNMixedTailProofObligationOpenGap
  uniformTailRayleighCoercivityOpen :
    NSTriadKNMixedTailProofObligationOpenGap
  structuralBKMProjectionEstimateOpen :
    NSTriadKNMixedTailProofObligationOpenGap
  finiteShellTelemetryToPDETrajectoryBridgeOpen :
    NSTriadKNMixedTailProofObligationOpenGap
  residenceTimeBKMContradictionAssemblyOpen :
    NSTriadKNMixedTailProofObligationOpenGap
  noTheoremFullNSOrClayPromotion :
    NSTriadKNMixedTailProofObligationOpenGap

canonicalNSTriadKNMixedTailProofObligationOpenGaps :
  List NSTriadKNMixedTailProofObligationOpenGap
canonicalNSTriadKNMixedTailProofObligationOpenGaps =
  analyticSchurGapLowerBoundOpen
  ∷ uniformTailRayleighCoercivityOpen
  ∷ structuralBKMProjectionEstimateOpen
  ∷ finiteShellTelemetryToPDETrajectoryBridgeOpen
  ∷ residenceTimeBKMContradictionAssemblyOpen
  ∷ noTheoremFullNSOrClayPromotion
  ∷ []

nSTriadKNMixedTailProofObligationOpenGapCount : Nat
nSTriadKNMixedTailProofObligationOpenGapCount =
  listLength canonicalNSTriadKNMixedTailProofObligationOpenGaps

nSTriadKNMixedTailProofObligationOpenGapCountIs6 :
  nSTriadKNMixedTailProofObligationOpenGapCount ≡ 6
nSTriadKNMixedTailProofObligationOpenGapCountIs6 =
  refl

data NSTriadKNMixedTailProofObligationPromotion : Set where

promotionImpossibleHere :
  NSTriadKNMixedTailProofObligationPromotion → ⊥
promotionImpossibleHere ()

canonicalReceiptText : String
canonicalReceiptText =
  "Candidate-only proof-obligation map for the mixed-tail K_N route after the N=6,8,10,12 sparse-Schur scaling receipt."

canonicalScalingAnchorText : String
canonicalScalingAnchorText =
  "Evidence anchor: NSTriadKNMixedTailSchurScalingReceipt records q_gap ~ N^-2.198, D ~ N^1.985, stable D*q_gap telemetry, and false promotion flags."

canonicalOText : String
canonicalOText =
  "O: record the mixed-tail K_N proof-obligation map as a candidate-only dependency receipt."

canonicalRText : String
canonicalRText =
  "R: split the frontier into Schur-gap scale, tail coercivity, BKM projection smallness, and residence-time exclusion obligations."

canonicalCText : String
canonicalCText =
  "C: export obligation rows with input telemetry, target statement, missing bridge, source scaling receipt, open gaps, and false promotion flags."

canonicalSText : String
canonicalSText =
  "S: this is a proof-obligation map only; no listed target is discharged here."

canonicalLText : String
canonicalLText =
  "L: finite sparse-Schur telemetry -> named candidate obligations -> analytic lower bounds and PDE bridge still open."

canonicalPText : String
canonicalPText =
  "P: attack the diagonal-residue bridge first, then MixedTailSchurGapDissipationScale, BKM projection, and residence assembly."

canonicalGText : String
canonicalGText =
  "G: do not infer theorem, full-NS, BKM exclusion, or Clay promotion from this map."

canonicalFText : String
canonicalFText =
  "F: the map remains blocked by a uniform tail coercivity bound, a structural Schur residue estimate, projection smallness, and trajectory-level residence closure."

record NSTriadKNMixedTailProofObligationMapORCSLPGF : Set where
  constructor mkNSTriadKNMixedTailProofObligationMapORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ canonicalOText
    R : String
    RIsCanonical : R ≡ canonicalRText
    C : String
    CIsCanonical : C ≡ canonicalCText
    S : String
    SIsCanonical : S ≡ canonicalSText
    L : String
    LIsCanonical : L ≡ canonicalLText
    P : String
    PIsCanonical : P ≡ canonicalPText
    G : String
    GIsCanonical : G ≡ canonicalGText
    F : String
    FIsCanonical : F ≡ canonicalFText

canonicalNSTriadKNMixedTailProofObligationMapORCSLPGF :
  NSTriadKNMixedTailProofObligationMapORCSLPGF
canonicalNSTriadKNMixedTailProofObligationMapORCSLPGF =
  mkNSTriadKNMixedTailProofObligationMapORCSLPGF
    canonicalOText
    refl
    canonicalRText
    refl
    canonicalCText
    refl
    canonicalSText
    refl
    canonicalLText
    refl
    canonicalPText
    refl
    canonicalGText
    refl
    canonicalFText
    refl

record NSTriadKNMixedTailProofObligationMapReceipt : Setω where
  constructor mkNSTriadKNMixedTailProofObligationMapReceipt
  field
    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNMixedTailProofObligationMapReceipt"

    status :
      NSTriadKNMixedTailProofObligationStatus
    statusIsCanonical :
      status ≡ mixedTailProofObligationMapRecorded

    receiptText :
      String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    scalingAnchorText :
      String
    scalingAnchorTextIsCanonical :
      scalingAnchorText ≡ canonicalScalingAnchorText

    scalingReceiptTheoremPromoted :
      Bool
    scalingReceiptTheoremPromotedIsFalse :
      scalingReceiptTheoremPromoted ≡
        Scaling.theoremPromoted Scaling.canonicalNSTriadKNMixedTailSchurScalingReceipt

    scalingReceiptClayPromoted :
      Bool
    scalingReceiptClayPromotedIsFalse :
      scalingReceiptClayPromoted ≡
        Scaling.clayPromoted Scaling.canonicalNSTriadKNMixedTailSchurScalingReceipt

    obligationRows :
      List NSTriadKNMixedTailProofObligationRow
    obligationRowsAreCanonical :
      obligationRows ≡ canonicalNSTriadKNMixedTailProofObligationRows

    openGaps :
      List NSTriadKNMixedTailProofObligationOpenGap
    openGapsAreCanonical :
      openGaps ≡ canonicalNSTriadKNMixedTailProofObligationOpenGaps

    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    failClosed :
      Bool
    failClosedIsTrue :
      failClosed ≡ true

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted :
      Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    bkmExclusionProved :
      Bool
    bkmExclusionProvedIsFalse :
      bkmExclusionProved ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotionFlags :
      List NSTriadKNMixedTailProofObligationPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    orcslpgf :
      NSTriadKNMixedTailProofObligationMapORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadKNMixedTailProofObligationMapORCSLPGF

open NSTriadKNMixedTailProofObligationMapReceipt public

canonicalNSTriadKNMixedTailProofObligationMapReceipt :
  NSTriadKNMixedTailProofObligationMapReceipt
canonicalNSTriadKNMixedTailProofObligationMapReceipt =
  mkNSTriadKNMixedTailProofObligationMapReceipt
    "NSTriadKNMixedTailProofObligationMapReceipt"
    refl
    mixedTailProofObligationMapRecorded
    refl
    canonicalReceiptText
    refl
    canonicalScalingAnchorText
    refl
    false
    refl
    false
    refl
    canonicalNSTriadKNMixedTailProofObligationRows
    refl
    canonicalNSTriadKNMixedTailProofObligationOpenGaps
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
    []
    refl
    canonicalNSTriadKNMixedTailProofObligationMapORCSLPGF
    refl

proofObligationMapKeepsTheoremPromotedFalse :
  theoremPromoted canonicalNSTriadKNMixedTailProofObligationMapReceipt ≡ false
proofObligationMapKeepsTheoremPromotedFalse =
  refl

proofObligationMapKeepsFullNSPromotedFalse :
  fullNSPromoted canonicalNSTriadKNMixedTailProofObligationMapReceipt ≡ false
proofObligationMapKeepsFullNSPromotedFalse =
  refl

proofObligationMapKeepsBKMExclusionProvedFalse :
  bkmExclusionProved canonicalNSTriadKNMixedTailProofObligationMapReceipt ≡ false
proofObligationMapKeepsBKMExclusionProvedFalse =
  refl

proofObligationMapKeepsClayPromotedFalse :
  clayPromoted canonicalNSTriadKNMixedTailProofObligationMapReceipt ≡ false
proofObligationMapKeepsClayPromotedFalse =
  refl
