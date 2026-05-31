module DASHI.Physics.Closure.NSH118GlobalRegularityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- H^{11/8} global regularity candidate for carrier-structured data.
--
-- This receipt records the A2 candidate theorem surface only.  The six
-- proof-sketch steps are present as data, the status is candidate theorem,
-- and the only named remaining gap is uniqueness/stability of the limit.
-- It deliberately makes no Clay, arbitrary-data, global-terminal, or
-- terminal-promotion claim.

data NSH118TheoremStatus : Set where
  candidateTheorem :
    NSH118TheoremStatus

data NSH118ProofSketchStep : Set where
  carrierStructuredH118InitialData :
    NSH118ProofSketchStep

  finiteDepthSmoothCarrierApproximants :
    NSH118ProofSketchStep

  uniformH118A-prioriBound :
    NSH118ProofSketchStep

  compactnessAndLimitExtraction :
    NSH118ProofSketchStep

  nonlinearTermPassageToLimit :
    NSH118ProofSketchStep

  limitInheritsGlobalH118Regularity :
    NSH118ProofSketchStep

canonicalNSH118ProofSketchSteps :
  List NSH118ProofSketchStep
canonicalNSH118ProofSketchSteps =
  carrierStructuredH118InitialData
  ∷ finiteDepthSmoothCarrierApproximants
  ∷ uniformH118A-prioriBound
  ∷ compactnessAndLimitExtraction
  ∷ nonlinearTermPassageToLimit
  ∷ limitInheritsGlobalH118Regularity
  ∷ []

data NSH118RemainingGap : Set where
  uniquenessStabilityOfLimit :
    NSH118RemainingGap

canonicalNSH118RemainingGaps :
  List NSH118RemainingGap
canonicalNSH118RemainingGaps =
  uniquenessStabilityOfLimit
  ∷ []

data NSH118GlobalRegularityPromotion : Set where

nsH118GlobalRegularityPromotionImpossibleHere :
  NSH118GlobalRegularityPromotion →
  ⊥
nsH118GlobalRegularityPromotionImpossibleHere ()

nsH118GlobalRegularityStatement : String
nsH118GlobalRegularityStatement =
  "Candidate theorem: for carrier-structured initial data in H^{11/8}, the six-step route records carrier-structured H^{11/8} data, finite-depth smooth carrier approximants, a uniform H^{11/8} a-priori bound, compactness and limit extraction, nonlinear passage to the limit, and inheritance of global H^{11/8} regularity by the limit.  The remaining gap is uniqueness/stability of the limit.  This is not a Clay Navier-Stokes proof, not an arbitrary-data theorem, and not a global terminal promotion."

record NSH118GlobalRegularityReceipt : Setω where
  field
    status :
      NSH118TheoremStatus

    statusIsCandidateTheorem :
      status ≡ candidateTheorem

    carrierStructuredInitialData :
      Bool

    carrierStructuredInitialDataIsTrue :
      carrierStructuredInitialData ≡ true

    sobolevNumerator :
      Nat

    sobolevNumeratorIs11 :
      sobolevNumerator ≡ 11

    sobolevDenominator :
      Nat

    sobolevDenominatorIs8 :
      sobolevDenominator ≡ 8

    proofSketchSteps :
      List NSH118ProofSketchStep

    proofSketchStepsAreCanonical :
      proofSketchSteps ≡ canonicalNSH118ProofSketchSteps

    sixProofSketchStepsRecorded :
      Bool

    sixProofSketchStepsRecordedIsTrue :
      sixProofSketchStepsRecorded ≡ true

    finiteDepthSmoothCarrierApproximantsRecorded :
      Bool

    finiteDepthSmoothCarrierApproximantsRecordedIsTrue :
      finiteDepthSmoothCarrierApproximantsRecorded ≡ true

    uniformH118BoundRecorded :
      Bool

    uniformH118BoundRecordedIsTrue :
      uniformH118BoundRecorded ≡ true

    compactnessAndLimitExtractionRecorded :
      Bool

    compactnessAndLimitExtractionRecordedIsTrue :
      compactnessAndLimitExtractionRecorded ≡ true

    nonlinearPassageRecorded :
      Bool

    nonlinearPassageRecordedIsTrue :
      nonlinearPassageRecorded ≡ true

    limitGlobalH118RegularityRecorded :
      Bool

    limitGlobalH118RegularityRecordedIsTrue :
      limitGlobalH118RegularityRecorded ≡ true

    remainingGaps :
      List NSH118RemainingGap

    remainingGapsAreCanonical :
      remainingGaps ≡ canonicalNSH118RemainingGaps

    uniquenessStabilityOfLimitClosed :
      Bool

    uniquenessStabilityOfLimitClosedIsFalse :
      uniquenessStabilityOfLimitClosed ≡ false

    uniquenessStabilityOfLimitRemainingGap :
      Bool

    uniquenessStabilityOfLimitRemainingGapIsTrue :
      uniquenessStabilityOfLimitRemainingGap ≡ true

    nsRegularityAt11/8 :
      NSH118TheoremStatus

    nsRegularityAt11/8IsCandidateTheorem :
      nsRegularityAt11/8 ≡ candidateTheorem

    arbitraryDataTheoremPromoted :
      Bool

    arbitraryDataTheoremPromotedIsFalse :
      arbitraryDataTheoremPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    globalTerminalPromotion :
      Bool

    globalTerminalPromotionIsFalse :
      globalTerminalPromotion ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsH118GlobalRegularityStatement

    promotionFlags :
      List NSH118GlobalRegularityPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSH118GlobalRegularityReceipt public

canonicalNSH118GlobalRegularityReceipt :
  NSH118GlobalRegularityReceipt
canonicalNSH118GlobalRegularityReceipt =
  record
    { status =
        candidateTheorem
    ; statusIsCandidateTheorem =
        refl
    ; carrierStructuredInitialData =
        true
    ; carrierStructuredInitialDataIsTrue =
        refl
    ; sobolevNumerator =
        11
    ; sobolevNumeratorIs11 =
        refl
    ; sobolevDenominator =
        8
    ; sobolevDenominatorIs8 =
        refl
    ; proofSketchSteps =
        canonicalNSH118ProofSketchSteps
    ; proofSketchStepsAreCanonical =
        refl
    ; sixProofSketchStepsRecorded =
        true
    ; sixProofSketchStepsRecordedIsTrue =
        refl
    ; finiteDepthSmoothCarrierApproximantsRecorded =
        true
    ; finiteDepthSmoothCarrierApproximantsRecordedIsTrue =
        refl
    ; uniformH118BoundRecorded =
        true
    ; uniformH118BoundRecordedIsTrue =
        refl
    ; compactnessAndLimitExtractionRecorded =
        true
    ; compactnessAndLimitExtractionRecordedIsTrue =
        refl
    ; nonlinearPassageRecorded =
        true
    ; nonlinearPassageRecordedIsTrue =
        refl
    ; limitGlobalH118RegularityRecorded =
        true
    ; limitGlobalH118RegularityRecordedIsTrue =
        refl
    ; remainingGaps =
        canonicalNSH118RemainingGaps
    ; remainingGapsAreCanonical =
        refl
    ; uniquenessStabilityOfLimitClosed =
        false
    ; uniquenessStabilityOfLimitClosedIsFalse =
        refl
    ; uniquenessStabilityOfLimitRemainingGap =
        true
    ; uniquenessStabilityOfLimitRemainingGapIsTrue =
        refl
    ; nsRegularityAt11/8 =
        candidateTheorem
    ; nsRegularityAt11/8IsCandidateTheorem =
        refl
    ; arbitraryDataTheoremPromoted =
        false
    ; arbitraryDataTheoremPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; globalTerminalPromotion =
        false
    ; globalTerminalPromotionIsFalse =
        refl
    ; statement =
        nsH118GlobalRegularityStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "status = candidate theorem"
        ∷ "nsRegularityAt11/8 = candidate theorem"
        ∷ "carrier-structured initial data in H^{11/8} only"
        ∷ "six proof-sketch steps are recorded"
        ∷ "remaining gap = uniqueness/stability of limit"
        ∷ "No Clay Navier-Stokes promotion is made"
        ∷ "No global terminal promotion is made"
        ∷ []
    }

canonicalNSRegularityAt11/8IsCandidateTheorem :
  nsRegularityAt11/8 canonicalNSH118GlobalRegularityReceipt
  ≡
  candidateTheorem
canonicalNSRegularityAt11/8IsCandidateTheorem =
  refl

canonicalNSH118RemainingGapIsUniquenessStability :
  remainingGaps canonicalNSH118GlobalRegularityReceipt
  ≡
  canonicalNSH118RemainingGaps
canonicalNSH118RemainingGapIsUniquenessStability =
  refl

nsH118GlobalRegularityDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSH118GlobalRegularityReceipt ≡ false
nsH118GlobalRegularityDoesNotPromoteClay =
  refl

nsH118GlobalRegularityNoPromotion :
  NSH118GlobalRegularityPromotion →
  ⊥
nsH118GlobalRegularityNoPromotion =
  nsH118GlobalRegularityPromotionImpossibleHere
