module DASHI.Physics.Closure.NSCalc12ExecutableRunReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Calc 12 executable run receipt.
--
-- Candidate-only receipt for the executable Calc 12 pipeline.  This
-- records the paired builder and route selector scripts together with the
-- emitted result artifact.  The receipt is non-promoting, theorem-free,
-- and proof-blocking remains false.

data NSCalc12ExecutableRunMode : Set where
  candidateOnlyExecutableRun :
    NSCalc12ExecutableRunMode

data NSCalc12ExecutableRunPromotion : Set where

nsCalc12ExecutableRunPromotionImpossibleHere :
  NSCalc12ExecutableRunPromotion →
  ⊥
nsCalc12ExecutableRunPromotionImpossibleHere ()

nsCalc12ExecutableRunSummary : String
nsCalc12ExecutableRunSummary =
  "Calc 12 executable run receipt: candidate-only pipeline with scripts/ns_clay_calc12_pair_builder.py, scripts/ns_clay_calc12_route_selector.py, and scripts/data/outputs/ns_clay_calc12_route_selector_real_N128_20260619.json; theorem authority false, proof blocking false, and Clay promotion false."

data NSCalc12ExecutableRunBoundary : Set where
  candidateOnlyPipelineRecorded :
    NSCalc12ExecutableRunBoundary

canonicalNSCalc12ExecutableRunBoundary : List NSCalc12ExecutableRunBoundary
canonicalNSCalc12ExecutableRunBoundary =
  candidateOnlyPipelineRecorded
  ∷ []

record NSCalc12ExecutableRunReceipt : Setω where
  field
    mode :
      NSCalc12ExecutableRunMode

    modeIsCandidateOnlyExecutableRun :
      mode ≡ candidateOnlyExecutableRun

    pairBuilderScript :
      String

    pairBuilderScriptIsCanonical :
      pairBuilderScript ≡ "scripts/ns_clay_calc12_pair_builder.py"

    routeSelectorScript :
      String

    routeSelectorScriptIsCanonical :
      routeSelectorScript ≡ "scripts/ns_clay_calc12_route_selector.py"

    resultArtifact :
      String

    resultArtifactIsCanonical :
      resultArtifact ≡ "scripts/data/outputs/ns_clay_calc12_route_selector_real_N128_20260619.json"

    proofBlocking :
      Bool

    proofBlockingIsFalse :
      proofBlocking ≡ false

    theoremAuthority :
      Bool

    theoremAuthorityIsFalse :
      theoremAuthority ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    summary :
      String

    summaryIsCanonical :
      summary ≡ nsCalc12ExecutableRunSummary

    promotionFlags :
      List NSCalc12ExecutableRunPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCalc12ExecutableRunReceipt public

canonicalNSCalc12ExecutableRunReceipt :
  NSCalc12ExecutableRunReceipt
canonicalNSCalc12ExecutableRunReceipt =
  record
    { mode =
        candidateOnlyExecutableRun
    ; modeIsCandidateOnlyExecutableRun =
        refl
    ; pairBuilderScript =
        "scripts/ns_clay_calc12_pair_builder.py"
    ; pairBuilderScriptIsCanonical =
        refl
    ; routeSelectorScript =
        "scripts/ns_clay_calc12_route_selector.py"
    ; routeSelectorScriptIsCanonical =
        refl
    ; resultArtifact =
        "scripts/data/outputs/ns_clay_calc12_route_selector_real_N128_20260619.json"
    ; resultArtifactIsCanonical =
        refl
    ; proofBlocking =
        false
    ; proofBlockingIsFalse =
        refl
    ; theoremAuthority =
        false
    ; theoremAuthorityIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; summary =
        nsCalc12ExecutableRunSummary
    ; summaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Calc 12 executable run is candidate-only"
        ∷ "Pair builder and route selector scripts are recorded explicitly"
        ∷ "The emitted JSON artifact is recorded as the run result"
        ∷ "Proof blocking, theorem authority, and Clay promotion all remain false"
        ∷ []
    }

canonicalNSCalc12ExecutableRunProofBlockingFalse :
  proofBlocking canonicalNSCalc12ExecutableRunReceipt ≡ false
canonicalNSCalc12ExecutableRunProofBlockingFalse =
  refl

canonicalNSCalc12ExecutableRunTheoremAuthorityFalse :
  theoremAuthority canonicalNSCalc12ExecutableRunReceipt ≡ false
canonicalNSCalc12ExecutableRunTheoremAuthorityFalse =
  refl

canonicalNSCalc12ExecutableRunClayPromotionFalse :
  clayPromotion canonicalNSCalc12ExecutableRunReceipt ≡ false
canonicalNSCalc12ExecutableRunClayPromotionFalse =
  refl
