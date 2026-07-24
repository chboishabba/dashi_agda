module DASHI.Cognition.PNF.CandidateInvalidation where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.EventAlgebra as PNF

data InvalidationGround : Set where
  missingSpan incompatibleRole impossibleTemporalScope : InvalidationGround
  incompatibleEntityType wrongJurisdiction excessAuthority : InvalidationGround
  failedTypedMeet invalidTranslationTransport : InvalidationGround

record PNFInvalidationReceipt : Set where
  constructor pnfInvalidationReceipt
  field
    originalCandidate : PNF.CandidatePNF
    grounds : List InvalidationGround
    explanation : String
    invalidatedCandidate : PNF.CandidatePNF
    invalidatedCandidateIsInvalid :
      PNF.validity invalidatedCandidate ≡ PNF.invalid

open PNFInvalidationReceipt public

invalidateCandidate :
  PNF.CandidatePNF →
  List InvalidationGround →
  String →
  PNFInvalidationReceipt
invalidateCandidate candidate grounds explanation =
  pnfInvalidationReceipt
    candidate
    grounds
    explanation
    (PNF.candidatePNF
      (PNF.event candidate)
      PNF.invalid
      explanation
      true
      refl)
    refl

invalidatedCannotBeAdmitted :
  (receipt : PNFInvalidationReceipt) →
  PNF.validity (invalidatedCandidate receipt) ≡ PNF.admissible →
  ⊥
invalidatedCannotBeAdmitted receipt proof =
  PNF.invalidIsNotAdmissible
    (Agda.Builtin.Equality.trans
      (Agda.Builtin.Equality.sym (invalidatedCandidateIsInvalid receipt))
      proof)
