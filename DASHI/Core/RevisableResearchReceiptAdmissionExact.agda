module DASHI.Core.RevisableResearchReceiptAdmissionExact where

-- Generic receipt firewall: Johl Brown with OpenAI ChatGPT assistance,
-- 2026-10-26. Reuses the existing ESD/SLR pattern without importing any
-- Digital ESD corpus, source audit, team project or institutional authority.
-- Source-written; independent kernel check pending.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

data ReceiptKind : Set where
  workerCompleted sourceAcquired repositoryResolved
    formalKernelVerified empiricalReviewed : ReceiptKind

data Authority : Set where
  candidateOnly formalTheorem empiricalFinding : Authority

-- The producer's identity is typed separately from its authority.
-- This predicate is a necessary *classification* condition; it does not
-- authenticate an external worker or checker.
data MayClaim : ReceiptKind → Authority → Set where
  workerCandidate : MayClaim workerCompleted candidateOnly
  sourceCandidate : MayClaim sourceAcquired candidateOnly
  repositoryCandidate : MayClaim repositoryResolved candidateOnly
  formalCandidate : MayClaim formalKernelVerified candidateOnly
  formalVerified : MayClaim formalKernelVerified formalTheorem
  empiricalCandidate : MayClaim empiricalReviewed candidateOnly
  empiricalVerified : MayClaim empiricalReviewed empiricalFinding

workerCannotClaimTheorem :
  MayClaim workerCompleted formalTheorem → ⊥
workerCannotClaimTheorem ()

repositoryCannotClaimTheorem :
  MayClaim repositoryResolved formalTheorem → ⊥
repositoryCannotClaimTheorem ()

sourceCannotClaimFinding :
  MayClaim sourceAcquired empiricalFinding → ⊥
sourceCannotClaimFinding ()

formalReceiptCannotClaimEmpiricalFinding :
  MayClaim formalKernelVerified empiricalFinding → ⊥
formalReceiptCannotClaimEmpiricalFinding ()

-- External verification is a separate witness, not a string or exit code.
record IndependentlyVerified {Evidence : Set}
    (verify : Evidence → Set) (evidence : Evidence) : Set where
  constructor independentlyVerified
  field
    verificationWitness : verify evidence

record AdmittedFormalResult {Evidence : Set}
    (verify : Evidence → Set) (evidence : Evidence) : Set where
  constructor admittedFormalResult
  field
    receiptClass : MayClaim formalKernelVerified formalTheorem
    independentCheck : IndependentlyVerified verify evidence

record AdmittedEmpiricalResult {Evidence : Set}
    (review : Evidence → Set) (evidence : Evidence) : Set where
  constructor admittedEmpiricalResult
  field
    receiptClass : MayClaim empiricalReviewed empiricalFinding
    independentReview : IndependentlyVerified review evidence

-- An untrusted label or a successful worker exit cannot construct either
-- admitted result without the externally supplied verification witness.
