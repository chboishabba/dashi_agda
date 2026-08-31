module DASHI.Mathematics.NumberTheory.DiophantineTupleDPrimeSquare2026ClaimAuditExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

-- Source-bounded interface for the August 2026 D(p^2)-tuple Problem 5.6
-- announcement.  The advertised numerical statement is kept separate from
-- an Agda proof of the Diophantine argument.

data ClaimStage : Set where
  authorAnnouncement : ClaimStage
  manuscriptRecovered : ClaimStage
  proofReconstructed : ClaimStage
  kernelChecked : ClaimStage
  independentlyReviewed : ClaimStage

record DPrimeSquareProblem : Set where
  field
    prime : Nat
    tupleSize : Nat
    dProperty : Set

-- The reported strict upper threshold is 2^123.  We record it as a closed Nat
-- datum without asserting that every D(p^2)-tuple satisfies it.
pow2 : Nat -> Nat
pow2 0 = 1
pow2 (suc n) = 2 * pow2 n

reportedThreshold : Nat
reportedThreshold = pow2 123

record ReportedAbsoluteBound : Set where
  field
    stage : ClaimStage
    threshold : Nat
    thresholdIsReportedValue : threshold ≡ reportedThreshold

record ProvenAbsoluteBound : Set where
  field
    report : ReportedAbsoluteBound
    mathematicalProof : Set
    checkedStatementMatchesProblem56 : Set

announcementNotKernelCheck : authorAnnouncement ≡ kernelChecked -> ⊥
announcementNotKernelCheck ()

manuscriptNotIndependentReview : manuscriptRecovered ≡ independentlyReviewed -> ⊥
manuscriptNotIndependentReview ()

-- In particular, the existence of a ReportedAbsoluteBound is not definitionally
-- a ProvenAbsoluteBound.  A proof reconstruction and exact statement match are
-- additional obligations.
