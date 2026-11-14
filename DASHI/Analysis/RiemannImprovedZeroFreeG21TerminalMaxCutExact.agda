module DASHI.Analysis.RiemannImprovedZeroFreeG21TerminalMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannImprovedZeroFreeHalfPlaneDonorExact as Donor
import DASHI.Analysis.RiemannImprovedZeroFreeG21UniformGapExact as Gap
import DASHI.Analysis.RiemannG21LeanHyperbolicMonotonicityReceiptBoundary as Mono
import DASHI.Analysis.RiemannG21LeanAtomicTP2ReceiptBoundary as TP2
import DASHI.Analysis.RiemannG21ParityMinorAnalyticFrontierExact as Historical

------------------------------------------------------------------------
-- Terminal recut after the improved zero-free donor and the new Lean-side
-- scalar/pointwise proof candidates.
--
-- Historical G21 source should remain historically accurate: it records what
-- was paid on its own proof graph.  This module is the new branch-local status
-- owner and therefore distinguishes
--
--   source-written external/cross-prover candidate
--
-- from
--
--   Agda theorem imported/proved on this graph.
--
-- The max-cut is now:
--
-- external improved zeta zero-free theorem
--   -> exact same-zeta attachment                         [PENDING]
--   -> a <= 187479/500000, p-a > 1/8                    [compiler written]
--
-- Lean x*tanh/x*coth strict monotonicity candidates      [SOURCE-WRITTEN]
--   -> Lean sinh/cosh atomic TP2 candidates              [SOURCE-WRITTEN]
--   -> Agda/cross-prover transport                       [PENDING]
--   -> actual taper-weighted continuum moment signs      [OPEN]
--   -> exact six-term remainder < cubic determinant gap  [OPEN]
--   -> finite even+odd parity minors                     [OPEN]
--   -> nuisance-aware pole-quotient transversality       [OPEN]
--   -> prime-pair relational lane / terminal RH          [OPEN]
------------------------------------------------------------------------

record ImprovedZeroFreeG21TerminalBoundary : Set where
  constructor improved-zero-free-g21-terminal-boundary
  field
    externalImprovedZeroFreeSourcePinned : Bool
    externalImprovedZeroFreeSourcePinnedIsTrue :
      externalImprovedZeroFreeSourcePinned ≡ true

    exactSameZetaExternalAttachmentPaid : Bool
    exactSameZetaExternalAttachmentPaidIsFalse :
      exactSameZetaExternalAttachmentPaid ≡ false

    safeRationalTargetCapCompilerPaid : Bool
    safeRationalTargetCapCompilerPaidIsTrue :
      safeRationalTargetCapCompilerPaid ≡ true

    uniformPoleGapCompilerPaid : Bool
    uniformPoleGapCompilerPaidIsTrue : uniformPoleGapCompilerPaid ≡ true

    uniformPoleGapStrictlyExceedsOneEighth : Bool
    uniformPoleGapStrictlyExceedsOneEighthIsTrue :
      uniformPoleGapStrictlyExceedsOneEighth ≡ true

    scaledHyperbolicLeanCandidatesAvailable : Bool
    scaledHyperbolicLeanCandidatesAvailableIsTrue :
      scaledHyperbolicLeanCandidatesAvailable ≡ true

    atomicHyperbolicTP2LeanCandidateAvailable : Bool
    atomicHyperbolicTP2LeanCandidateAvailableIsTrue :
      atomicHyperbolicTP2LeanCandidateAvailable ≡ true

    exactHeadLeanKernelChecked : Bool
    exactHeadLeanKernelCheckedIsFalse : exactHeadLeanKernelChecked ≡ false

    hyperbolicCandidatesImportedIntoAgda : Bool
    hyperbolicCandidatesImportedIntoAgdaIsFalse :
      hyperbolicCandidatesImportedIntoAgda ≡ false

    genericTP2MomentCompositionAlreadyAvailable : Bool
    genericTP2MomentCompositionAlreadyAvailableIsTrue :
      genericTP2MomentCompositionAlreadyAvailable ≡ true

    actualContinuumMomentSignsPaid : Bool
    actualContinuumMomentSignsPaidIsFalse : actualContinuumMomentSignsPaid ≡ false

    exactSixTermRemainderDecompositionAlreadyAvailable : Bool
    exactSixTermRemainderDecompositionAlreadyAvailableIsTrue :
      exactSixTermRemainderDecompositionAlreadyAvailable ≡ true

    directRemainderBelowDeterminantMarginPaid : Bool
    directRemainderBelowDeterminantMarginPaidIsFalse :
      directRemainderBelowDeterminantMarginPaid ≡ false

    finiteRadiusParityMinorsPaid : Bool
    finiteRadiusParityMinorsPaidIsFalse : finiteRadiusParityMinorsPaid ≡ false

    poleQuotientTransversalityPaid : Bool
    poleQuotientTransversalityPaidIsFalse :
      poleQuotientTransversalityPaid ≡ false

    signedA1A2BProducerPaidByExternalDonor : Bool
    signedA1A2BProducerPaidByExternalDonorIsFalse :
      signedA1A2BProducerPaidByExternalDonor ≡ false

    riemannHypothesisDerived : Bool
    riemannHypothesisDerivedIsFalse : riemannHypothesisDerived ≡ false

    terminalReading : String

canonicalImprovedZeroFreeG21TerminalBoundary : ImprovedZeroFreeG21TerminalBoundary
canonicalImprovedZeroFreeG21TerminalBoundary =
  improved-zero-free-g21-terminal-boundary
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The improved Liu/OpenAI zero-free theorem is now represented by a conservative exact rational consumer cap and yields a conditional G21 pole/off-line gap >1/8, but its same-zeta theorem term is not imported into Agda. Lean now has source-written candidates for both scaled hyperbolic monotonicity leaves and both atomic sinh/cosh strict-TP2 determinants; exact-head kernel checking and Agda transport remain pending. Historical G21 already owns the generic TP2->moment composition shape, cubic determinant factorization, exact six-term remainder decomposition and parity block reduction. Therefore the first substantive analytic leaf after transport is the actual taper-weighted continuum even/odd moment sign, followed by direct remainder-below-margin, finite parity minors and nuisance-aware pole-quotient transversality. The external donor does not pay DASHI A1/A2/Route-B signed producers and RH is not derived."

historicalParityFrontier : Historical.ParityAnalyticFrontierBoundary
historicalParityFrontier = Historical.canonicalParityAnalyticFrontierBoundary

donorBoundary : Donor.ImprovedZeroFreeDonorBoundary
donorBoundary = Donor.canonicalImprovedZeroFreeDonorBoundary

gapBoundary : Gap.G21UniformPoleGapBoundary
gapBoundary = Gap.canonicalG21UniformPoleGapBoundary

monotonicityReceipt : Mono.LeanHyperbolicMonotonicityReceiptBoundary
monotonicityReceipt = Mono.canonicalLeanHyperbolicMonotonicityReceiptBoundary

atomicTP2Receipt : TP2.LeanAtomicTP2ReceiptBoundary
atomicTP2Receipt = TP2.canonicalLeanAtomicTP2ReceiptBoundary
