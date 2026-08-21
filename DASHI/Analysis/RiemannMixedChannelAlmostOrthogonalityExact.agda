module DASHI.Analysis.RiemannMixedChannelAlmostOrthogonalityExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Exact nonnegative bookkeeping for the only sign-indefinite loss exposed by
-- `RiemannWeilPairKernelFrobeniusExact`:
--
--   N_uv = (a_u . d_v)^2 + (b_u . c_v)^2.
--
-- The analytic frontier is to show that the aggregate mixed-channel budget
-- cannot absorb the positive diagonal Hermitian excess.  Here that statement
-- is represented as an explicit residual/margin certificate, never assumed by
-- arithmetic subtraction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

record MixedChannelGlobalLedger : Set where
  constructor mixedChannelGlobalLedger
  field
    positiveDiagonalEnergy : Nat
    mixedInterferenceBudget : Nat
    retainedGlobalExcess : Nat
    interferenceDecomposition :
      mixedInterferenceBudget + retainedGlobalExcess ≡ positiveDiagonalEnergy

open MixedChannelGlobalLedger public

record PairInsideDiagonalLedger (g : MixedChannelGlobalLedger) : Set where
  constructor pairInsideDiagonalLedger
  field
    targetPairDefect : Nat
    otherDiagonalEnergy : Nat
    pairInsideDiagonal :
      targetPairDefect + otherDiagonalEnergy ≡ positiveDiagonalEnergy g

open PairInsideDiagonalLedger public

-- Strong local almost-orthogonality certificate: all mixed interference can be
-- paid from the non-target diagonal reservoir, leaving an explicit margin.
record PairAlmostOrthogonality
  (g : MixedChannelGlobalLedger)
  (p : PairInsideDiagonalLedger g) : Set where
  constructor pairAlmostOrthogonality
  field
    orthogonalityMargin : Nat
    mixedPlusMarginIsOtherDiagonal :
      mixedInterferenceBudget g + orthogonalityMargin ≡ otherDiagonalEnergy p

open PairAlmostOrthogonality public

-- The precise target conclusion is retained as a certificate rather than a
-- hidden subtraction: retained global excess contains the target pair plus the
-- unused almost-orthogonality margin.
record RetainedPairCertificate
  (g : MixedChannelGlobalLedger)
  (p : PairInsideDiagonalLedger g) : Set where
  constructor retainedPairCertificate
  field
    retainedMargin : Nat
    retainedContainsPair :
      targetPairDefect p + retainedMargin ≡ retainedGlobalExcess g

record AlmostOrthogonalityProducer : Set₁ where
  field
    ZeroPair : Set
    diagonalHermitianExcess : ZeroPair → Nat
    mixedCrossBudget : ZeroPair → ZeroPair → Nat
    aggregateDiagonalEnergy : Nat
    aggregateMixedBudget : Nat
    retainedExcess : Nat
    globalLedger : MixedChannelGlobalLedger
    targetPairEmbedding : ZeroPair → PairInsideDiagonalLedger globalLedger
    analyticInterferenceDomination :
      (rho : ZeroPair) →
      Set

record MixedChannelAlmostOrthogonalityBoundary : Set where
  field
    mixedInterferenceLedgerConstructed : Bool
    targetPairInsideDiagonalLedgerConstructed : Bool
    retainedPairCertificateSurfaceConstructed : Bool
    sourceMixedChannelIdentified : Bool
    actualZetaCrossSumEstimatedHere : Bool
    almostOrthogonalityProvedForZetaHere : Bool
    diagonalExcessDominatesInterferenceForZetaHere : Bool

mixedChannelAlmostOrthogonalityBoundary : MixedChannelAlmostOrthogonalityBoundary
mixedChannelAlmostOrthogonalityBoundary = record
  { mixedInterferenceLedgerConstructed = true
  ; targetPairInsideDiagonalLedgerConstructed = true
  ; retainedPairCertificateSurfaceConstructed = true
  ; sourceMixedChannelIdentified = true
  ; actualZetaCrossSumEstimatedHere = false
  ; almostOrthogonalityProvedForZetaHere = false
  ; diagonalExcessDominatesInterferenceForZetaHere = false
  }
