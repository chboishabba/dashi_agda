module DASHI.Physics.Closure.NSPeriodicNormalizedBoundaryCandidateTuple where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact rational-data representation of the finite common-tuple candidate.
--
-- The diagnostic candidate is
--   gamma* = 7/100,
--   rho*   = 64/100,
--   eta*   = 36/100,
--   M^2    = 45.
--
-- Keeping numerators and a common denominator avoids floating-point values in
-- the Agda surface.  This module proves only exact scalar bookkeeping; the
-- finite search is not promoted into a Dini derivative theorem.
------------------------------------------------------------------------

record NormalizedBoundaryCandidateTuple : Set where
  field
    gammaNumerator gammaDenominator : Nat
    packetFractionNumerator offPacketNumerator fractionDenominator : Nat
    sizeSquaredCeiling : Nat

    packetAndOffPartition :
      packetFractionNumerator + offPacketNumerator ≡ fractionDenominator

open NormalizedBoundaryCandidateTuple public

selectedNormalizedBoundaryCandidate : NormalizedBoundaryCandidateTuple
selectedNormalizedBoundaryCandidate = record
  { gammaNumerator = 7
  ; gammaDenominator = 100
  ; packetFractionNumerator = 64
  ; offPacketNumerator = 36
  ; fractionDenominator = 100
  ; sizeSquaredCeiling = 45
  ; packetAndOffPartition = refl
  }

selectedPacketOffPartition :
  packetFractionNumerator selectedNormalizedBoundaryCandidate
  + offPacketNumerator selectedNormalizedBoundaryCandidate
  ≡ fractionDenominator selectedNormalizedBoundaryCandidate
selectedPacketOffPartition =
  packetAndOffPartition selectedNormalizedBoundaryCandidate

selectedGammaNumerator :
  gammaNumerator selectedNormalizedBoundaryCandidate ≡ 7
selectedGammaNumerator = refl

selectedGammaDenominator :
  gammaDenominator selectedNormalizedBoundaryCandidate ≡ 100
selectedGammaDenominator = refl

selectedPacketFractionNumerator :
  packetFractionNumerator selectedNormalizedBoundaryCandidate ≡ 64
selectedPacketFractionNumerator = refl

selectedOffPacketNumerator :
  offPacketNumerator selectedNormalizedBoundaryCandidate ≡ 36
selectedOffPacketNumerator = refl

selectedSizeSquaredCeiling :
  sizeSquaredCeiling selectedNormalizedBoundaryCandidate ≡ 45
selectedSizeSquaredCeiling = refl

------------------------------------------------------------------------
-- Status: exact tuple arithmetic is checked.  The continuum PDE signs remain
-- unpromoted and must be proved for the real-carrier interpretation of this
-- tuple (or for a different tuple if later falsification rejects this one).
------------------------------------------------------------------------

normalizedBoundaryCandidateTupleAssemblyLevel : ProofLevel
normalizedBoundaryCandidateTupleAssemblyLevel = machineChecked
