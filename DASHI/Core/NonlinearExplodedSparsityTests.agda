module DASHI.Core.NonlinearExplodedSparsityTests where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Core.MinimalKernelAlgebra using (decodeSupportSign)
open import DASHI.Core.NonlinearExplodedSparsity

identityPartition : TritPartition Trit
identityPartition = record
  { classify = λ t → t
  ; NegativeRegion = λ t → t ≡ neg
  ; NeutralRegion = λ t → t ≡ zer
  ; PositiveRegion = λ t → t ≡ pos
  ; negativeExact = λ t → iff (λ p → p) (λ p → p)
  ; neutralExact = λ t → iff (λ p → p) (λ p → p)
  ; positiveExact = λ t → iff (λ p → p) (λ p → p)
  }

identityKernel : ThresholdKernel Bool Trit
identityKernel = record
  { localField = λ s x → s x
  ; partition = identityPartition
  }

sampleState : State Bool
sampleState false = zer
sampleState true = pos

identityKernelClosed : KernelClosed identityKernel sampleState
identityKernelClosed x = refl

sampleNeutralIsLowMargin :
  TritPartition.NeutralRegion identityPartition
    (ThresholdKernel.localField identityKernel sampleState false)
sampleNeutralIsLowMargin =
  closedNeutralHasNeutralMargin
    identityKernel sampleState identityKernelClosed false refl

samplePositiveIsPositiveMargin :
  TritPartition.PositiveRegion identityPartition
    (ThresholdKernel.localField identityKernel sampleState true)
samplePositiveIsPositiveMargin =
  closedPositiveHasPositiveMargin
    identityKernel sampleState identityKernelClosed true refl

sampleSatisfiesCSP : SatisfiesAllLocalConstraints identityKernel sampleState
sampleSatisfiesCSP = kernelClosed→CSP identityKernelClosed

------------------------------------------------------------------------
-- A genuinely adjacency-dependent two-node kernel cannot be represented
-- by any coordinate-only threshold/ReLU-like rule.
------------------------------------------------------------------------

swapField : State Bool → Bool → Trit
swapField s false = s true
swapField s true = s false

swapKernel : ThresholdKernel Bool Trit
swapKernel = record
  { localField = swapField
  ; partition = identityPartition
  }

leftState : State Bool
leftState false = neg
leftState true = zer

rightState : State Bool
rightState false = pos
rightState true = zer

neg≢pos : ¬ (neg ≡ pos)
neg≢pos ()

swapNonCoordinate : NonCoordinateWitness swapKernel
swapNonCoordinate = record
  { leftState = leftState
  ; rightState = rightState
  ; witnessNode = true
  ; sameAtom = refl
  ; differentOutput = neg≢pos
  }

swapHasNoCoordinateRepresentation : ¬ CoordinateRepresentation swapKernel
swapHasNoCoordinateRepresentation =
  nonCoordinateWitnessRulesOutCoordinateRepresentation swapNonCoordinate

------------------------------------------------------------------------
-- Exact support/sign explosion is lossless at each atom.
------------------------------------------------------------------------

sampleExplodedExact :
  decodeSupportSign (ExplodedAtom.supportSign (explodeAtom pos)) ≡
  ExplodedAtom.source (explodeAtom pos)
sampleExplodedExact = ExplodedAtom.exact (explodeAtom pos)
