module DASHI.Physics.Closure.NSPeriodicNearAmplitudeScalingObstruction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Homogeneity obstruction for an amplitude-uniform near estimate.
--
-- A trilinear tested nonlinearity is cubic in u, while viscous dissipation is
-- quadratic.  Doubling a fixed state shape therefore multiplies the two sides
-- by eight and four respectively.  This finite theorem does not choose the
-- missing smallness source; it records why admissibility/residual control is
-- mathematically necessary.
------------------------------------------------------------------------

data ScalingDegree : Set where
  quadratic cubic : ScalingDegree

powTwo : Nat → Nat
powTwo zero = 1
powTwo (suc n) = 2 * powTwo n

degree : ScalingDegree → Nat
degree quadratic = 2
degree cubic = 3

doublingFactor : ScalingDegree → Nat
doublingFactor kind = powTwo (degree kind)

quadraticDoublingFactor : doublingFactor quadratic ≡ 4
quadraticDoublingFactor = refl

cubicDoublingFactor : doublingFactor cubic ≡ 8
cubicDoublingFactor = refl

cubicRelativeToQuadratic :
  doublingFactor cubic ≡ 2 * doublingFactor quadratic
cubicRelativeToQuadratic = refl

record NearAmplitudeScalingCertificate : Set where
  field
    dissipation-factor : doublingFactor quadratic ≡ 4
    nonlinearity-factor : doublingFactor cubic ≡ 8
    relative-factor :
      doublingFactor cubic ≡ 2 * doublingFactor quadratic

nearAmplitudeScalingCertificate : NearAmplitudeScalingCertificate
nearAmplitudeScalingCertificate = record
  { dissipation-factor = quadraticDoublingFactor
  ; nonlinearity-factor = cubicDoublingFactor
  ; relative-factor = cubicRelativeToQuadratic
  }

nearAmplitudeScalingObstructionLevel : ProofLevel
nearAmplitudeScalingObstructionLevel = machineChecked
