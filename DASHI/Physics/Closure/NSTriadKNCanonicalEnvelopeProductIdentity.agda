module DASHI.Physics.Closure.NSTriadKNCanonicalEnvelopeProductIdentity where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitFoldEquality as Fold
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- Canonical orbit blocks and their exact unsigned envelope.
------------------------------------------------------------------------

canonicalBlockContributions :
  {A : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (same? : A → A → Agda.Builtin.Bool.Bool) →
  (A → Scalar.Scalar (Algebra.orderedScalar K)) →
  List A → List (Scalar.Scalar (Algebra.orderedScalar K))
canonicalBlockContributions K same? f [] = []
canonicalBlockContributions K same? f (pivot ∷ xs) =
  Scalar._+_ S (f pivot)
    (Fold.sumBy S f (Fold.relatedTail same? pivot xs)) ∷
  canonicalBlockContributions K same? f
    (Fold.unrelatedTail same? pivot xs)
  where
  S = Algebra.orderedScalar K

sumCanonicalBlockContributions :
  {A : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (same? : A → A → Agda.Builtin.Bool.Bool) →
  (f : A → Scalar.Scalar (Algebra.orderedScalar K)) →
  (xs : List A) →
  Fold.sumBy (Algebra.orderedScalar K) (λ x → x)
    (canonicalBlockContributions K same? f xs) ≡
  Fold.canonicalFoldBy K same? f xs
sumCanonicalBlockContributions K same? f [] = refl
sumCanonicalBlockContributions K same? f (pivot ∷ xs) =
  cong (Scalar._+_ S block)
    (sumCanonicalBlockContributions K same? f
      (Fold.unrelatedTail same? pivot xs))
  where
  S = Algebra.orderedScalar K
  block = Scalar._+_ S (f pivot)
    (Fold.sumBy S f (Fold.relatedTail same? pivot xs))

canonicalOrbitPacketContributions :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (M R : Nat) →
  Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M →
  Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K) →
  List (Scalar.Scalar (Algebra.orderedScalar K))
canonicalOrbitPacketContributions K M R z T =
  canonicalBlockContributions K Fold.sameZeroSumOrbit?
    (Energy.weightedZeroSumTriadContribution S M z T)
    (Fold.fullCutoffZeroSumWitnesses R)
  where
  S = Algebra.orderedScalar K

canonicalPacketTransferQK :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (M R : Nat) →
  Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M →
  Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K)
canonicalPacketTransferQK K M R z T =
  Fold.sumBy S (λ x → x)
    (canonicalOrbitPacketContributions K M R z T)
  where
  S = Algebra.orderedScalar K

canonicalAbsoluteEnvelopeAK :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (M R : Nat) →
  Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M →
  Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K)
canonicalAbsoluteEnvelopeAK K M R z T =
  Fold.sumBy S (Scalar.abs S)
    (canonicalOrbitPacketContributions K M R z T)
  where
  S = Algebra.orderedScalar K

canonicalPacketTransferQKEqualsOrderedGalerkin :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (M R : Nat) →
  (z : Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M) →
  (T : Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  canonicalPacketTransferQK K M R z T ≡
  Fold.orderedGalerkinPacketTransferSum K M R z T
canonicalPacketTransferQKEqualsOrderedGalerkin K M R z T =
  trans
    (sumCanonicalBlockContributions K Fold.sameZeroSumOrbit?
      (Energy.weightedZeroSumTriadContribution S M z T)
      (Fold.fullCutoffZeroSumWitnesses R))
    (Fold.canonicalRegroupedEqualsOrderedGalerkin K M R z T)
  where
  S = Algebra.orderedScalar K

------------------------------------------------------------------------
-- Explicit nonzero reciprocal convention.
--
-- The finite identity needs no completeness or limiting argument.  It needs
-- only a reciprocal for the two denominators and a proof that a nonzero scalar
-- cancels its reciprocal.  Zero-denominator behaviour remains intentionally
-- unspecified and cannot be used to manufacture a physical ratio.
------------------------------------------------------------------------

record ExactReciprocalAuthority
    (K : Algebra.ExactOrderedCommutativeRing) : Set₁ where
  field
    reciprocal :
      Scalar.Scalar (Algebra.orderedScalar K) →
      Scalar.Scalar (Algebra.orderedScalar K)
    reciprocalCancelsRight :
      (x : Scalar.Scalar (Algebra.orderedScalar K)) →
      Scalar.Nonzero (Algebra.orderedScalar K) x →
      Scalar._*_ (Algebra.orderedScalar K) x (reciprocal x) ≡
      Scalar.one (Algebra.orderedScalar K)

open ExactReciprocalAuthority public

viscousRate2NuD :
  (K : Algebra.ExactOrderedCommutativeRing) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K)
viscousRate2NuD K nu D =
  Scalar._*_ S
    (Scalar._*_ S (Scalar.natToScalar S 2) nu)
    D
  where
  S = Algebra.orderedScalar K

positivePacketInput :
  (K : Algebra.ExactOrderedCommutativeRing) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K)
positivePacketInput K Q = Scalar.maxPositive (Algebra.orderedScalar K) Q

canonicalGamma :
  (K : Algebra.ExactOrderedCommutativeRing) →
  ExactReciprocalAuthority K →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K)
canonicalGamma K I Q viscousRate =
  Scalar._*_ S (positivePacketInput K Q) (reciprocal I viscousRate)
  where
  S = Algebra.orderedScalar K

canonicalPositiveEfficiency :
  (K : Algebra.ExactOrderedCommutativeRing) →
  ExactReciprocalAuthority K →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K)
canonicalPositiveEfficiency K I Q envelope =
  Scalar._*_ S (positivePacketInput K Q) (reciprocal I envelope)
  where
  S = Algebra.orderedScalar K

canonicalEnvelopeDissipationRatio :
  (K : Algebra.ExactOrderedCommutativeRing) →
  ExactReciprocalAuthority K →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K)
canonicalEnvelopeDissipationRatio K I envelope viscousRate =
  Scalar._*_ S envelope (reciprocal I viscousRate)
  where
  S = Algebra.orderedScalar K

canonicalGammaProductIdentity :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (I : ExactReciprocalAuthority K) →
  (Q envelope viscousRate : Scalar.Scalar (Algebra.orderedScalar K)) →
  Scalar.Nonzero (Algebra.orderedScalar K) envelope →
  Scalar.Nonzero (Algebra.orderedScalar K) viscousRate →
  Scalar._*_ (Algebra.orderedScalar K)
    (canonicalPositiveEfficiency K I Q envelope)
    (canonicalEnvelopeDissipationRatio K I envelope viscousRate) ≡
  canonicalGamma K I Q viscousRate
canonicalGammaProductIdentity K I Q envelope viscousRate envelopeNonzero viscousNonzero =
  trans
    (Algebra.mulAssociative K qPositive invEnvelope
      (Scalar._*_ S envelope invViscous))
    (trans
      (cong (Scalar._*_ S qPositive)
        (sym (Algebra.mulAssociative K invEnvelope envelope invViscous)))
      (trans
        (cong
          (λ x → Scalar._*_ S qPositive
            (Scalar._*_ S x invViscous))
          (trans
            (Algebra.mulCommutative K invEnvelope envelope)
            (reciprocalCancelsRight I envelope envelopeNonzero)))
        (cong (Scalar._*_ S qPositive)
          (Algebra.mulOneLeft K invViscous))))
  where
  S = Algebra.orderedScalar K
  qPositive = positivePacketInput K Q
  invEnvelope = reciprocal I envelope
  invViscous = reciprocal I viscousRate

------------------------------------------------------------------------
-- The issue-#11 specialization:
-- Gamma_K = E_{K,+} * A_K/(2 nu D_K).
------------------------------------------------------------------------

canonicalFiniteGammaProductIdentity :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (I : ExactReciprocalAuthority K) →
  (M R : Nat) →
  (z : Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M) →
  (T : Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  (nu D : Scalar.Scalar (Algebra.orderedScalar K)) →
  Scalar.Nonzero (Algebra.orderedScalar K)
    (canonicalAbsoluteEnvelopeAK K M R z T) →
  Scalar.Nonzero (Algebra.orderedScalar K)
    (viscousRate2NuD K nu D) →
  Scalar._*_ (Algebra.orderedScalar K)
    (canonicalPositiveEfficiency K I
      (canonicalPacketTransferQK K M R z T)
      (canonicalAbsoluteEnvelopeAK K M R z T))
    (canonicalEnvelopeDissipationRatio K I
      (canonicalAbsoluteEnvelopeAK K M R z T)
      (viscousRate2NuD K nu D)) ≡
  canonicalGamma K I
    (canonicalPacketTransferQK K M R z T)
    (viscousRate2NuD K nu D)
canonicalFiniteGammaProductIdentity K I M R z T nu D envelopeNonzero viscousNonzero =
  canonicalGammaProductIdentity K I
    (canonicalPacketTransferQK K M R z T)
    (canonicalAbsoluteEnvelopeAK K M R z T)
    (viscousRate2NuD K nu D)
    envelopeNonzero viscousNonzero
