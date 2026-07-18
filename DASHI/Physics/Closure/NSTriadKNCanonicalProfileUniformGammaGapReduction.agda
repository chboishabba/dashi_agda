module DASHI.Physics.Closure.NSTriadKNCanonicalProfileUniformGammaGapReduction where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNCanonicalEnvelopeProductIdentity as Envelope
import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- Exact analytic target surface for issue #11.
--
-- This module does not inhabit the profile-uniform estimate.  It connects the
-- already-proved finite identity
--
--   Gamma_K = E_{K,+} * A_K / (2 nu D_K)
--
-- to an abstract interval integral, proves that the product and Gamma forms
-- have exactly the same integral under explicit nonzero denominator
-- hypotheses, and proves the ordinary monotonicity reduction from a
-- pointwise strict gap to the requested time-integrated gap.
--
-- The missing theorem remains the construction of the pointwise or directly
-- integrated gap uniformly over all cutoffs and all normalized critical
-- profiles.  No postulate, Boolean promotion, sampled receipt, or canonical
-- inhabitant is introduced here.
------------------------------------------------------------------------

record IntervalIntegralStructure
    (K : Algebra.ExactOrderedCommutativeRing)
    (Time : Set) : Set₁ where
  field
    integrate :
      (Time → Scalar.Scalar (Algebra.orderedScalar K)) →
      Scalar.Scalar (Algebra.orderedScalar K)

    intervalLength :
      Scalar.Scalar (Algebra.orderedScalar K)

    integrateCong :
      {f g : Time → Scalar.Scalar (Algebra.orderedScalar K)} →
      ((t : Time) → f t ≡ g t) →
      integrate f ≡ integrate g

    integrateMonotone :
      {f g : Time → Scalar.Scalar (Algebra.orderedScalar K)} →
      ((t : Time) →
        Scalar._≤_ (Algebra.orderedScalar K) (f t) (g t)) →
      Scalar._≤_ (Algebra.orderedScalar K) (integrate f) (integrate g)

    integrateConstant :
      (c : Scalar.Scalar (Algebra.orderedScalar K)) →
      integrate (λ _ → c) ≡
      Scalar._*_ (Algebra.orderedScalar K) c intervalLength

open IntervalIntegralStructure public

oneMinusEta :
  (K : Algebra.ExactOrderedCommutativeRing) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  Scalar.Scalar (Algebra.orderedScalar K)
oneMinusEta K eta =
  Scalar._+_ S (Scalar.one S) (Scalar.neg S eta)
  where
  S = Algebra.orderedScalar K

StrictEta :
  (K : Algebra.ExactOrderedCommutativeRing) →
  Scalar.Scalar (Algebra.orderedScalar K) → Set
StrictEta K eta =
  Scalar.Nonnegative S eta × Scalar.Nonzero S eta
  where
  S = Algebra.orderedScalar K

canonicalQAt :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (M R : Nat) →
  (Time → Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M) →
  (Time → Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  Time → Scalar.Scalar (Algebra.orderedScalar K)
canonicalQAt K M R z T t =
  Envelope.canonicalPacketTransferQK K M R (z t) (T t)

canonicalAAt :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (M R : Nat) →
  (Time → Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M) →
  (Time → Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  Time → Scalar.Scalar (Algebra.orderedScalar K)
canonicalAAt K M R z T t =
  Envelope.canonicalAbsoluteEnvelopeAK K M R (z t) (T t)

viscousRateAt :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  (Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  Time → Scalar.Scalar (Algebra.orderedScalar K)
viscousRateAt K nu D t = Envelope.viscousRate2NuD K nu (D t)

canonicalProductIntegrandAt :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  Envelope.ExactReciprocalAuthority K →
  (M R : Nat) →
  (Time → Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M) →
  (Time → Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  (Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  Time → Scalar.Scalar (Algebra.orderedScalar K)
canonicalProductIntegrandAt K I M R z T nu D t =
  Scalar._*_ S
    (Envelope.canonicalPositiveEfficiency K I
      (canonicalQAt K M R z T t)
      (canonicalAAt K M R z T t))
    (Envelope.canonicalEnvelopeDissipationRatio K I
      (canonicalAAt K M R z T t)
      (viscousRateAt K nu D t))
  where
  S = Algebra.orderedScalar K

canonicalGammaIntegrandAt :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  Envelope.ExactReciprocalAuthority K →
  (M R : Nat) →
  (Time → Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M) →
  (Time → Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  (Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  Time → Scalar.Scalar (Algebra.orderedScalar K)
canonicalGammaIntegrandAt K I M R z T nu D t =
  Envelope.canonicalGamma K I
    (canonicalQAt K M R z T t)
    (viscousRateAt K nu D t)

canonicalProductIntegrandEqualsGammaAt :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (I : Envelope.ExactReciprocalAuthority K) →
  (M R : Nat) →
  (z : Time → Energy.AdmissibleFourierMultiplier
    (Algebra.orderedScalar K) M) →
  (T : Time → Energy.ZeroSumTriadTransferField
    (Algebra.orderedScalar K)) →
  (nu : Scalar.Scalar (Algebra.orderedScalar K)) →
  (D : Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  ((t : Time) → Scalar.Nonzero (Algebra.orderedScalar K)
    (canonicalAAt K M R z T t)) →
  ((t : Time) → Scalar.Nonzero (Algebra.orderedScalar K)
    (viscousRateAt K nu D t)) →
  (t : Time) →
  canonicalProductIntegrandAt K I M R z T nu D t ≡
  canonicalGammaIntegrandAt K I M R z T nu D t
canonicalProductIntegrandEqualsGammaAt
  K I M R z T nu D envelopeNonzero viscousNonzero t =
  Envelope.canonicalFiniteGammaProductIdentity
    K I M R (z t) (T t) nu (D t)
    (envelopeNonzero t) (viscousNonzero t)

integratedProductEqualsIntegratedGamma :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (I : Envelope.ExactReciprocalAuthority K) →
  (J : IntervalIntegralStructure K Time) →
  (M R : Nat) →
  (z : Time → Energy.AdmissibleFourierMultiplier
    (Algebra.orderedScalar K) M) →
  (T : Time → Energy.ZeroSumTriadTransferField
    (Algebra.orderedScalar K)) →
  (nu : Scalar.Scalar (Algebra.orderedScalar K)) →
  (D : Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  ((t : Time) → Scalar.Nonzero (Algebra.orderedScalar K)
    (canonicalAAt K M R z T t)) →
  ((t : Time) → Scalar.Nonzero (Algebra.orderedScalar K)
    (viscousRateAt K nu D t)) →
  integrate J (canonicalProductIntegrandAt K I M R z T nu D) ≡
  integrate J (canonicalGammaIntegrandAt K I M R z T nu D)
integratedProductEqualsIntegratedGamma
  K I J M R z T nu D envelopeNonzero viscousNonzero =
  integrateCong J
    (canonicalProductIntegrandEqualsGammaAt
      K I M R z T nu D envelopeNonzero viscousNonzero)

IntegratedProductGap :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  Envelope.ExactReciprocalAuthority K →
  IntervalIntegralStructure K Time →
  (M R : Nat) →
  (Time → Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M) →
  (Time → Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  (Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  Scalar.Scalar (Algebra.orderedScalar K) → Set
IntegratedProductGap K I J M R z T nu D eta =
  Scalar._≤_ S
    (integrate J (canonicalProductIntegrandAt K I M R z T nu D))
    (Scalar._*_ S (oneMinusEta K eta) (intervalLength J))
  where
  S = Algebra.orderedScalar K

IntegratedGammaGap :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  Envelope.ExactReciprocalAuthority K →
  IntervalIntegralStructure K Time →
  (M R : Nat) →
  (Time → Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M) →
  (Time → Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  (Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  Scalar.Scalar (Algebra.orderedScalar K) → Set
IntegratedGammaGap K I J M R z T nu D eta =
  Scalar._≤_ S
    (integrate J (canonicalGammaIntegrandAt K I M R z T nu D))
    (Scalar._*_ S (oneMinusEta K eta) (intervalLength J))
  where
  S = Algebra.orderedScalar K

productGapImpliesGammaGap :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (I : Envelope.ExactReciprocalAuthority K) →
  (J : IntervalIntegralStructure K Time) →
  (M R : Nat) →
  (z : Time → Energy.AdmissibleFourierMultiplier
    (Algebra.orderedScalar K) M) →
  (T : Time → Energy.ZeroSumTriadTransferField
    (Algebra.orderedScalar K)) →
  (nu : Scalar.Scalar (Algebra.orderedScalar K)) →
  (D : Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  (eta : Scalar.Scalar (Algebra.orderedScalar K)) →
  ((t : Time) → Scalar.Nonzero (Algebra.orderedScalar K)
    (canonicalAAt K M R z T t)) →
  ((t : Time) → Scalar.Nonzero (Algebra.orderedScalar K)
    (viscousRateAt K nu D t)) →
  IntegratedProductGap K I J M R z T nu D eta →
  IntegratedGammaGap K I J M R z T nu D eta
productGapImpliesGammaGap
  K I J M R z T nu D eta envelopeNonzero viscousNonzero productGap =
  subst
    (λ lhs → Scalar._≤_ S lhs rhs)
    (integratedProductEqualsIntegratedGamma
      K I J M R z T nu D envelopeNonzero viscousNonzero)
    productGap
  where
  S = Algebra.orderedScalar K
  rhs = Scalar._*_ S (oneMinusEta K eta) (intervalLength J)

gammaGapImpliesProductGap :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (I : Envelope.ExactReciprocalAuthority K) →
  (J : IntervalIntegralStructure K Time) →
  (M R : Nat) →
  (z : Time → Energy.AdmissibleFourierMultiplier
    (Algebra.orderedScalar K) M) →
  (T : Time → Energy.ZeroSumTriadTransferField
    (Algebra.orderedScalar K)) →
  (nu : Scalar.Scalar (Algebra.orderedScalar K)) →
  (D : Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  (eta : Scalar.Scalar (Algebra.orderedScalar K)) →
  ((t : Time) → Scalar.Nonzero (Algebra.orderedScalar K)
    (canonicalAAt K M R z T t)) →
  ((t : Time) → Scalar.Nonzero (Algebra.orderedScalar K)
    (viscousRateAt K nu D t)) →
  IntegratedGammaGap K I J M R z T nu D eta →
  IntegratedProductGap K I J M R z T nu D eta
gammaGapImpliesProductGap
  K I J M R z T nu D eta envelopeNonzero viscousNonzero gammaGap =
  subst
    (λ lhs → Scalar._≤_ S lhs rhs)
    (sym (integratedProductEqualsIntegratedGamma
      K I J M R z T nu D envelopeNonzero viscousNonzero))
    gammaGap
  where
  S = Algebra.orderedScalar K
  rhs = Scalar._*_ S (oneMinusEta K eta) (intervalLength J)

PointwiseGammaGap :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  Envelope.ExactReciprocalAuthority K →
  (M R : Nat) →
  (Time → Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) M) →
  (Time → Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  (Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  Scalar.Scalar (Algebra.orderedScalar K) → Set
PointwiseGammaGap K I M R z T nu D eta =
  (t : _) →
  Scalar._≤_ (Algebra.orderedScalar K)
    (canonicalGammaIntegrandAt K I M R z T nu D t)
    (oneMinusEta K eta)

pointwiseGammaGapImpliesIntegratedGammaGap :
  {Time : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (I : Envelope.ExactReciprocalAuthority K) →
  (J : IntervalIntegralStructure K Time) →
  (M R : Nat) →
  (z : Time → Energy.AdmissibleFourierMultiplier
    (Algebra.orderedScalar K) M) →
  (T : Time → Energy.ZeroSumTriadTransferField
    (Algebra.orderedScalar K)) →
  (nu : Scalar.Scalar (Algebra.orderedScalar K)) →
  (D : Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  (eta : Scalar.Scalar (Algebra.orderedScalar K)) →
  PointwiseGammaGap K I M R z T nu D eta →
  IntegratedGammaGap K I J M R z T nu D eta
pointwiseGammaGapImpliesIntegratedGammaGap
  K I J M R z T nu D eta pointwise =
  subst
    (λ rhs → Scalar._≤_ S
      (integrate J (canonicalGammaIntegrandAt K I M R z T nu D)) rhs)
    (integrateConstant J (oneMinusEta K eta))
    (integrateMonotone J
      {f = canonicalGammaIntegrandAt K I M R z T nu D}
      {g = λ _ → oneMinusEta K eta}
      pointwise)
  where
  S = Algebra.orderedScalar K

ProfileUniformCutoffProductGap :
  {Time Profile : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  Envelope.ExactReciprocalAuthority K →
  IntervalIntegralStructure K Time →
  (M : Profile → Nat) →
  ((p : Profile) → Time →
    Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) (M p)) →
  (Profile → Time →
    Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  (Profile → Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  Scalar.Scalar (Algebra.orderedScalar K) → Set
ProfileUniformCutoffProductGap K I J M z T nu D eta =
  (p : _) → (R : Nat) →
  IntegratedProductGap K I J (M p) R (z p) (T p) nu (D p) eta

ProfileUniformCutoffGammaGap :
  {Time Profile : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  Envelope.ExactReciprocalAuthority K →
  IntervalIntegralStructure K Time →
  (M : Profile → Nat) →
  ((p : Profile) → Time →
    Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) (M p)) →
  (Profile → Time →
    Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  (Profile → Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  Scalar.Scalar (Algebra.orderedScalar K) → Set
ProfileUniformCutoffGammaGap K I J M z T nu D eta =
  (p : _) → (R : Nat) →
  IntegratedGammaGap K I J (M p) R (z p) (T p) nu (D p) eta

ProfileEnvelopeNonzero :
  {Time Profile : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (M : Profile → Nat) →
  ((p : Profile) → Time →
    Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) (M p)) →
  (Profile → Time →
    Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) → Set
ProfileEnvelopeNonzero K M z T =
  (p : _) → (R : Nat) → (t : _) →
  Scalar.Nonzero (Algebra.orderedScalar K)
    (canonicalAAt K (M p) R (z p) (T p) t)

ProfileViscousRateNonzero :
  {Time Profile : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  Scalar.Scalar (Algebra.orderedScalar K) →
  (Profile → Time → Scalar.Scalar (Algebra.orderedScalar K)) → Set
ProfileViscousRateNonzero K nu D =
  (p : _) → (t : _) →
  Scalar.Nonzero (Algebra.orderedScalar K)
    (viscousRateAt K nu (D p) t)

profileUniformProductGapImpliesGammaGap :
  {Time Profile : Set} →
  (K : Algebra.ExactOrderedCommutativeRing) →
  (I : Envelope.ExactReciprocalAuthority K) →
  (J : IntervalIntegralStructure K Time) →
  (M : Profile → Nat) →
  (z : (p : Profile) → Time →
    Energy.AdmissibleFourierMultiplier (Algebra.orderedScalar K) (M p)) →
  (T : Profile → Time →
    Energy.ZeroSumTriadTransferField (Algebra.orderedScalar K)) →
  (nu : Scalar.Scalar (Algebra.orderedScalar K)) →
  (D : Profile → Time → Scalar.Scalar (Algebra.orderedScalar K)) →
  (eta : Scalar.Scalar (Algebra.orderedScalar K)) →
  ProfileEnvelopeNonzero K M z T →
  ProfileViscousRateNonzero K nu D →
  ProfileUniformCutoffProductGap K I J M z T nu D eta →
  ProfileUniformCutoffGammaGap K I J M z T nu D eta
profileUniformProductGapImpliesGammaGap
  K I J M z T nu D eta envelopeNonzero viscousNonzero productGap p R =
  productGapImpliesGammaGap
    K I J (M p) R (z p) (T p) nu (D p) eta
    (envelopeNonzero p R) (viscousNonzero p) (productGap p R)
