module DASHI.Physics.Closure.NSTriadKNVariationalRigidityOperatorRefinement where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Data.Nat using (_≤_; _<_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; *-monoʳ-≤; +-monoʳ-≤; *-identityʳ)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)

import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom

------------------------------------------------------------------------
-- This module implements the three honest routes past the saturated generic
-- weak/strong estimate:
--
--   1. a variational (Rayleigh-quotient) base-form certificate;
--   2. a quantitative compactness/rigidity gap on normalized states;
--   3. a refined operator estimate compared directly with qBase.
--
-- No canonical closure flag is flipped here.  Each route exposes exactly the
-- constructive witness which, once instantiated by the real Stage-3 carrier,
-- yields the strict base-minus-error margin required by ResidueScaleCompatibility.
------------------------------------------------------------------------

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

four : Nat
four = suc three

------------------------------------------------------------------------
-- 1. Variational / Rayleigh reformulation.
------------------------------------------------------------------------

record RayleighBaseCertificate {ℓ : Level}
    (Carrier : Set ℓ)
    (strongNormSquared qBase : Carrier → Nat) : Set (lsuc ℓ) where
  constructor mkRayleighBaseCertificate
  field
    rayleighFloor : Nat
    rayleighFloorPositive : zero < rayleighFloor
    rayleighLowerBound :
      (x : Carrier) →
      rayleighFloor * strongNormSquared x ≤ qBase x

open RayleighBaseCertificate public

-- Scale-aware form used by the q-gap package.  The quotient is encoded without
-- division: A is an admissible Rayleigh floor exactly when
-- A |x|^2 <= scaleSq qBase(x).
record ScaledRayleighBaseCertificate {ℓ : Level}
    (N : Nat)
    (Carrier : Set ℓ)
    (scale : ScaleHeadroom.CompatibilityScale N)
    (strongNormSquared qBase : Carrier → Nat) : Set (lsuc ℓ) where
  constructor mkScaledRayleighBaseCertificate
  field
    baseConstant : Nat
    baseConstantPositive : zero < baseConstant
    scaledRayleighLowerBound :
      (x : Carrier) →
      baseConstant * strongNormSquared x
        ≤ ScaleHeadroom.CompatibilityScale.scaleSq scale * qBase x

open ScaledRayleighBaseCertificate public

scaledRayleighToBaseGap :
  {N : Nat} {Carrier : Set} →
  {scale : ScaleHeadroom.CompatibilityScale N} →
  {strongNormSquared qBase : Carrier → Nat} →
  ScaledRayleighBaseCertificate N Carrier scale strongNormSquared qBase →
  (x : Carrier) →
  baseConstant _ * strongNormSquared x
    ≤ ScaleHeadroom.CompatibilityScale.scaleSq scale * qBase x
scaledRayleighToBaseGap cert = scaledRayleighLowerBound cert

------------------------------------------------------------------------
-- 2. Quantitative compactness / rigidity.
--
-- Rather than asserting a pointwise strict inequality from generic norm
-- domination, this record isolates a normalized compact state space, a rigid
-- zero-set, and a positive defect away from that zero-set.
------------------------------------------------------------------------

record QuantitativeRigidityGap {ℓ : Level}
    (Carrier : Set ℓ)
    (normalized rigid : Carrier → Set)
    (qBase qError strongNormSquared : Carrier → Nat) : Set (lsuc ℓ) where
  constructor mkQuantitativeRigidityGap
  field
    defectConstant : Nat
    defectConstantPositive : zero < defectConstant

    -- Compactness is represented constructively by a finite normal-form index:
    -- every normalized state has a canonical finite code.
    Code : Set
    code : Carrier → Code
    decode : Code → Carrier
    normalizedRetract :
      (x : Carrier) → normalized x → decode (code x) ≡ x

    rigidCharacterization :
      (x : Carrier) → normalized x →
      qBase x ≡ qError x → rigid x

    quantitativeAwayFromRigid :
      (x : Carrier) → normalized x → ¬ rigid x →
      qError x + defectConstant * strongNormSquared x ≤ qBase x

open QuantitativeRigidityGap public

-- The useful consequence: on the admissible normalized complement of the rigid
-- class, the error is strictly below the base form by an explicit norm defect.
rigidityGapWitness :
  {Carrier : Set} →
  {normalized rigid : Carrier → Set} →
  {qBase qError strongNormSquared : Carrier → Nat} →
  (gap : QuantitativeRigidityGap Carrier normalized rigid qBase qError strongNormSquared) →
  (x : Carrier) → normalized x → ¬ rigid x →
  qError x + QuantitativeRigidityGap.defectConstant gap * strongNormSquared x
    ≤ qBase x
rigidityGapWitness gap = QuantitativeRigidityGap.quantitativeAwayFromRigid gap

------------------------------------------------------------------------
-- 3. Refine the operator estimate itself.
--
-- This avoids multiplying two separately sharp generic inequalities.  The
-- refined quadratic error is tied directly to the actual Stage-3 operator and
-- compared with qBase on the admissible carrier.
------------------------------------------------------------------------

record RefinedOperatorRelativeGap {ℓ : Level}
    (Carrier : Set ℓ)
    (qBase qError strongNormSquared : Carrier → Nat) : Set (lsuc ℓ) where
  constructor mkRefinedOperatorRelativeGap
  field
    refinedError : Carrier → Nat
    refinedDominatesActual : (x : Carrier) → qError x ≤ refinedError x

    relativeDefectConstant : Nat
    relativeDefectPositive : zero < relativeDefectConstant
    refinedStrictRelativeBound :
      (x : Carrier) →
      refinedError x + relativeDefectConstant * strongNormSquared x
        ≤ qBase x

open RefinedOperatorRelativeGap public

actualErrorStrictRelativeBound :
  {Carrier : Set} →
  {qBase qError strongNormSquared : Carrier → Nat} →
  (refinement : RefinedOperatorRelativeGap Carrier qBase qError strongNormSquared) →
  (x : Carrier) →
  qError x + relativeDefectConstant refinement * strongNormSquared x ≤ qBase x
actualErrorStrictRelativeBound refinement x =
  ≤-trans
    (+-monoʳ-≤
      (relativeDefectConstant refinement * strongNormSquared x)
      (refinedDominatesActual refinement x))
    (refinedStrictRelativeBound refinement x)

------------------------------------------------------------------------
-- Scale-aware operator refinement.
------------------------------------------------------------------------

record ScaledRefinedOperatorEstimate {ℓ : Level}
    (N : Nat)
    (Carrier : Set ℓ)
    (scale : ScaleHeadroom.CompatibilityScale N)
    (qError strongNormSquared : Carrier → Nat) : Set (lsuc ℓ) where
  constructor mkScaledRefinedOperatorEstimate
  field
    refinedErrorConstant : Nat
    refinedErrorConstantPositive : zero < refinedErrorConstant
    refinedScaledOperatorBound :
      (x : Carrier) →
      ScaleHeadroom.CompatibilityScale.scaleSq scale * qError x
        ≤ refinedErrorConstant * strongNormSquared x

open ScaledRefinedOperatorEstimate public

scaledRefinementToQGapBridge :
  {N : Nat} {Carrier : Set} →
  {scale : ScaleHeadroom.CompatibilityScale N} →
  {qError strongNormSquared : Carrier → Nat} →
  ScaledRefinedOperatorEstimate N Carrier scale qError strongNormSquared →
  QGap.ScaledOperatorErrorBridge N Carrier
scaledRefinementToQGapBridge estimate =
  QGap.mkScaledOperatorErrorBridge
    _
    _
    _
    (refinedErrorConstant estimate)
    (refinedScaledOperatorBound estimate)

------------------------------------------------------------------------
-- Combined strict compatibility certificate.
------------------------------------------------------------------------

record VariationalCompatibilityCertificate {ℓ : Level}
    (N : Nat)
    (Carrier : Set ℓ)
    (scale : ScaleHeadroom.CompatibilityScale N)
    (qBase qError strongNormSquared : Carrier → Nat) : Set (lsuc ℓ) where
  constructor mkVariationalCompatibilityCertificate
  field
    baseRayleigh :
      ScaledRayleighBaseCertificate
        N Carrier scale strongNormSquared qBase
    operatorRefinement :
      ScaledRefinedOperatorEstimate
        N Carrier scale qError strongNormSquared
    strictConstantGap :
      refinedErrorConstant operatorRefinement < baseConstant baseRayleigh

open VariationalCompatibilityCertificate public

variationalBaseGapWitness :
  {N : Nat} {Carrier : Set} →
  {scale : ScaleHeadroom.CompatibilityScale N} →
  {qBase qError strongNormSquared : Carrier → Nat} →
  (cert : VariationalCompatibilityCertificate
    N Carrier scale qBase qError strongNormSquared) →
  (x : Carrier) →
  baseConstant (baseRayleigh cert) * strongNormSquared x
    ≤ ScaleHeadroom.CompatibilityScale.scaleSq scale * qBase x
variationalBaseGapWitness cert =
  scaledRayleighLowerBound (baseRayleigh cert)

variationalOperatorErrorWitness :
  {N : Nat} {Carrier : Set} →
  {scale : ScaleHeadroom.CompatibilityScale N} →
  {qBase qError strongNormSquared : Carrier → Nat} →
  (cert : VariationalCompatibilityCertificate
    N Carrier scale qBase qError strongNormSquared) →
  (x : Carrier) →
  ScaleHeadroom.CompatibilityScale.scaleSq scale * qError x
    ≤ refinedErrorConstant (operatorRefinement cert) * strongNormSquared x
variationalOperatorErrorWitness cert =
  refinedScaledOperatorBound (operatorRefinement cert)

------------------------------------------------------------------------
-- Canonical unit-shell audit.
--
-- On the presently exported model qBase = qError = strongNormSquared = energy.
-- The normalized unit-energy state therefore has generalized Rayleigh quotient
-- exactly one.  This proves that neither compactness nor a different statement
-- of the same pointwise forms can manufacture a positive defect: the actual
-- operator/form must be refined or the rigid equality direction excluded.
------------------------------------------------------------------------

CanonicalCarrier : Set
CanonicalCarrier = ResidueNorm.ResidueEnergyCarrier one

canonicalUnit : CanonicalCarrier
canonicalUnit = ResidueNorm.mkResidueEnergyCarrier one

canonicalEnergy : CanonicalCarrier → Nat
canonicalEnergy = ResidueNorm.residueEnergy

canonicalBaseAtUnit : canonicalEnergy canonicalUnit ≡ one
canonicalBaseAtUnit = refl

canonicalErrorAtUnit : canonicalEnergy canonicalUnit ≡ one
canonicalErrorAtUnit = refl

positiveDefectImpossibleAtCanonicalUnit :
  (δ : Nat) →
  zero < δ →
  ¬ (canonicalEnergy canonicalUnit + δ * canonicalEnergy canonicalUnit
      ≤ canonicalEnergy canonicalUnit)
positiveDefectImpossibleAtCanonicalUnit zero ()
positiveDefectImpossibleAtCanonicalUnit (suc δ) positive ()

canonicalRayleighRatioSaturated : Bool
canonicalRayleighRatioSaturated = true

canonicalRayleighRatioSaturatedIsTrue :
  canonicalRayleighRatioSaturated ≡ true
canonicalRayleighRatioSaturatedIsTrue = refl

canonicalVariationalCompatibilityClosed : Bool
canonicalVariationalCompatibilityClosed = false

canonicalVariationalCompatibilityClosedIsFalse :
  canonicalVariationalCompatibilityClosed ≡ false
canonicalVariationalCompatibilityClosedIsFalse = refl
