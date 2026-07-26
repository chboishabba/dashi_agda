module DASHI.Physics.YangMills.BalabanClayP4CommonParameterDomainExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; _/_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanClayP1BackgroundStabilityExact
  using (oneThirtySecond)
open import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact
  using (half)
open import DASHI.Physics.YangMills.BalabanClayP4DyadicCoercivityBudgetExact
  using (oneSixtyFourth)

------------------------------------------------------------------------
-- A single numerical witness used by every package.  The actual analytic
-- producer theorems must prove their bounds at these same values; they are not
-- allowed to select mutually incompatible parameters independently.
------------------------------------------------------------------------

record ClayParameterTuple : Set where
  constructor clayParameters
  field
    blockingSide collarWidth : Nat
    backgroundRadius coupling chartRadius gaugePenalty
      sizeMargin diameterMargin kpEta contractionRatio : ℚ

open ClayParameterTuple public

canonicalClayParameters : ClayParameterTuple
canonicalClayParameters = clayParameters
  16
  4
  (+ 1 / 1024)
  (+ 1 / 1024)
  (+ 1 / 64)
  1ℚ
  (+ 1 / 4)
  (+ 1 / 4)
  half
  half

canonicalBackgroundRadius :
  backgroundRadius canonicalClayParameters ≡ + 1 / 1024
canonicalBackgroundRadius = refl

canonicalCoupling : coupling canonicalClayParameters ≡ + 1 / 1024
canonicalCoupling = refl

canonicalKPEta : kpEta canonicalClayParameters ≡ half
canonicalKPEta = refl

canonicalContractionRatio :
  contractionRatio canonicalClayParameters ≡ half
canonicalContractionRatio = refl

canonicalEtaGap :
  kpEta canonicalClayParameters + half ≡ 1ℚ
canonicalEtaGap = ℚRing.solve-∀

canonicalContractionGap :
  contractionRatio canonicalClayParameters + half ≡ 1ℚ
canonicalContractionGap = ℚRing.solve-∀

canonicalBackgroundBudgetIdentity :
  (+ 32 / 1) * backgroundRadius canonicalClayParameters
  ≡ oneThirtySecond
canonicalBackgroundBudgetIdentity = ℚRing.solve-∀

canonicalCoercivityReserveIdentity :
  oneSixtyFourth + oneSixtyFourth ≡ oneThirtySecond
canonicalCoercivityReserveIdentity = ℚRing.solve-∀

canonicalRadiusPositive :
  0ℚ < backgroundRadius canonicalClayParameters
canonicalRadiusPositive =
  let
    instance
      radiusPositive : Positive (+ 1 / 1024)
      radiusPositive = ℚP.normalize-pos 1 1024
  in
  ℚP.positive⁻¹ (backgroundRadius canonicalClayParameters)

canonicalCouplingPositive :
  0ℚ < coupling canonicalClayParameters
canonicalCouplingPositive = canonicalRadiusPositive

canonicalEtaGapPositive : 0ℚ < half
canonicalEtaGapPositive =
  let
    instance
      halfPositive : Positive half
      halfPositive = ℚP.normalize-pos 1 2
  in
  ℚP.positive⁻¹ half

------------------------------------------------------------------------
-- The common-domain cutset.  All physical estimates are evaluated at one tuple.
------------------------------------------------------------------------

record CommonClayParameterDomain : Set₁ where
  field
    parameters : ClayParameterTuple

    BackgroundConstraint LargeFieldConstraint OneStepConstraint
      ContinuumConstraint : ClayParameterTuple → Set

    backgroundConstraint : BackgroundConstraint parameters
    largeFieldConstraint : LargeFieldConstraint parameters
    oneStepConstraint : OneStepConstraint parameters
    continuumConstraint : ContinuumConstraint parameters

open CommonClayParameterDomain public

record CanonicalClayParameterDomain : Set₁ where
  field
    BackgroundConstraint LargeFieldConstraint OneStepConstraint
      ContinuumConstraint : ClayParameterTuple → Set

    backgroundAtCanonical :
      BackgroundConstraint canonicalClayParameters
    largeFieldAtCanonical :
      LargeFieldConstraint canonicalClayParameters
    oneStepAtCanonical :
      OneStepConstraint canonicalClayParameters
    continuumAtCanonical :
      ContinuumConstraint canonicalClayParameters

open CanonicalClayParameterDomain public

canonicalDomainIsCommon :
  CanonicalClayParameterDomain → CommonClayParameterDomain
canonicalDomainIsCommon witness = record
  { CommonClayParameterDomain.parameters = canonicalClayParameters
  ; CommonClayParameterDomain.BackgroundConstraint =
      CanonicalClayParameterDomain.BackgroundConstraint witness
  ; CommonClayParameterDomain.LargeFieldConstraint =
      CanonicalClayParameterDomain.LargeFieldConstraint witness
  ; CommonClayParameterDomain.OneStepConstraint =
      CanonicalClayParameterDomain.OneStepConstraint witness
  ; CommonClayParameterDomain.ContinuumConstraint =
      CanonicalClayParameterDomain.ContinuumConstraint witness
  ; CommonClayParameterDomain.backgroundConstraint =
      backgroundAtCanonical witness
  ; CommonClayParameterDomain.largeFieldConstraint =
      largeFieldAtCanonical witness
  ; CommonClayParameterDomain.oneStepConstraint =
      oneStepAtCanonical witness
  ; CommonClayParameterDomain.continuumConstraint =
      continuumAtCanonical witness
  }

canonicalParameterArithmeticLevel : ProofLevel
canonicalParameterArithmeticLevel = machineChecked

commonParameterIntersectionAssemblyLevel : ProofLevel
commonParameterIntersectionAssemblyLevel = machineChecked

canonicalBackgroundConstraintProducerLevel : ProofLevel
canonicalBackgroundConstraintProducerLevel = conditional

canonicalLargeFieldConstraintProducerLevel : ProofLevel
canonicalLargeFieldConstraintProducerLevel = conditional

canonicalOneStepConstraintProducerLevel : ProofLevel
canonicalOneStepConstraintProducerLevel = conditional

canonicalContinuumConstraintProducerLevel : ProofLevel
canonicalContinuumConstraintProducerLevel = conditional
