{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopRichBrillouinGaussianExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityBishopInversePiSquaredUnitBoundExact as Pi
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2Running
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanYM4SU2GaussianBetaLowerExact as SU2
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CANONICAL BISHOP RUNNING = RICH T4 BRILLOUIN GAUSSIAN
--
-- Both sides already expose the same physical formula:
--
--   (11 C_A / 24) * pi^{-2} * log L.
--
-- The canonical P3/Bishop convention writes the rational color coefficient
-- as one embedded rational, whereas the rich Brillouin carrier writes
--
--   embed(11/24) * embed(C_A).
--
-- The Bishop rational embedding is multiplicative, so this is only carrier
-- algebra.  The remaining inputs below identify the rich carrier operations,
-- SU(2) Casimir, Machin pi^{-2}, and log coordinate with the canonical Bishop
-- objects.  No rationalized log coordinate appears.
------------------------------------------------------------------------

record CanonicalBishopRichBrillouinNormalization
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ)
    (running : SU2Running.CanonicalBishopSU2RunningInputs Nat) : Set₁ where
  field
    rationalIsCanonical :
      ∀ rational →
      Bishop._≃_
        (Rich.rational rich rational)
        (Embed.embed rational)

    multiplyIsBishop :
      ∀ left right →
      Bishop._≃_
        (Rich.multiply rich left right)
        (Bishop._*_ left right)

    casimirIsCanonicalSU2 :
      ∀ scale →
      Bishop._≃_
        (Rich.casimirAdjoint rich scale)
        (Embed.embed SU2.su2Casimir)

    inversePiSquaredIsCanonicalMachin :
      ∀ scale →
      Bishop._≃_
        (Rich.inversePiSquared rich scale)
        Pi.inversePiSquared

    logBlockingIsCanonical :
      ∀ scale →
      Bishop._≃_
        (Rich.logBlocking rich scale)
        (SU2Running.logBlocking running scale)

open CanonicalBishopRichBrillouinNormalization public

equalityAsBishopSetoid :
  ∀ {left right : Bishop.ℝ} →
  left ≡ right →
  Bishop._≃_ left right
equalityAsBishopSetoid {left} equality =
  subst
    (λ selected → Bishop._≃_ left selected)
    equality
    BishopP.≃-refl

embeddedElevenTwentyFourthTimesSU2IsCanonicalCoefficient :
  Bishop._≃_
    (Bishop._*_
      (Embed.embed Integral.elevenTwentyFourth)
      (Embed.embed SU2.su2Casimir))
    (Embed.embed
      (Beta.pureYMInverseCouplingCoefficient SU2.su2Casimir))
embeddedElevenTwentyFourthTimesSU2IsCanonicalCoefficient =
  BishopP.≃-trans
    (BishopP.≃-symm
      (Embed.embedMul
        Integral.elevenTwentyFourth
        SU2.su2Casimir))
    (subst
      (λ selected →
        Bishop._≃_
          (Embed.embed
            (Integral.elevenTwentyFourth * SU2.su2Casimir))
          (Embed.embed selected))
      (sym
        (Beta.inverseCouplingIsElevenOverTwentyFour
          SU2.su2Casimir))
      BishopP.≃-refl)

richColorFactorIsCanonicalCoefficient :
  ∀ {rich running}
    (normalization :
      CanonicalBishopRichBrillouinNormalization rich running)
    scale →
  Bishop._≃_
    (Rich.multiply rich
      (Rich.rational rich Integral.elevenTwentyFourth)
      (Rich.casimirAdjoint rich scale))
    (Embed.embed
      (Beta.pureYMInverseCouplingCoefficient SU2.su2Casimir))
richColorFactorIsCanonicalCoefficient
    {rich = rich} normalization scale =
  BishopP.≃-trans
    (multiplyIsBishop normalization
      (Rich.rational rich Integral.elevenTwentyFourth)
      (Rich.casimirAdjoint rich scale))
    (BishopP.≃-trans
      (BishopP.*-cong
        (rationalIsCanonical normalization Integral.elevenTwentyFourth)
        (casimirIsCanonicalSU2 normalization scale))
      embeddedElevenTwentyFourthTimesSU2IsCanonicalCoefficient)

richPiLogFactorIsCanonical :
  ∀ {rich running}
    (normalization :
      CanonicalBishopRichBrillouinNormalization rich running)
    scale →
  Bishop._≃_
    (Rich.multiply rich
      (Rich.inversePiSquared rich scale)
      (Rich.logBlocking rich scale))
    (Bishop._*_
      Pi.inversePiSquared
      (SU2Running.logBlocking running scale))
richPiLogFactorIsCanonical
    {rich = rich} normalization scale =
  BishopP.≃-trans
    (multiplyIsBishop normalization
      (Rich.inversePiSquared rich scale)
      (Rich.logBlocking rich scale))
    (BishopP.*-cong
      (inversePiSquaredIsCanonicalMachin normalization scale)
      (logBlockingIsCanonical normalization scale))

richScalarIntegralUsesCanonicalBishopSU2 :
  ∀ {rich running}
    (normalization :
      CanonicalBishopRichBrillouinNormalization rich running)
    scale →
  Bishop._≃_
    (Rich.scalarIntegral rich scale)
    (Bishop._*_
      (Embed.embed
        (Beta.pureYMInverseCouplingCoefficient SU2.su2Casimir))
      (Bishop._*_
        Pi.inversePiSquared
        (SU2Running.logBlocking running scale)))
richScalarIntegralUsesCanonicalBishopSU2
    {rich = rich} normalization scale =
  BishopP.≃-trans
    (equalityAsBishopSetoid
      (Rich.infraredShellIntegralLogLExact rich scale))
    (BishopP.≃-trans
      (multiplyIsBishop normalization
        (Rich.multiply rich
          (Rich.rational rich Integral.elevenTwentyFourth)
          (Rich.casimirAdjoint rich scale))
        (Rich.multiply rich
          (Rich.inversePiSquared rich scale)
          (Rich.logBlocking rich scale)))
      (BishopP.*-cong
        (richColorFactorIsCanonicalCoefficient normalization scale)
        (richPiLogFactorIsCanonical normalization scale)))

p3GaussianSameRichScalarIntegral :
  ∀ {rich running}
    (normalization :
      CanonicalBishopRichBrillouinNormalization rich running)
    scale →
  Bishop._≃_
    (P3.betaLogBlocking (SU2Running.recursion running) scale)
    (Rich.scalarIntegral rich scale)
p3GaussianSameRichScalarIntegral
    {running = running} normalization scale =
  BishopP.≃-trans
    (equalityAsBishopSetoid
      (SU2Running.betaLogBlockingDefinition running scale))
    (BishopP.≃-symm
      (richScalarIntegralUsesCanonicalBishopSU2 normalization scale))

------------------------------------------------------------------------
-- FRONTIER RECUT
------------------------------------------------------------------------

independentP3ToRichGaussianWitnessRequired :
  Agda.Builtin.Bool.Bool
independentP3ToRichGaussianWitnessRequired =
  Agda.Builtin.Bool.false

canonicalBishopRichBrillouinNormalizationCompilerLevel : ProofLevel
canonicalBishopRichBrillouinNormalizationCompilerLevel = machineChecked

canonicalBishopRichBrillouinCarrierIdentificationLevel : ProofLevel
canonicalBishopRichBrillouinCarrierIdentificationLevel = conditional
