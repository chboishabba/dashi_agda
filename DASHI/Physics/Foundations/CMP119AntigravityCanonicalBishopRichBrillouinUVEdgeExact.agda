{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopRichBrillouinUVEdgeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (_*_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityBishopInversePiSquaredUnitBoundExact as Pi
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as Running
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopRichBrillouinGaussianExact as SameScale
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanYM4SU2GaussianBetaLowerExact as SU2
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- UV NODE/EDGE NORMALIZATION
--
-- P3 carries the increment on node (suc k), because nextScale(suc k)=k.
-- The literal/rich producer labels the same RG edge by k.  Keep that shift
-- explicit here:
--
--   P3 betaLogBlocking (suc k)  <->  rich scalarIntegral k.
------------------------------------------------------------------------

record CanonicalBishopRichBrillouinUVEdgeNormalization
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ)
    (running : Running.CanonicalBishopSU2RunningInputs Nat) : Set₁ where
  field
    rationalIsCanonical :
      ∀ rational →
      Bishop._≃_ (Rich.rational rich rational) (Embed.embed rational)

    multiplyIsBishop :
      ∀ left right →
      Bishop._≃_
        (Rich.multiply rich left right)
        (Bishop._*_ left right)

    casimirIsCanonicalSU2 :
      ∀ edge →
      Bishop._≃_
        (Rich.casimirAdjoint rich edge)
        (Embed.embed SU2.su2Casimir)

    inversePiSquaredIsCanonicalMachin :
      ∀ edge →
      Bishop._≃_
        (Rich.inversePiSquared rich edge)
        Pi.inversePiSquared

    edgeLogIsSuccessorNodeLog :
      ∀ edge →
      Bishop._≃_
        (Rich.logBlocking rich edge)
        (Running.logBlocking running (suc edge))

open CanonicalBishopRichBrillouinUVEdgeNormalization public

equalityAsBishopSetoid :
  ∀ {left right : Bishop.ℝ} →
  left ≡ right → Bishop._≃_ left right
equalityAsBishopSetoid {left} equality =
  subst (λ selected → Bishop._≃_ left selected) equality BishopP.≃-refl

richColorFactorIsCanonical :
  ∀ {rich running}
    (normalization :
      CanonicalBishopRichBrillouinUVEdgeNormalization rich running)
    edge →
  Bishop._≃_
    (Rich.multiply rich
      (Rich.rational rich Integral.elevenTwentyFourth)
      (Rich.casimirAdjoint rich edge))
    (Embed.embed
      (Beta.pureYMInverseCouplingCoefficient SU2.su2Casimir))
richColorFactorIsCanonical {rich = rich} normalization edge =
  BishopP.≃-trans
    (multiplyIsBishop normalization
      (Rich.rational rich Integral.elevenTwentyFourth)
      (Rich.casimirAdjoint rich edge))
    (BishopP.≃-trans
      (BishopP.*-cong
        (rationalIsCanonical normalization Integral.elevenTwentyFourth)
        (casimirIsCanonicalSU2 normalization edge))
      SameScale.embeddedElevenTwentyFourthTimesSU2IsCanonicalCoefficient)

richPiLogFactorIsCanonicalAtSuccessor :
  ∀ {rich running}
    (normalization :
      CanonicalBishopRichBrillouinUVEdgeNormalization rich running)
    edge →
  Bishop._≃_
    (Rich.multiply rich
      (Rich.inversePiSquared rich edge)
      (Rich.logBlocking rich edge))
    (Bishop._*_
      Pi.inversePiSquared
      (Running.logBlocking running (suc edge)))
richPiLogFactorIsCanonicalAtSuccessor
    {rich = rich} normalization edge =
  BishopP.≃-trans
    (multiplyIsBishop normalization
      (Rich.inversePiSquared rich edge)
      (Rich.logBlocking rich edge))
    (BishopP.*-cong
      (inversePiSquaredIsCanonicalMachin normalization edge)
      (edgeLogIsSuccessorNodeLog normalization edge))

richScalarIntegralAtEdgeUsesSuccessorCanonicalNode :
  ∀ {rich running}
    (normalization :
      CanonicalBishopRichBrillouinUVEdgeNormalization rich running)
    edge →
  Bishop._≃_
    (Rich.scalarIntegral rich edge)
    (Bishop._*_
      (Bishop._*_
        (Embed.embed
          (Beta.pureYMInverseCouplingCoefficient SU2.su2Casimir))
        Pi.inversePiSquared)
      (Running.logBlocking running (suc edge)))
richScalarIntegralAtEdgeUsesSuccessorCanonicalNode
    {rich = rich} {running = running} normalization edge =
  BishopP.≃-trans
    (equalityAsBishopSetoid
      (Rich.infraredShellIntegralLogLExact rich edge))
    (BishopP.≃-trans
      (multiplyIsBishop normalization
        (Rich.multiply rich
          (Rich.rational rich Integral.elevenTwentyFourth)
          (Rich.casimirAdjoint rich edge))
        (Rich.multiply rich
          (Rich.inversePiSquared rich edge)
          (Rich.logBlocking rich edge)))
      (BishopP.≃-trans
        (BishopP.*-cong
          (richColorFactorIsCanonical normalization edge)
          (richPiLogFactorIsCanonicalAtSuccessor normalization edge))
        (BishopP.≃-symm
          (BishopP.*-assoc
            (Embed.embed
              (Beta.pureYMInverseCouplingCoefficient SU2.su2Casimir))
            Pi.inversePiSquared
            (Running.logBlocking running (suc edge))))))

p3SuccessorGaussianSameRichEdgeIntegral :
  ∀ {rich running}
    (normalization :
      CanonicalBishopRichBrillouinUVEdgeNormalization rich running)
    edge →
  Bishop._≃_
    (P3.betaLogBlocking (Running.recursion running) (suc edge))
    (Rich.scalarIntegral rich edge)
p3SuccessorGaussianSameRichEdgeIntegral
    {running = running} normalization edge =
  BishopP.≃-trans
    (equalityAsBishopSetoid
      (Running.betaLogBlockingDefinition running (suc edge)))
    (BishopP.≃-symm
      (richScalarIntegralAtEdgeUsesSuccessorCanonicalNode
        normalization edge))

canonicalBishopRichBrillouinUVEdgeCompilerLevel : ProofLevel
canonicalBishopRichBrillouinUVEdgeCompilerLevel = machineChecked

canonicalBishopRichBrillouinUVEdgePhysicalIdentificationLevel : ProofLevel
canonicalBishopRichBrillouinUVEdgePhysicalIdentificationLevel = conditional
