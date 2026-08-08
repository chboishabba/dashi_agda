module DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaRound27Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Integrate the highest-alpha Round 27 exports from the finite Monster
-- projector/core lane into the literal periodic Navier--Stokes route:
--
-- * sharp finite shell-projector algebra;
-- * Fourier reality as an involutive fixed-point carrier;
-- * state/dual separation and exact signed translation--multiplier
--   commutator;
-- * division-free centred five-source probe;
-- * maximal uniform viscosity-core theorem under unique ownership;
-- * exact Plucker/Gram geometry for physical resonant triads;
-- * generated finite arithmetic certificates.
--
-- These are substantive exact lemmas.  The finite Picard--Lindelof instance,
-- physical time-dependent shell balance, cutoff-uniform operator taxes,
-- periodic CZ estimate, strict eta margin, limits and Clay theorem remain
-- open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Agda.Builtin.Nat as Nat
open import Data.Nat.Base using (_≤_)
import Data.Integer.Base as Int
import Data.Rational.Base as Rat

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteShellProjectorRound27Exact as Projector
import DASHI.Physics.Closure.NSTriadKNRealityInvolutionEquivarianceRound27Exact as Reality
import DASHI.Physics.Closure.NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact as Commutator
import DASHI.Physics.Closure.NSTriadKNCentredFiveSourceProbeRound27Exact as Probe
import DASHI.Physics.Closure.NSTriadKNMaximalUniformViscosityCoreRound27Exact as Core
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadPluckerInvariantRound27Exact as Plucker
import DASHI.Physics.Closure.NSTriadKNLuoRound27FiniteCertificateGenerated as Certificate

record Round27ExactEvidence : Set₁ where
  field
    shellProjectorIdempotent : ∀ shell mode →
      Nat._*_
        (Projector.shellProjectorCoefficient shell mode)
        (Projector.shellProjectorCoefficient shell mode)
      ≡ Projector.shellProjectorCoefficient shell mode

    shellProjectorsDisjoint : ∀ left right mode →
      Projector.natEqual left right ≡ false →
      Nat._*_
        (Projector.shellProjectorCoefficient left mode)
        (Projector.shellProjectorCoefficient right mode)
      ≡ 0

    shellProjectorsResolveFiniteCarrier : ∀ maximum mode →
      Shell.shellIndex mode ≤ maximum →
      Projector.shellResolutionCoefficient
        maximum (Shell.shellIndex mode)
      ≡ 1

    signedTranslationMultiplierCommutator :
      ∀ multiplier shift state output →
      Commutator.stateCoefficient
        (Commutator.translationMultiplierCommutator
          multiplier shift state) output
      ≡
      Commutator.stateCoefficient
        (Commutator.signedDifferenceCommutator
          multiplier shift state) output

    centredFiveSourceProbe :
      (weights : Probe.FiveSourceWeights) →
      (source : Probe.FiveSourceCoreDefect) →
      Rat._*_
        Probe.five
        (Probe.weightedSourceProbe weights source)
      ≡
      Rat._+_
        (Rat._*_
          (Probe.weightSum weights)
          (Probe.sourceAugmentation source))
        (Probe.centredDefectProbe weights source)

    maximalUniformViscosityCore :
      ∀ {allocation} →
      (witness : Core.MaximalUniformCoreWitness allocation) →
      (candidate : Core.UniformViscosityCoreDecomposition allocation) →
      Core.commonCore candidate
      ≤ Core.commonCore (Core.canonicalDecomposition witness)

    physicalTriadGramIdentity :
      (triad : Physical.PhysicalTriadIncidence) →
      Plucker.pluckerNormSquared (Physical.p triad) (Physical.q triad)
      ≡
      Int._-_
        (Int._*_
          (Plucker.modeNormSquared (Physical.p triad))
          (Plucker.modeNormSquared (Physical.q triad)))
        (Int._*_
          (Plucker.dotMode (Physical.p triad) (Physical.q triad))
          (Plucker.dotMode (Physical.p triad) (Physical.q triad)))

open Round27ExactEvidence public

canonicalRound27ExactEvidence : Round27ExactEvidence
canonicalRound27ExactEvidence = record
  { shellProjectorIdempotent = Projector.shellProjectorIdempotent
  ; shellProjectorsDisjoint =
      Projector.shellProjectorDisjointOutsideShell
  ; shellProjectorsResolveFiniteCarrier =
      Projector.finiteShellProjectorResolution
  ; signedTranslationMultiplierCommutator =
      Commutator.translationMultiplierCommutatorExact
  ; centredFiveSourceProbe = Probe.centredFiveSourceProbeIdentity
  ; maximalUniformViscosityCore =
      Core.maximalUniformCoreDominatesEveryCandidate
  ; physicalTriadGramIdentity =
      λ triad → Plucker.pluckerGramIdentity
        (Physical.p triad) (Physical.q triad)
  }

record Round27HighestAlphaBoundary : Set where
  constructor round27-highest-alpha-boundary
  field
    sharpFiniteShellProjectorAlgebra : Bool
    shellRealityCovarianceGeneric : Bool
    realityInvolutionFixedPointAlgebra : Bool
    diagonalMultiplierRealityEquivariance : Bool
    fullPhysicalVectorFieldEquivariance : Bool
    stateDualCarrierSeparated : Bool
    signedTranslationMultiplierCommutator : Bool
    cutoffUniformSignedOperatorTax : Bool
    centredFiveSourceProbe : Bool
    maximalUniformViscosityCore : Bool
    physicalOwnerAllocationsInstantiated : Bool
    physicalTriadPluckerGeometry : Bool
    finiteCertificatePipeline : Bool
    finitePicardLindelofInstantiated : Bool
    physicalTimeDependentShellBalance : Bool
    periodicStrainCZTax : Bool
    strictTotalViscosityMargin : Bool
    shellAndGalerkinLimits : Bool
    unconditionalClayTheorem : Bool

open Round27HighestAlphaBoundary public

canonicalRound27HighestAlphaBoundary : Round27HighestAlphaBoundary
canonicalRound27HighestAlphaBoundary =
  round27-highest-alpha-boundary
    true true true true false
    true true false
    true true false true true
    false false false false false false

physicalVectorFieldEquivarianceStillOpen :
  fullPhysicalVectorFieldEquivariance canonicalRound27HighestAlphaBoundary
  ≡ false
physicalVectorFieldEquivarianceStillOpen = refl

uniformSignedOperatorTaxStillOpen :
  cutoffUniformSignedOperatorTax canonicalRound27HighestAlphaBoundary
  ≡ false
uniformSignedOperatorTaxStillOpen = refl

finiteODEStillOpen :
  finitePicardLindelofInstantiated canonicalRound27HighestAlphaBoundary
  ≡ false
finiteODEStillOpen = refl

strictMarginStillOpen :
  strictTotalViscosityMargin canonicalRound27HighestAlphaBoundary
  ≡ false
strictMarginStillOpen = refl

clayPromotionStillFalse :
  unconditionalClayTheorem canonicalRound27HighestAlphaBoundary
  ≡ false
clayPromotionStillFalse = refl

finiteCertificatePassed : Certificate.allFiniteChecksPassed ≡ true
finiteCertificatePassed = refl
