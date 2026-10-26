module DASHI.Analysis.IITZetaGeneratingBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Analysis.ZetaTheoremSurface as Zeta
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- IIT / ZETA GENERATING BOUNDARY
--
-- The zeta lane is downstream of the finite integration programme.  A family
-- of finite integration counts may be packaged as coefficients of a generating
-- object, but no Dirichlet-series convergence, analytic continuation or RH
-- statement follows from that packaging.  A single sampled coefficient is also
-- provably insufficient for the full coefficient sequence.
------------------------------------------------------------------------

IntegrationCoefficientSequence : Set
IntegrationCoefficientSequence = Nat → Nat

sequenceA : IntegrationCoefficientSequence
sequenceA zero = 0
sequenceA (suc zero) = 0
sequenceA (suc (suc n)) = 0

sequenceB : IntegrationCoefficientSequence
sequenceB zero = 0
sequenceB (suc zero) = 1
sequenceB (suc (suc n)) = 0

constantCoefficient : IntegrationCoefficientSequence → Nat
constantCoefficient sequence = sequence zero

firstPositiveCoefficient : IntegrationCoefficientSequence → Nat
firstPositiveCoefficient sequence = sequence (suc zero)

constantCoefficientCollision :
  constantCoefficient sequenceA ≡ constantCoefficient sequenceB
constantCoefficientCollision = refl

zeroNotOne : 0 ≡ 1 → ⊥
zeroNotOne ()

singleCoefficientLosesSpectrum :
  Descent.ConsumerNonDescentWitness
    constantCoefficient
    firstPositiveCoefficient
singleCoefficientLosesSpectrum =
  Descent.consumerNonDescentWitness
    sequenceA
    sequenceB
    refl
    zeroNotOne

singleCoefficientCannotRecoverNextCoefficient :
  Descent.FactorsThrough constantCoefficient firstPositiveCoefficient → ⊥
singleCoefficientCannotRecoverNextCoefficient =
  Descent.nonDescentWitnessBlocksFactorization
    singleCoefficientLosesSpectrum

record IITZetaGeneratingBoundary : Set where
  constructor iitZetaGeneratingBoundary
  field
    finiteIntegrationCountsCanFormCoefficientSequence : Bool
    coefficientPackagingConstructsDirichletSeriesConvergence : Bool
    coefficientPackagingConstructsAnalyticContinuation : Bool
    oneZetaLikeSampleRecoversFullIntegrationSpectrum : Bool
    zetaCoincidenceIdentifiesIITMechanism : Bool
    existingRiemannProgrammeRemainsIndependent : Bool
    analyticPromotionRequiresSeparateSameObjectBridge : Bool

open IITZetaGeneratingBoundary public

canonicalIITZetaGeneratingBoundary : IITZetaGeneratingBoundary
canonicalIITZetaGeneratingBoundary =
  iitZetaGeneratingBoundary
    true
    false false false false
    true true

finitePackagingIsNotAnalyticContinuation :
  coefficientPackagingConstructsAnalyticContinuation
    canonicalIITZetaGeneratingBoundary ≡ false
finitePackagingIsNotAnalyticContinuation = refl

zetaCoincidenceDoesNotIdentifyIIT :
  zetaCoincidenceIdentifiesIITMechanism canonicalIITZetaGeneratingBoundary ≡ false
zetaCoincidenceDoesNotIdentifyIIT = refl
