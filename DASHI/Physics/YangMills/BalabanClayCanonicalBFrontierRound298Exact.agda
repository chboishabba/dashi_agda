{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound298Exact where

------------------------------------------------------------------------
-- ROUND298 / HONEST DIRECT B MIN-CUT AFTER R295-R297
--
-- This round performs two opposite introspective corrections:
--
--   * REMOVE compiler debt:
--       - signed D^2 log Z = covariance;
--       - source covariance = exact finite T5 covariance on the preferred
--         expectation algebra;
--       - signed -> magnitude carrier correction;
--       - arbitrary nonzero-witness interpretation;
--       - opaque choice of separating time.
--
--   * RESTORE a hidden physical prerequisite:
--       - positive-time vacuum cyclicity of the actual reconstructed observable
--         carrier was embedded inside the R287/R288 spectral core and must not
--         disappear from the canonical frontier merely because the record was
--         already constructed.
--
-- The surviving direct-route theorem/source coordinates are therefore:
--
--   F1. literal physical CMP116/CMP119 J directions on the exact finite T5
--       expectation carrier obey the ABSOLUTE differentiated rooted-shell bound;
--   F2. physical positive-time reconstructed vacuum cyclicity;
--   F3. the actual cyclic overlap gives the positive spectral lower envelope on
--       the SAME continuum covariance carrier;
--   F4. physical subgap rate semantics: a positive energy below the candidate
--       carries positive spectral amplitude and a strictly slower decay ratio;
--   F5. the direct clustering ratio q=1/2 is the SAME reconstructed candidate
--       energy under the physical OS/transfer-semigroup convention.
--
-- No claim of Clay closure is made here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact as Geometric293
import DASHI.Physics.YangMills.BalabanClusteringDecayRatioToGapRound285Exact as R285
import DASHI.Physics.YangMills.BalabanClayT5OSReconstructionCyclicityExact as Cyclic


data DirectBSearchObject298 : Set where
  literalAbsoluteJLocalization : DirectBSearchObject298
  physicalPositiveTimeCyclicity : DirectBSearchObject298
  physicalSpectralLowerFromOverlap : DirectBSearchObject298
  physicalSubgapRateSemantics : DirectBSearchObject298
  clusteringRateToSpectrumEnergy : DirectBSearchObject298

  signedLogDerivativeCovariance : DirectBSearchObject298
  sourceCovarianceSelectedT5SameObject : DirectBSearchObject298
  signedMagnitudeConflationRepair : DirectBSearchObject298
  arbitrarySubgapNonzeroMeaning : DirectBSearchObject298
  observableChoiceAndOverlap : DirectBSearchObject298
  opaqueSeparatingTime : DirectBSearchObject298
  fullSlowFastContradiction : DirectBSearchObject298
  positiveTransferGap : DirectBSearchObject298

searchRole298 : DirectBSearchObject298 → Introspective.ProofSearchTargetRole
searchRole298 literalAbsoluteJLocalization = Introspective.canonicalConsumerResidual
searchRole298 physicalPositiveTimeCyclicity = Introspective.canonicalConsumerResidual
searchRole298 physicalSpectralLowerFromOverlap = Introspective.canonicalConsumerResidual
searchRole298 physicalSubgapRateSemantics = Introspective.canonicalConsumerResidual
searchRole298 clusteringRateToSpectrumEnergy = Introspective.canonicalConsumerResidual

searchRole298 signedLogDerivativeCovariance = Introspective.compilerConsequence
searchRole298 sourceCovarianceSelectedT5SameObject = Introspective.compilerConsequence
searchRole298 signedMagnitudeConflationRepair = Introspective.compilerConsequence
searchRole298 arbitrarySubgapNonzeroMeaning = Introspective.compilerConsequence
searchRole298 observableChoiceAndOverlap = Introspective.compilerConsequence
searchRole298 opaqueSeparatingTime = Introspective.compilerConsequence
searchRole298 fullSlowFastContradiction = Introspective.compilerConsequence
searchRole298 positiveTransferGap = Introspective.compilerConsequence

record Round298Boundary : Set where
  constructor round298-boundary
  field
    sourceCovarianceT5SameObjectStillPhysical : Bool
    sourceCovarianceT5SameObjectStillPhysicalIsFalse :
      sourceCovarianceT5SameObjectStillPhysical ≡ false

    signedCumulantTreatedAsMagnitude : Bool
    signedCumulantTreatedAsMagnitudeIsFalse :
      signedCumulantTreatedAsMagnitude ≡ false

    subgapNonzeroInterpretationSeparatePhysicalLeaf : Bool
    subgapNonzeroInterpretationSeparatePhysicalLeafIsFalse :
      subgapNonzeroInterpretationSeparatePhysicalLeaf ≡ false

    opaqueSeparatingTimePhysicalLeaf : Bool
    opaqueSeparatingTimePhysicalLeafIsFalse :
      opaqueSeparatingTimePhysicalLeaf ≡ false

    positiveTimeCyclicityHiddenInsideConstructedCore : Bool
    positiveTimeCyclicityHiddenInsideConstructedCoreIsFalse :
      positiveTimeCyclicityHiddenInsideConstructedCore ≡ false

    honestDirectPhysicalCutHasFiveCoordinates : Bool
    honestDirectPhysicalCutHasFiveCoordinatesIsTrue :
      honestDirectPhysicalCutHasFiveCoordinates ≡ true

canonicalRound298Boundary : Round298Boundary
canonicalRound298Boundary =
  round298-boundary false refl false refl false refl false refl false refl true refl

round298DirectB1ShellCompilerLevel : ProofLevel
round298DirectB1ShellCompilerLevel = R296.round296DirectB1ShellCompilerLevel

round298ActualNonzeroSubgapCompilerLevel : ProofLevel
round298ActualNonzeroSubgapCompilerLevel = R297.round297ActualNonzeroSubgapCompilerLevel

round298SeparatingTimeCompilerLevel : ProofLevel
round298SeparatingTimeCompilerLevel = Geometric293.round293SeparatingTimeCompilerLevel

round298LiteralAbsoluteJLocalizationLevel : ProofLevel
round298LiteralAbsoluteJLocalizationLevel =
  R296.round296LiteralAbsoluteTwoJLocalizationLevel

round298PhysicalPositiveTimeCyclicityLevel : ProofLevel
round298PhysicalPositiveTimeCyclicityLevel =
  R297.round297PhysicalPositiveTimeCyclicityLevel

round298PhysicalSpectralLowerFromOverlapLevel : ProofLevel
round298PhysicalSpectralLowerFromOverlapLevel =
  Cyclic.physicalSpectralLowerBoundFromOverlapInputsLevel

round298PhysicalSubgapRateSemanticsLevel : ProofLevel
round298PhysicalSubgapRateSemanticsLevel =
  Geometric293.round293PhysicalSubgapRateSemanticsLevel

round298ClusteringRateToSpectrumEnergyLevel : ProofLevel
round298ClusteringRateToSpectrumEnergyLevel =
  R285.round285PhysicalRateToSpectrumIdentificationLevel
