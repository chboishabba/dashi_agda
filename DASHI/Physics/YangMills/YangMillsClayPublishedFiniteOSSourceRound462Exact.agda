{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSSourceRound462Exact where

------------------------------------------------------------------------
-- GOAL-1 A1/A2 / ROUND462: SOURCE-FED FINITE OS CONSTRUCTOR.
--
-- Preferred human-proof route:
--   * CMP119 whole-lattice Euclidean covariance: published/source authority;
--   * bosonic permutation symmetry: standard finite source symmetry;
--   * Wilson reflection positivity: Osterwalder--Seiler /
--     Menotti--Pelissetto, attached by R461;
--   * OS0/OS5: canonical limit closure after uniform finite estimates;
--   * OS4: supplied by the selected B/common-continuum clustering route.
--
-- Therefore explicit product-Haar change-of-variables and explicit
-- Peter--Weyl square reconstruction are optional constructive audits, not
-- mandatory Goal-1 theorem leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119FiniteEuclideanSourceExact as Euclidean
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119BosonicOS3SourceExact as Bosonic
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact as OS05
import DASHI.Physics.YangMills.YangMillsClayPublishedWilsonRPRound461Exact as R461
import DASHI.Physics.YangMills.BalabanCylinderLimitActionInvariantExact as ActionLimit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PublishedFiniteOSSource
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState EuclideanAction Permutation : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          CompactSimpleGroup Spacetime Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          HilbertSpace Hamiltonian VacuumState))
    : Set₂ where
  field
    family : ∀ group →
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division

    cylinderEncoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position

    observableAlgebra :
      OS2.CylinderOSAlgebra (Configuration → ℝ)

    euclidean :
      ∀ group →
      Euclidean.CMP119WholeLatticeEuclideanCovariance
        Configuration EuclideanAction (family group)

    bosonic :
      ∀ group →
      Bosonic.LiteralCMP119BosonicPermutationSymmetry
        Configuration Permutation (family group)

    wilsonRP :
      ∀ group →
      R461.PublishedWilsonRPApplication
        Configuration (family group) observableAlgebra

    os05 :
      ∀ group →
      OS05.CanonicalCMP119OS05LimitData
        Configuration (family group)

    OS4Clustering : CompactSimpleGroup → Set
    os4 : ∀ group → OS4Clustering group

open PublishedFiniteOSSource public

euclideanLimitInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      PublishedFiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  ActionLimit.CylinderActionInvariantInputs
    (Limit.asCylinderLimitData (family source group))
    EuclideanAction
euclideanLimitInputs source group = record
  { ActionLimit.CylinderActionInvariantInputs.act =
      Euclidean.actObservable (euclidean source group)
  ; ActionLimit.CylinderActionInvariantInputs.finiteActionInvariant =
      Euclidean.finiteEuclideanInvariant (euclidean source group)
  }

bosonicLimitInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      PublishedFiniteOSSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  ActionLimit.CylinderActionInvariantInputs
    (Limit.asCylinderLimitData (family source group))
    Permutation
bosonicLimitInputs source group = record
  { ActionLimit.CylinderActionInvariantInputs.act =
      Bosonic.permuteObservable (bosonic source group)
  ; ActionLimit.CylinderActionInvariantInputs.finiteActionInvariant =
      Bosonic.finitePermutationInvariant (bosonic source group)
  }

asPinnedOSAxiomInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S} →
  PublishedFiniteOSSource
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    EuclideanAction Permutation
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  Pinned.PinnedCMP119OSAxiomInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
asPinnedOSAxiomInputs source = record
  { Pinned.PinnedCMP119OSAxiomInputs.family =
      family source
  ; Pinned.PinnedCMP119OSAxiomInputs.cylinderEncoding =
      cylinderEncoding source
  ; Pinned.PinnedCMP119OSAxiomInputs.observableAlgebra =
      observableAlgebra source
  ; Pinned.PinnedCMP119OSAxiomInputs.finiteReflectionPositive =
      λ group →
        R461.finiteReflectionPositiveFromPublishedWilson
          (wilsonRP source group)
  ; Pinned.PinnedCMP119OSAxiomInputs.OS0Regularity =
      λ group →
        OS05.ContinuumRegularity (os05 source group)
          (Limit.limitExpectation (family source group))
  ; Pinned.PinnedCMP119OSAxiomInputs.OS1EuclideanCovariance =
      λ group → ∀ action observable →
        Limit.limitExpectation (family source group)
          (Euclidean.actObservable
            (euclidean source group) action observable)
        ≡ Limit.limitExpectation (family source group) observable
  ; Pinned.PinnedCMP119OSAxiomInputs.OS3PermutationSymmetry =
      λ group → ∀ permutation observable →
        Limit.limitExpectation (family source group)
          (Bosonic.permuteObservable
            (bosonic source group) permutation observable)
        ≡ Limit.limitExpectation (family source group) observable
  ; Pinned.PinnedCMP119OSAxiomInputs.OS4Clustering =
      OS4Clustering source
  ; Pinned.PinnedCMP119OSAxiomInputs.OS5GrowthControl =
      λ group →
        OS05.ContinuumGrowthControl (os05 source group)
          (Limit.limitExpectation (family source group))
  ; Pinned.PinnedCMP119OSAxiomInputs.os0 =
      λ group → OS05.canonicalCMP119OS0 (os05 source group)
  ; Pinned.PinnedCMP119OSAxiomInputs.os1 =
      λ group →
        ActionLimit.continuumActionInvariant
          (euclideanLimitInputs source group)
  ; Pinned.PinnedCMP119OSAxiomInputs.os3 =
      λ group →
        ActionLimit.continuumActionInvariant
          (bosonicLimitInputs source group)
  ; Pinned.PinnedCMP119OSAxiomInputs.os4 =
      os4 source
  ; Pinned.PinnedCMP119OSAxiomInputs.os5 =
      λ group → OS05.canonicalCMP119OS5 (os05 source group)
  }

round462PublishedFiniteOSCompilerLevel : ProofLevel
round462PublishedFiniteOSCompilerLevel = machineChecked

a1ExplicitHaarReconstructionMandatory : Agda.Builtin.Bool.Bool
a1ExplicitHaarReconstructionMandatory = Agda.Builtin.Bool.false

a2ExplicitPeterWeylReconstructionMandatory : Agda.Builtin.Bool.Bool
a2ExplicitPeterWeylReconstructionMandatory = Agda.Builtin.Bool.false

-- Preferred A1/A2 source payments are now the literal attachments to the
-- published finite symmetry/RP theorems.
literalRound462PublishedFiniteOSApplicationLevel : ProofLevel
literalRound462PublishedFiniteOSApplicationLevel = conditional
