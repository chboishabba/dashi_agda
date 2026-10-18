{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteAFromSourcesExact where

------------------------------------------------------------------------
-- A / SOURCE-FED ONE-FAMILY PINNED OS CONSTRUCTOR
--
-- Construct PinnedCMP119OSAxiomInputs directly.  This deliberately avoids
-- forcing all compact-simple groups to share one artificial Wilson
-- Peter-Weyl interface type.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.BalabanCylinderLimitActionInvariantExact as ActionLimit
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119FiniteEuclideanSourceExact as Euclidean
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119BosonicOS3SourceExact as Bosonic
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StandaloneWilsonSquareExact as Wilson
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact as OS05
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record ConcreteAFromSources
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
    family : ∀ G →
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division

    cylinderEncoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position

    observableAlgebra :
      OS2.CylinderOSAlgebra (Configuration → ℝ)

    euclidean :
      ∀ G →
      Euclidean.CMP119WholeLatticeEuclideanCovariance
        Configuration EuclideanAction (family G)

    bosonic :
      ∀ G →
      Bosonic.LiteralCMP119BosonicPermutationSymmetry
        Configuration Permutation (family G)

    wilson :
      ∀ G →
      Wilson.StandaloneCMP119WilsonSquare
        Configuration (family G) observableAlgebra

    os05 :
      ∀ G →
      OS05.CanonicalCMP119OS05LimitData
        Configuration (family G)

    OS4Clustering : CompactSimpleGroup → Set
    os4 : ∀ G → OS4Clustering G

open ConcreteAFromSources public

euclideanLimitInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      ConcreteAFromSources
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
      ConcreteAFromSources
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

continuumEuclideanInvariant :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      ConcreteAFromSources
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group action observable →
  Limit.limitExpectation (family source group)
    (Euclidean.actObservable (euclidean source group) action observable)
  ≡ Limit.limitExpectation (family source group) observable
continuumEuclideanInvariant source group =
  ActionLimit.continuumActionInvariant
    (euclideanLimitInputs source group)

continuumBosonicInvariant :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      ConcreteAFromSources
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group permutation observable →
  Limit.limitExpectation (family source group)
    (Bosonic.permuteObservable (bosonic source group) permutation observable)
  ≡ Limit.limitExpectation (family source group) observable
continuumBosonicInvariant source group =
  ActionLimit.continuumActionInvariant
    (bosonicLimitInputs source group)

asPinnedOSAxiomInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S} →
  ConcreteAFromSources
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
        Wilson.finiteReflectionPositive (wilson source group)
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
      continuumEuclideanInvariant source
  ; Pinned.PinnedCMP119OSAxiomInputs.os3 =
      continuumBosonicInvariant source
  ; Pinned.PinnedCMP119OSAxiomInputs.os4 =
      os4 source
  ; Pinned.PinnedCMP119OSAxiomInputs.os5 =
      λ group → OS05.canonicalCMP119OS5 (os05 source group)
  }

sourceFedPinnedOSCompilerLevel : ProofLevel
sourceFedPinnedOSCompilerLevel = machineChecked

literalConcreteAFromSourcesLevel : ProofLevel
literalConcreteAFromSourcesLevel = conditional
