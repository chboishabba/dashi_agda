{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteAFromSourcesExact where

------------------------------------------------------------------------
-- A / SOURCE-FED ONE-FAMILY CONSTRUCTOR
--
-- One literal normalized CMP119 family is fed by:
--
--   CMP119 whole-lattice Euclidean covariance,
--   literal Wilson/Haar square factorization,
--   finite bosonic permutation symmetry,
--   canonical-limit OS0/OS5 regularity/growth,
--   B's clustering theorem.
--
-- The output is the existing PinnedCMP119ConcreteAInputs, hence ultimately the
-- exact PinnedCMP119OSAxiomInputs consumed by reconstruction.  No parallel
-- continuum or Schwinger object is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteAExact as A
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

    -- B owns OS4; this constructor merely consumes its theorem on the same
    -- selected group/family.
    OS4Clustering : CompactSimpleGroup → Set
    os4 : ∀ G → OS4Clustering G

open ConcreteAFromSources public

asConcreteA :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S} →
  ConcreteAFromSources
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    EuclideanAction Permutation
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  A.PinnedCMP119ConcreteAInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    EuclideanAction Permutation
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
asConcreteA source = record
  { A.PinnedCMP119ConcreteAInputs.family =
      family source
  ; A.PinnedCMP119ConcreteAInputs.cylinderEncoding =
      cylinderEncoding source
  ; A.PinnedCMP119ConcreteAInputs.observableAlgebra =
      observableAlgebra source
  ; A.PinnedCMP119ConcreteAInputs.euclideanAct =
      Euclidean.actObservable (euclidean source _)
  ; A.PinnedCMP119ConcreteAInputs.finiteEuclideanInvariant =
      λ group →
        Euclidean.finiteEuclideanInvariant (euclidean source group)
  ; A.PinnedCMP119ConcreteAInputs.permute =
      Bosonic.permuteObservable (bosonic source _)
  ; A.PinnedCMP119ConcreteAInputs.finitePermutationInvariant =
      λ group →
        Bosonic.finitePermutationInvariant (bosonic source group)
  ; A.PinnedCMP119ConcreteAInputs.Interface =
      Σ G (λ group → Wilson.Interface (wilson source group))
  ; A.PinnedCMP119ConcreteAInputs.indices =
      λ group cutoff testFamily →
        Data.List.Base.map
          (λ index → group , index)
          (Wilson.indices (wilson source group) cutoff testFamily)
  ; A.PinnedCMP119ConcreteAInputs.squareTerm =
      λ group cutoff testFamily tagged →
        Wilson.squareTerm
          (wilson source (Agda.Builtin.Sigma.fst tagged))
          cutoff testFamily
          (Agda.Builtin.Sigma.snd tagged)
  ; A.PinnedCMP119ConcreteAInputs.squareTermNonnegative =
      λ group cutoff testFamily tagged →
        Wilson.squareTermNonnegative
          (wilson source (Agda.Builtin.Sigma.fst tagged))
          cutoff testFamily
          (Agda.Builtin.Sigma.snd tagged)
  ; A.PinnedCMP119ConcreteAInputs.peterWeylWilsonFactorization =
      λ group cutoff testFamily →
        Wilson.peterWeylWilsonFactorization
          (wilson source group) cutoff testFamily
  ; A.PinnedCMP119ConcreteAInputs.OS0Regularity =
      λ group →
        OS05.ContinuumRegularity (os05 source group)
          (Limit.limitExpectation (family source group))
  ; A.PinnedCMP119ConcreteAInputs.OS4Clustering =
      OS4Clustering source
  ; A.PinnedCMP119ConcreteAInputs.OS5GrowthControl =
      λ group →
        OS05.ContinuumGrowthControl (os05 source group)
          (Limit.limitExpectation (family source group))
  ; A.PinnedCMP119ConcreteAInputs.os0 =
      λ group → OS05.canonicalCMP119OS0 (os05 source group)
  ; A.PinnedCMP119ConcreteAInputs.os4 =
      os4 source
  ; A.PinnedCMP119ConcreteAInputs.os5 =
      λ group → OS05.canonicalCMP119OS5 (os05 source group)
  }

concreteAFromSourcesCompilerLevel : ProofLevel
concreteAFromSourcesCompilerLevel = machineChecked

-- Source/application leaves left by this constructor:
-- * literal CMP119 whole-lattice covariance attachment;
-- * literal Wilson square/source RP identification;
-- * literal bosonic observable/permutation attachment;
-- * uniform finite regularity and growth estimates;
-- * B's same-family clustering theorem.
literalConcreteAFromSourcesLevel : ProofLevel
literalConcreteAFromSourcesLevel = conditional
