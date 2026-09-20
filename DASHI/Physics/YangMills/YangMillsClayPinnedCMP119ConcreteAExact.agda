{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteAExact where

------------------------------------------------------------------------
-- A / ONE LITERAL CMP119 FAMILY -> CONCRETE OS1 + OS2 + OS3
--
-- Preferred A constructor.  One normalized finite CMP119 family supplies:
--
--   finite Euclidean invariance     -> continuum OS1
--   Wilson/Haar square factorization -> finite RP -> continuum OS2
--   finite bosonic permutation symmetry -> continuum OS3
--
-- OS0 and OS5 remain separate analytic regularity/growth inputs. OS4 is B.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _≤ℝ_; ≤ℝ-refl; +-mono-≤)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.FiniteReflectionPositivity as FiniteRP
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanCylinderLimitActionInvariantExact as ActionLimit
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as Pinned
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

realPositiveAdditiveScalar : FiniteRP.PositiveAdditiveScalar ℝ
realPositiveAdditiveScalar = record
  { FiniteRP.PositiveAdditiveScalar.zero = 0ℝ
  ; FiniteRP.PositiveAdditiveScalar.add = _+ℝ_
  ; FiniteRP.PositiveAdditiveScalar.Nonnegative = λ x → 0ℝ ≤ℝ x
  ; FiniteRP.PositiveAdditiveScalar.zeroNonnegative = ≤ℝ-refl
  ; FiniteRP.PositiveAdditiveScalar.addNonnegative = +-mono-≤
  }

record PinnedCMP119ConcreteAInputs
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
          HilbertSpace Hamiltonian VacuumState)) : Set₂ where
  field
    family : ∀ G →
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division

    cylinderEncoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position

    observableAlgebra :
      OS2.CylinderOSAlgebra (Configuration → ℝ)

    euclideanAct :
      EuclideanAction → (Configuration → ℝ) → (Configuration → ℝ)

    finiteEuclideanInvariant :
      ∀ G cutoff action observable →
      Limit.finiteExpectation (family G) cutoff
        (euclideanAct action observable)
      ≡ Limit.finiteExpectation (family G) cutoff observable

    permute :
      Permutation → (Configuration → ℝ) → (Configuration → ℝ)

    finitePermutationInvariant :
      ∀ G cutoff permutation observable →
      Limit.finiteExpectation (family G) cutoff
        (permute permutation observable)
      ≡ Limit.finiteExpectation (family G) cutoff observable

    Interface : Set
    indices :
      ∀ G cutoff
        (testFamily :
          Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
      List Interface
    squareTerm :
      ∀ G cutoff
        (testFamily :
          Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ) →
      Interface → ℝ
    squareTermNonnegative :
      ∀ G cutoff testFamily index →
      0ℝ ≤ℝ squareTerm G cutoff testFamily index
    peterWeylWilsonFactorization :
      ∀ G cutoff testFamily →
      Gram.physicalReflectedGramQuadraticForm
        (OS2.operations observableAlgebra)
        (λ observable →
          Limit.finiteExpectation (family G) cutoff observable)
        testFamily
      ≡ FiniteRP.sumTerms realPositiveAdditiveScalar
          (squareTerm G cutoff testFamily)
          (indices G cutoff testFamily)

    OS0Regularity : CompactSimpleGroup → Set
    OS4Clustering : CompactSimpleGroup → Set
    OS5GrowthControl : CompactSimpleGroup → Set
    os0 : ∀ G → OS0Regularity G
    os4 : ∀ G → OS4Clustering G
    os5 : ∀ G → OS5GrowthControl G

open PinnedCMP119ConcreteAInputs public

euclideanInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119ConcreteAInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  ActionLimit.CylinderActionInvariantInputs
    (Limit.asCylinderLimitData (family inputs group)) Action
euclideanInputs inputs group = record
  { ActionLimit.CylinderActionInvariantInputs.act = euclideanAct inputs
  ; ActionLimit.CylinderActionInvariantInputs.finiteActionInvariant =
      finiteEuclideanInvariant inputs group
  }

permutationInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119ConcreteAInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  ActionLimit.CylinderActionInvariantInputs
    (Limit.asCylinderLimitData (family inputs group)) Permutation
permutationInputs inputs group = record
  { ActionLimit.CylinderActionInvariantInputs.act = permute inputs
  ; ActionLimit.CylinderActionInvariantInputs.finiteActionInvariant =
      finitePermutationInvariant inputs group
  }

continuumEuclideanInvariant :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119ConcreteAInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group action observable →
  Limit.limitExpectation (family inputs group)
    (euclideanAct inputs action observable)
  ≡ Limit.limitExpectation (family inputs group) observable
continuumEuclideanInvariant inputs group =
  ActionLimit.continuumActionInvariant (euclideanInputs inputs group)

continuumPermutationInvariant :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119ConcreteAInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group permutation observable →
  Limit.limitExpectation (family inputs group)
    (permute inputs permutation observable)
  ≡ Limit.limitExpectation (family inputs group) observable
continuumPermutationInvariant inputs group =
  ActionLimit.continuumActionInvariant (permutationInputs inputs group)

finiteReflectionPositive :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119ConcreteAInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group cutoff testFamily →
  0ℝ ≤ℝ
    Gram.physicalReflectedGramQuadraticForm
      (OS2.operations (observableAlgebra inputs))
      (λ observable →
        Limit.finiteExpectation (family inputs group) cutoff observable)
      testFamily
finiteReflectionPositive inputs group cutoff testFamily =
  let
    factorization :
      FiniteRP.ReflectionSquareFactorization
        (Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ)
        (Interface inputs) ℝ realPositiveAdditiveScalar
    factorization = record
      { FiniteRP.ReflectionSquareFactorization.indices =
          indices inputs group cutoff testFamily
      ; FiniteRP.ReflectionSquareFactorization.squareTerm =
          λ _ index → squareTerm inputs group cutoff testFamily index
      ; FiniteRP.ReflectionSquareFactorization.squareTermNonnegative =
          λ _ index → squareTermNonnegative inputs group cutoff testFamily index
      ; FiniteRP.ReflectionSquareFactorization.osForm =
          λ family' →
            Gram.physicalReflectedGramQuadraticForm
              (OS2.operations (observableAlgebra inputs))
              (λ observable →
                Limit.finiteExpectation (family inputs group) cutoff observable)
              family'
      ; FiniteRP.ReflectionSquareFactorization.factorization =
          λ _ → peterWeylWilsonFactorization inputs group cutoff testFamily
      }
  in
  FiniteRP.osFormNonnegative factorization testFamily

asPinnedOSAxiomInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
      sequenceLimit limitLaws quotient division S} →
  PinnedCMP119ConcreteAInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  Pinned.PinnedCMP119OSAxiomInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
asPinnedOSAxiomInputs inputs = record
  { Pinned.PinnedCMP119OSAxiomInputs.family = family inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.cylinderEncoding = cylinderEncoding inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.observableAlgebra = observableAlgebra inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.finiteReflectionPositive =
      finiteReflectionPositive inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.OS0Regularity = OS0Regularity inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.OS1EuclideanCovariance =
      λ G → ∀ action observable →
        Limit.limitExpectation (family inputs G)
          (euclideanAct inputs action observable)
        ≡ Limit.limitExpectation (family inputs G) observable
  ; Pinned.PinnedCMP119OSAxiomInputs.OS3PermutationSymmetry =
      λ G → ∀ permutation observable →
        Limit.limitExpectation (family inputs G)
          (permute inputs permutation observable)
        ≡ Limit.limitExpectation (family inputs G) observable
  ; Pinned.PinnedCMP119OSAxiomInputs.OS4Clustering = OS4Clustering inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.OS5GrowthControl = OS5GrowthControl inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.os0 = os0 inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.os1 = continuumEuclideanInvariant inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.os3 = continuumPermutationInvariant inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.os4 = os4 inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.os5 = os5 inputs
  }

concreteAOS123CompilerLevel : ProofLevel
concreteAOS123CompilerLevel = machineChecked

-- Remaining A physics after consolidation:
-- * literal finite Euclidean invariance on the selected lattice/cylinder action;
-- * literal Wilson/Haar Peter-Weyl square factorization;
-- * literal finite bosonic permutation invariance;
-- * OS0 regularity and OS5 growth on the same limit.
-- OS4 is supplied by B.
literalConcreteAFiniteSymmetryAndWilsonInputsLevel : ProofLevel
literalConcreteAFiniteSymmetryAndWilsonInputsLevel = conditional

literalConcreteAOS0OS5Level : ProofLevel
literalConcreteAOS0OS5Level = conditional
