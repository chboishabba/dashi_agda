{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119WilsonSquareOS2Exact where

------------------------------------------------------------------------
-- A / LITERAL WILSON SQUARE FACTORIZATION -> PINNED CMP119 FINITE OS2
--
-- Non-circular preferred constructor.  The input stops BEFORE finite OS2:
-- it carries the literal normalized CMP119 family and a per-cutoff,
-- per-test-family Wilson/Haar square factorization.  FiniteReflectionPositivity
-- compiles that factorization into the Gram inequality, and only then do we
-- construct PinnedCMP119OSAxiomInputs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _≤ℝ_; ≤ℝ-refl; +-mono-≤)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.FiniteReflectionPositivity as FiniteRP
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
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

record PinnedCMP119WilsonSquareOSInputs
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState : Set)
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
      ≡
      FiniteRP.sumTerms realPositiveAdditiveScalar
        (squareTerm G cutoff testFamily)
        (indices G cutoff testFamily)

    OS0Regularity : CompactSimpleGroup → Set
    OS1EuclideanCovariance : CompactSimpleGroup → Set
    OS3PermutationSymmetry : CompactSimpleGroup → Set
    OS4Clustering : CompactSimpleGroup → Set
    OS5GrowthControl : CompactSimpleGroup → Set

    os0 : ∀ G → OS0Regularity G
    os1 : ∀ G → OS1EuclideanCovariance G
    os3 : ∀ G → OS3PermutationSymmetry G
    os4 : ∀ G → OS4Clustering G
    os5 : ∀ G → OS5GrowthControl G

open PinnedCMP119WilsonSquareOSInputs public

asReflectionSquareFactorization :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119WilsonSquareOSInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group cutoff testFamily →
  FiniteRP.ReflectionSquareFactorization
    (Gram.PhysicalOSFiniteTestFamily (Configuration → ℝ) ℝ)
    (Interface inputs)
    ℝ
    realPositiveAdditiveScalar
asReflectionSquareFactorization inputs group cutoff testFamily = record
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

finiteCMP119ReflectionPositiveFromWilsonSquares :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S}
    (inputs :
      PinnedCMP119WilsonSquareOSInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S) →
  ∀ group cutoff testFamily →
  0ℝ ≤ℝ
    Gram.physicalReflectedGramQuadraticForm
      (OS2.operations (observableAlgebra inputs))
      (λ observable →
        Limit.finiteExpectation (family inputs group) cutoff observable)
      testFamily
finiteCMP119ReflectionPositiveFromWilsonSquares inputs group cutoff testFamily =
  FiniteRP.osFormNonnegative
    (asReflectionSquareFactorization inputs group cutoff testFamily)
    testFamily

asPinnedOSAxiomInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S} →
  PinnedCMP119WilsonSquareOSInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  Pinned.PinnedCMP119OSAxiomInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
asPinnedOSAxiomInputs inputs = record
  { Pinned.PinnedCMP119OSAxiomInputs.family =
      family inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.cylinderEncoding =
      cylinderEncoding inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.observableAlgebra =
      observableAlgebra inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.finiteReflectionPositive =
      finiteCMP119ReflectionPositiveFromWilsonSquares inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.OS0Regularity =
      OS0Regularity inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.OS1EuclideanCovariance =
      OS1EuclideanCovariance inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.OS3PermutationSymmetry =
      OS3PermutationSymmetry inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.OS4Clustering =
      OS4Clustering inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.OS5GrowthControl =
      OS5GrowthControl inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.os0 =
      os0 inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.os1 =
      os1 inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.os3 =
      os3 inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.os4 =
      os4 inputs
  ; Pinned.PinnedCMP119OSAxiomInputs.os5 =
      os5 inputs
  }

pinnedWilsonSquareToFiniteOS2CompilerLevel : ProofLevel
pinnedWilsonSquareToFiniteOS2CompilerLevel = machineChecked

pinnedWilsonSquareOSSystemAdapterLevel : ProofLevel
pinnedWilsonSquareOSSystemAdapterLevel = machineChecked

-- Genuine physical leaf after this recut: identify the literal normalized
-- CMP119 finite Wilson/Haar Gram form with its Peter-Weyl interface squares.
literalCMP119WilsonPeterWeylFactorizationLevel : ProofLevel
literalCMP119WilsonPeterWeylFactorizationLevel = conditional
