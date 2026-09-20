{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteANumeratorExact where

------------------------------------------------------------------------
-- A / LITERAL NUMERATOR CHANGE OF VARIABLES -> CONCRETE A
--
-- Finite Euclidean and bosonic symmetries are naturally proved before
-- normalization: product-Haar change of variables preserves the Gibbs/Wilson
-- numerator.  The partition function is unchanged because it is the common
-- denominator.  This owner makes that least-privilege route the preferred
-- constructor for ConcreteA.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsFiniteNormalizedExpectationSymmetryExact as Sym
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteAExact as A
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedCMP119ConcreteANumeratorInputs
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

    finiteEuclideanNumeratorInvariant :
      ∀ G →
      Sym.FiniteNumeratorActionInvariant
        (family G) euclideanAct

    permute :
      Permutation → (Configuration → ℝ) → (Configuration → ℝ)

    finitePermutationNumeratorInvariant :
      ∀ G →
      Sym.FiniteNumeratorActionInvariant
        (family G) permute

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
      DASHI.Physics.YangMills.FiniteReflectionPositivity.sumTerms
        A.realPositiveAdditiveScalar
        (squareTerm G cutoff testFamily)
        (indices G cutoff testFamily)

    OS0Regularity : CompactSimpleGroup → Set
    OS4Clustering : CompactSimpleGroup → Set
    OS5GrowthControl : CompactSimpleGroup → Set
    os0 : ∀ G → OS0Regularity G
    os4 : ∀ G → OS4Clustering G
    os5 : ∀ G → OS5GrowthControl G

open PinnedCMP119ConcreteANumeratorInputs public

asConcreteAInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
      sequenceLimit limitLaws quotient division S} →
  PinnedCMP119ConcreteANumeratorInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  A.PinnedCMP119ConcreteAInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
asConcreteAInputs inputs = record
  { A.PinnedCMP119ConcreteAInputs.family = family inputs
  ; A.PinnedCMP119ConcreteAInputs.cylinderEncoding = cylinderEncoding inputs
  ; A.PinnedCMP119ConcreteAInputs.observableAlgebra = observableAlgebra inputs
  ; A.PinnedCMP119ConcreteAInputs.euclideanAct = euclideanAct inputs
  ; A.PinnedCMP119ConcreteAInputs.finiteEuclideanInvariant =
      λ G cutoff action observable →
        Sym.finiteNormalizedExpectationInvariantFromNumerator
          (family inputs G)
          (euclideanAct inputs)
          (finiteEuclideanNumeratorInvariant inputs G)
          cutoff action observable
  ; A.PinnedCMP119ConcreteAInputs.permute = permute inputs
  ; A.PinnedCMP119ConcreteAInputs.finitePermutationInvariant =
      λ G cutoff permutation observable →
        Sym.finiteNormalizedExpectationInvariantFromNumerator
          (family inputs G)
          (permute inputs)
          (finitePermutationNumeratorInvariant inputs G)
          cutoff permutation observable
  ; A.PinnedCMP119ConcreteAInputs.Interface = Interface inputs
  ; A.PinnedCMP119ConcreteAInputs.indices = indices inputs
  ; A.PinnedCMP119ConcreteAInputs.squareTerm = squareTerm inputs
  ; A.PinnedCMP119ConcreteAInputs.squareTermNonnegative =
      squareTermNonnegative inputs
  ; A.PinnedCMP119ConcreteAInputs.peterWeylWilsonFactorization =
      peterWeylWilsonFactorization inputs
  ; A.PinnedCMP119ConcreteAInputs.OS0Regularity = OS0Regularity inputs
  ; A.PinnedCMP119ConcreteAInputs.OS4Clustering = OS4Clustering inputs
  ; A.PinnedCMP119ConcreteAInputs.OS5GrowthControl = OS5GrowthControl inputs
  ; A.PinnedCMP119ConcreteAInputs.os0 = os0 inputs
  ; A.PinnedCMP119ConcreteAInputs.os4 = os4 inputs
  ; A.PinnedCMP119ConcreteAInputs.os5 = os5 inputs
  }

numeratorSymmetryToConcreteACompilerLevel : ProofLevel
numeratorSymmetryToConcreteACompilerLevel = machineChecked

-- The A1/A3 physical leaf is now exactly the finite product-Haar/Gibbs
-- change-of-variables theorem for the unnormalized numerator.
literalFiniteNumeratorChangeOfVariablesLevel : ProofLevel
literalFiniteNumeratorChangeOfVariablesLevel = conditional
