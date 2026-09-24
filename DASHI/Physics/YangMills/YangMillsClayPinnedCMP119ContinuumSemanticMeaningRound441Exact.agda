{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ContinuumSemanticMeaningRound441Exact where

------------------------------------------------------------------------
-- ROUND441 / CONCRETE CMP119 CONTINUUM OBJECTS -> LITERAL CLAY SEMANTICS
--
-- The continuum expectation functional is already constructed by
-- YangMillsFinitePhysicalMeasureLimitExact:
--
--   E_infty(F) = lim_n E_n(F).
--
-- The continuum Schwinger family is already constructed from that SAME
-- expectation functional by YangMillsContinuumSchwingerFromMeasureExact.
--
-- Therefore source-native A3 should not accept two opaque witnesses saying
-- "continuum limit" and "Schwinger belongs".  Its remaining physical content is
-- exactly the semantic interpretation of those concrete constructions in the
-- literal Clay vocabulary.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record ConcreteCMP119ContinuumSemanticMeaning
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum : Set)
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
          G X Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    (group : G)
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    (encoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position)
    : Set₂ where
  field
    -- Literal semantic meaning of the already-constructed all-observable
    -- expectation limit.  The convergence witness itself is compiler-owned.
    expectationLimitMeansLiteralContinuum :
      (∀ observable →
        Cylinder.Converges
          (RealLimit.canonicalCylinderAlgebra limitLaws)
          (λ cutoff → Limit.finiteExpectation family cutoff observable)
          (Limit.limitExpectation family observable)) →
      Top.IsContinuumLimitOf S group
        (Limit.finiteMeasure family)
        (Limit.continuumMeasure family)

    -- Literal semantic meaning of the already-constructed Schwinger functional.
    -- Its pointwise same-measure equation is compiler-owned below.
    sameMeasureSchwingerMeansLiteralBelonging :
      (∀ observable left right →
        Physical.schwinger
          (Schwinger.schwingerFromMeasure
            encoding (Limit.continuumMeasure family))
          observable left right
        ≡
        Physical.expectation
          (Limit.continuumMeasure family)
          (Schwinger.twoPointCylinder encoding observable left right)) →
      Top.SchwingerBelongsToMeasure S
        (Limit.continuumMeasure family)
        (Schwinger.schwingerFromMeasure
          encoding (Limit.continuumMeasure family))

open ConcreteCMP119ContinuumSemanticMeaning public

concreteExpectationLimitConverges :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S group family encoding}
    (meaning :
      ConcreteCMP119ContinuumSemanticMeaning
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S group family encoding) →
  ∀ observable →
  Cylinder.Converges
    (RealLimit.canonicalCylinderAlgebra limitLaws)
    (λ cutoff → Limit.finiteExpectation family cutoff observable)
    (Limit.limitExpectation family observable)
concreteExpectationLimitConverges {family = family} meaning observable =
  Cylinder.selectedConverges
    (Limit.asCylinderLimitData family)
    observable

literalContinuumLimitFromConcreteExpectationLimit :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S group family encoding}
    (meaning :
      ConcreteCMP119ContinuumSemanticMeaning
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S group family encoding) →
  Top.IsContinuumLimitOf S group
    (Limit.finiteMeasure family)
    (Limit.continuumMeasure family)
literalContinuumLimitFromConcreteExpectationLimit meaning =
  expectationLimitMeansLiteralContinuum meaning
    (concreteExpectationLimitConverges meaning)

literalSchwingerBelongsFromConcreteSameMeasure :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      sequenceLimit limitLaws quotient division S group family encoding}
    (meaning :
      ConcreteCMP119ContinuumSemanticMeaning
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S group family encoding) →
  Top.SchwingerBelongsToMeasure S
    (Limit.continuumMeasure family)
    (Schwinger.schwingerFromMeasure
      encoding (Limit.continuumMeasure family))
literalSchwingerBelongsFromConcreteSameMeasure
    {family = family} {encoding = encoding} meaning =
  sameMeasureSchwingerMeansLiteralBelonging meaning
    (Schwinger.schwingerValueIsMeasureExpectation
      encoding (Limit.continuumMeasure family))

round441ConcreteExpectationLimitCompilerLevel : ProofLevel
round441ConcreteExpectationLimitCompilerLevel = machineChecked

round441SameMeasureSchwingerCompilerLevel : ProofLevel
round441SameMeasureSchwingerCompilerLevel = machineChecked

round441ContinuumSemanticInterpretationLevel : ProofLevel
round441ContinuumSemanticInterpretationLevel = conditional

round441IndependentContinuumExistenceWitnessRequired : Bool
round441IndependentContinuumExistenceWitnessRequired = false

round441IndependentSchwingerBelongingWitnessRequired : Bool
round441IndependentSchwingerBelongingWitnessRequired = false
