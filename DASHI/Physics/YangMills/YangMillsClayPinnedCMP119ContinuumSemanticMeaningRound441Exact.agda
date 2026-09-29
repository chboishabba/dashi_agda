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

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
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
import DASHI.Physics.YangMills.YangMillsClayNormalizedExpectationRepresentationFirewallRound448Exact as R448
import DASHI.Physics.YangMills.YangMillsRepresentedContinuumCarrierRound450Exact as R450

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
    -- The selected limit expectation is only an expectation functional.
    -- Crossing to the literal Clay continuum predicate requires an explicit
    -- countably-additive representation object; normalized quotient convergence
    -- alone is not licensed to perform this promotion.
    continuumRepresentation :
      R448.ContinuumMeasureRepresentationAuthority
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S group family

    -- Schwinger is constructed from the represented carrier itself.  The
    -- same-expectation equation is definitional in R450, so no equality premise
    -- is accepted here.
    representedSchwingerMeansLiteralBelonging :
      Top.SchwingerBelongsToMeasure S
        (R450.representedContinuumMeasure
          (R448.representedCarrier continuumRepresentation))
        (R450.representedSchwinger encoding
          (R448.representedCarrier continuumRepresentation))

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
    (R450.representedContinuumMeasure
      (R448.representedCarrier (continuumRepresentation meaning)))
literalContinuumLimitFromConcreteExpectationLimit meaning =
  R448.literalContinuumLimitFromRepresentation
    (continuumRepresentation meaning)

literalContinuumLimitFromConcreteRepresentation :
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
    (R450.representedContinuumMeasure
      (R448.representedCarrier (continuumRepresentation meaning)))
literalContinuumLimitFromConcreteRepresentation meaning =
  R448.literalContinuumLimitFromRepresentation
    (continuumRepresentation meaning)

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
    (R450.representedContinuumMeasure
      (R448.representedCarrier (continuumRepresentation meaning)))
    (R450.representedSchwinger encoding
      (R448.representedCarrier (continuumRepresentation meaning)))
literalSchwingerBelongsFromConcreteSameMeasure meaning =
  representedSchwingerMeansLiteralBelonging meaning

round441ConcreteExpectationLimitCompilerLevel : ProofLevel
round441ConcreteExpectationLimitCompilerLevel = machineChecked

round441SameMeasureSchwingerCompilerLevel : ProofLevel
round441SameMeasureSchwingerCompilerLevel = machineChecked

round441SchwingerExpectationEqualityRequiredAsPremise : Bool
round441SchwingerExpectationEqualityRequiredAsPremise = false

round441ContinuumSemanticInterpretationLevel : ProofLevel
round441ContinuumSemanticInterpretationLevel = conditional

round441CountablyAdditiveRepresentationRequired : Bool
round441CountablyAdditiveRepresentationRequired = true

round441IndependentContinuumExistenceWitnessRequired : Bool
round441IndependentContinuumExistenceWitnessRequired = false

round441IndependentSchwingerBelongingWitnessRequired : Bool
round441IndependentSchwingerBelongingWitnessRequired = false
