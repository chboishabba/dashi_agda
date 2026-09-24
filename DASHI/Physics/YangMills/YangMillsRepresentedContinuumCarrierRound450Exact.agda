{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsRepresentedContinuumCarrierRound450Exact where

------------------------------------------------------------------------
-- ROUND450 / REPRESENTATION-FIRST CONTINUUM CARRIER
--
-- GRQFT specialization invariant:
--
--   if an equality only expresses how the object was chosen, put that choice
--   in the constructor and make the equality definitional.
--
-- Here the represented continuum measure is chosen first.  The physical
-- continuum expectation carrier is then DEFINED by integration against that
-- exact represented measure, and the Schwinger family is defined from the same
-- carrier.  Hence
--
--   expectation representedContinuumMeasure F = integrate mu F
--
-- and the Schwinger-to-expectation equation are both refl.
--
-- The genuine mathematical payment remains:
--
--   the selected finite expectation limit is represented by this integral,
--   and the represented measure is countably additive.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record RepresentedContinuumCarrier
    (Configuration Position : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    (encoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position)
    : Set₂ where
  field
    MeasureObject : Set
    IsCountablyAdditive : MeasureObject → Set

    representedMeasure : MeasureObject
    integrate :
      MeasureObject → (Configuration → ℝ) → ℝ

    representedMeasureCountablyAdditive :
      IsCountablyAdditive representedMeasure

    -- Genuine representation theorem: the already-selected limit functional
    -- is integration against the chosen countably-additive measure.
    limitExpectationIsRepresentedIntegral :
      ∀ observable →
      Limit.limitExpectation family observable
      ≡ integrate representedMeasure observable

open RepresentedContinuumCarrier public

representedContinuumMeasure :
  ∀ {Configuration Position sequenceLimit limitLaws quotient division
      family encoding} →
  RepresentedContinuumCarrier
    Configuration Position
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family encoding →
  Physical.PhysicalContinuumYMMeasure (Configuration → ℝ) ℝ
representedContinuumMeasure carrier =
  Physical.physicalContinuumMeasure
    (integrate carrier (representedMeasure carrier))

representedContinuumExpectationIsIntegral :
  ∀ {Configuration Position sequenceLimit limitLaws quotient division
      family encoding}
    (carrier :
      RepresentedContinuumCarrier
        Configuration Position
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family encoding)
    observable →
  Physical.expectation (representedContinuumMeasure carrier) observable
  ≡ integrate carrier (representedMeasure carrier) observable
representedContinuumExpectationIsIntegral carrier observable = refl

representedSchwinger :
  ∀ {Configuration Position sequenceLimit limitLaws quotient division
      family encoding} →
  (carrier :
    RepresentedContinuumCarrier
      Configuration Position
      {sequenceLimit = sequenceLimit}
      limitLaws quotient division family encoding) →
  Physical.PhysicalSchwingerFamily (Configuration → ℝ) Position ℝ
representedSchwinger {encoding = encoding} carrier =
  Schwinger.schwingerFromMeasure
    encoding
    (representedContinuumMeasure carrier)

representedSchwingerIsSameExpectation :
  ∀ {Configuration Position sequenceLimit limitLaws quotient division
      family encoding}
    (carrier :
      RepresentedContinuumCarrier
        Configuration Position
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family encoding)
    observable left right →
  Physical.schwinger
    (representedSchwinger carrier)
    observable left right
  ≡
  Physical.expectation
    (representedContinuumMeasure carrier)
    (Schwinger.twoPointCylinder encoding observable left right)
representedSchwingerIsSameExpectation carrier observable left right = refl

-- The old limit-functional carrier and the representation-first carrier agree
-- extensionally on every selected observable as a CONSEQUENCE of the one real
-- representation theorem.  This equality is not an input to the constructor.
oldLimitExpectationAgreesWithRepresentedCarrier :
  ∀ {Configuration Position sequenceLimit limitLaws quotient division
      family encoding}
    (carrier :
      RepresentedContinuumCarrier
        Configuration Position
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family encoding)
    observable →
  Physical.expectation
    (Limit.continuumMeasure family)
    observable
  ≡
  Physical.expectation
    (representedContinuumMeasure carrier)
    observable
oldLimitExpectationAgreesWithRepresentedCarrier carrier observable =
  limitExpectationIsRepresentedIntegral carrier observable

round450RepresentedCarrierCompilerLevel : ProofLevel
round450RepresentedCarrierCompilerLevel = machineChecked

round450ExpectationByIntegrationDefinitionalLevel : ProofLevel
round450ExpectationByIntegrationDefinitionalLevel = machineChecked

round450SchwingerSameCarrierDefinitionalLevel : ProofLevel
round450SchwingerSameCarrierDefinitionalLevel = machineChecked

round450CountablyAdditiveRepresentationLevel : ProofLevel
round450CountablyAdditiveRepresentationLevel = conditional
