{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsRepresentedContinuumTransportRound454Exact where

------------------------------------------------------------------------
-- ROUND454 / TRANSPORT UNAFFECTED EXPECTATION-LEVEL RECEIPTS
--
-- The representation-first carrier changes HOW the continuum expectation is
-- constructed, not the selected scalar functional it represents.
--
-- Avoid record equality between the legacy expectation-functional carrier and
-- the represented carrier.  Instead, transport only predicates that declare
-- themselves extensional under pointwise equality of expectation functionals.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsRepresentedContinuumCarrierRound450Exact as R450
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

ExpectationFunctional : Set → Set
ExpectationFunctional Configuration =
  (Configuration → ℝ) → ℝ

record ExtensionalExpectationPredicate
    {Configuration : Set}
    (Predicate : ExpectationFunctional Configuration → Set)
    : Set₁ where
  field
    respectsPointwiseEquality :
      ∀ left right →
      (∀ observable → left observable ≡ right observable) →
      Predicate left →
      Predicate right

open ExtensionalExpectationPredicate public

representedExpectation :
  ∀ {Configuration Position sequenceLimit limitLaws quotient division family} →
  R450.RepresentedContinuumCarrier
    Configuration Position
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family →
  ExpectationFunctional Configuration
representedExpectation carrier =
  Physical.expectation (R450.representedContinuumMeasure carrier)

limitExpectationAgreesPointwiseWithRepresented :
  ∀ {Configuration Position sequenceLimit limitLaws quotient division family}
    (carrier :
      R450.RepresentedContinuumCarrier
        Configuration Position
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    observable →
  Limit.limitExpectation family observable
  ≡ representedExpectation carrier observable
limitExpectationAgreesPointwiseWithRepresented carrier observable =
  R450.oldLimitExpectationAgreesWithRepresentedCarrier carrier observable

transportExpectationPredicate :
  ∀ {Configuration Position sequenceLimit limitLaws quotient division family}
    {Predicate : ExpectationFunctional Configuration → Set}
    (transport : ExtensionalExpectationPredicate Predicate)
    (carrier :
      R450.RepresentedContinuumCarrier
        Configuration Position
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family) →
  Predicate (Limit.limitExpectation family) →
  Predicate (representedExpectation carrier)
transportExpectationPredicate transport carrier oldReceipt =
  respectsPointwiseEquality transport
    (Limit.limitExpectation family)
    (representedExpectation carrier)
    (limitExpectationAgreesPointwiseWithRepresented carrier)
    oldReceipt

round454PointwiseExpectationTransportCompilerLevel : ProofLevel
round454PointwiseExpectationTransportCompilerLevel = machineChecked

round454WholeMeasureRecordEqualityRequired : Bool
round454WholeMeasureRecordEqualityRequired = false

round454UnaffectedReceiptTransportUsesOnlyPointwiseExpectationEquality : Bool
round454UnaffectedReceiptTransportUsesOnlyPointwiseExpectationEquality = true
