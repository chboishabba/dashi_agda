{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSelectedCylinderFunctionClosureRound553Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND553:
-- SELECTED-CYLINDER CLOSURE REDUCED TO FINITE-CYLINDER REALIZATION
--
-- Standard projective-measure theorem:
--
--   if F is a bounded/measurable finite-cylinder function, and the projective
--   measure has the selected finite YM marginals, then the finite expectations
--   of F converge to integral F dmu.
--
-- The finite CMP119 family independently converges to limitExpectation(F).
-- Scalar-limit uniqueness therefore gives
--
--   limitExpectation(F) = integral F dmu.
--
-- Hence the only YM-specific A3e payment is that every selected Wilson/cylinder
-- observable consumed downstream is genuinely a finite-cylinder function of
-- the same projective configuration.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsSelectedCylinderRepresentationRound547Exact as R547
import DASHI.Physics.YangMills.YangMillsProjectiveCylinderMeasureRepresentationRound534Exact as R534
import DASHI.Physics.YangMills.YangMillsSelectedRepresentedExpectationConvergenceRound549Exact as R549
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record ProjectiveCylinderFunctionConvergenceAuthority
    (Configuration Event : Set)
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
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    : Set₂ where
  field
    IsFiniteCylinderFunction :
      (Configuration → ℝ) → Set

    finiteCylinderFunctionConvergesToProjectiveIntegral :
      ∀ observable →
      IsFiniteCylinderFunction observable →
      Cylinder.Converges
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        (λ cutoff →
          Limit.finiteExpectation family cutoff observable)
        (R534.integrate
          (R547.extensionAuthority representation)
          (R547.representedMeasure representation)
          observable)

open ProjectiveCylinderFunctionConvergenceAuthority public

record SelectedWilsonCylinderRealization
    (Configuration Event : Set)
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
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family)
    (authority :
      ProjectiveCylinderFunctionConvergenceAuthority
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family representation)
    : Set₂ where
  field
    selectedObservableIsFiniteCylinder :
      ∀ selected →
      IsFiniteCylinderFunction authority
        (R547.asObservable
          (R547.selectedClass representation)
          selected)

open SelectedWilsonCylinderRealization public

selectedLimitIsRepresentedIntegral :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    {representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family}
    (authority :
      ProjectiveCylinderFunctionConvergenceAuthority
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family representation)
    (realization :
      SelectedWilsonCylinderRealization
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family representation authority)
    selected →
  Limit.limitExpectation family
    (R547.asObservable (R547.selectedClass representation) selected)
  ≡
  R534.integrate
    (R547.extensionAuthority representation)
    (R547.representedMeasure representation)
    (R547.asObservable (R547.selectedClass representation) selected)
selectedLimitIsRepresentedIntegral
    {family = family} {limitLaws = limitLaws}
    authority realization selected =
  Cylinder.convergenceUnique
    (RealLimit.canonicalCylinderAlgebra limitLaws)
    (λ cutoff →
      Limit.finiteExpectation family cutoff
        (R547.asObservable
          (R547.selectedClass _)
          selected))
    (Limit.limitExpectation family
      (R547.asObservable (R547.selectedClass _) selected))
    (R534.integrate
      (R547.extensionAuthority _)
      (R547.representedMeasure _)
      (R547.asObservable (R547.selectedClass _) selected))
    (Cylinder.selectedConverges
      (Limit.asCylinderLimitData family)
      (R547.asObservable (R547.selectedClass _) selected))
    (finiteCylinderFunctionConvergesToProjectiveIntegral
      authority
      (R547.asObservable (R547.selectedClass _) selected)
      (selectedObservableIsFiniteCylinder realization selected))

asSelectedObservableRepresentationClosure :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family}
    {representation :
      R547.SelectedCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family}
    (authority :
      ProjectiveCylinderFunctionConvergenceAuthority
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family representation) →
  SelectedWilsonCylinderRealization
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family representation authority →
  R549.SelectedObservableRepresentationClosure
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family representation
asSelectedObservableRepresentationClosure authority realization = record
  { R549.SelectedObservableRepresentationClosure.selectedLimitIsRepresentedIntegral =
      selectedLimitIsRepresentedIntegral authority realization
  }

round553SelectedClosureCompilerLevel : ProofLevel
round553SelectedClosureCompilerLevel = machineChecked

round553ProjectiveCylinderFunctionConvergenceAuthorityLevel : ProofLevel
round553ProjectiveCylinderFunctionConvergenceAuthorityLevel = standardImported

round553GeneralLpCompletionRequired : Bool
round553GeneralLpCompletionRequired = false

round553ProkhorovRequired : Bool
round553ProkhorovRequired = false

-- Genuine YM payment after standard projective measure theory:
-- the exact selected Wilson/cylinder observables are finite-cylinder functions
-- of the same projective configuration.
literalRound553SelectedWilsonFiniteCylinderRealizationLevel : ProofLevel
literalRound553SelectedWilsonFiniteCylinderRealizationLevel = conditional
