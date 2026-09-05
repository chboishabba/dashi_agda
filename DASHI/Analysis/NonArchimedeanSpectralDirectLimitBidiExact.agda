module DASHI.Analysis.NonArchimedeanSpectralDirectLimitBidiExact where

------------------------------------------------------------------------
-- AF/direct-limit cross-pollination boundary.
--
-- The source repository has a substantive direct-limit map into dyadic
-- rationals and proves injectivity.  What transfers into DASHI is the proof
-- architecture: stage-local data -> compatible transition maps -> colimit
-- representative -> faithful scalar realization.  This is recorded as a
-- reusable BIDI pattern, not as an identification of its AF algebra with any
-- existing DASHI carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record DirectLimitDiscipline : Set where
  constructor directLimitDiscipline
  field
    stageDataExplicit : Bool
    transitionCompatibilityRequired : Bool
    quotientRepresentativeTracked : Bool
    scalarRealizationFaithfulOnlyWithInjectivity : Bool
    externalAFCarrierEqualsExistingDASHICarrier : Bool

canonicalDirectLimitDiscipline : DirectLimitDiscipline
canonicalDirectLimitDiscipline =
  directLimitDiscipline true true true true false

------------------------------------------------------------------------
-- Reverse direction: asking for a faithful scalar observable of an inductive
-- system compiles back to an injectivity/separation obligation, not merely a
-- stagewise formula.
------------------------------------------------------------------------

data DirectLimitTarget : Set where
  stageFormula : DirectLimitTarget
  wellDefinedColimitMap : DirectLimitTarget
  faithfulScalarRealization : DirectLimitTarget
  carrierIdentification : DirectLimitTarget


data DirectLimitObligation : Set where
  stageComputation : DirectLimitObligation
  transitionCompatibility : DirectLimitObligation
  injectivityOrSeparation : DirectLimitObligation
  explicitCarrierEquivalence : DirectLimitObligation

reverseDirectLimit : DirectLimitTarget → DirectLimitObligation
reverseDirectLimit stageFormula = stageComputation
reverseDirectLimit wellDefinedColimitMap = transitionCompatibility
reverseDirectLimit faithfulScalarRealization = injectivityOrSeparation
reverseDirectLimit carrierIdentification = explicitCarrierEquivalence

faithfulNeedsInjective :
  reverseDirectLimit faithfulScalarRealization ≡ injectivityOrSeparation
faithfulNeedsInjective = refl

identificationNeedsEquivalence :
  reverseDirectLimit carrierIdentification ≡ explicitCarrierEquivalence
identificationNeedsEquivalence = refl
