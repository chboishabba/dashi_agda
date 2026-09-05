module DASHI.Analysis.SumIntegralDefectExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC SUM-MINUS-INTEGRAL DEFECT
--
-- Application-neutral carrier for comparisons between a discrete spectral
-- sum and a matched continuum reference.  The theorem shape may be reused by
-- Casimir, Poisson, Abel-Plana, Euler-Maclaurin, or other producers, but no
-- application-specific evaluation is encoded here.
------------------------------------------------------------------------

record SumIntegralDefect : Set₁ where
  field
    Parameter : Set
    Function : Set
    Value : Set

    discrete : Parameter → Function → Value
    continuum : Parameter → Function → Value
    subtract : Value → Value → Value
    defect : Parameter → Function → Value

    defectLaw : (p : Parameter) → (f : Function) →
      defect p f ≡ subtract (discrete p f) (continuum p f)

    reading : String

open SumIntegralDefect public

------------------------------------------------------------------------
-- BIDI producer/consumer interface.
------------------------------------------------------------------------

record DefectEvaluationMethod (D : SumIntegralDefect) : Set₁ where
  field
    MethodState : Set
    methodState : MethodState
    Evaluated : Parameter D → Function D → Value D → Set
    evaluate : (p : Parameter D) → (f : Function D) →
      Evaluated p f (defect D p f)
    methodReading : String

open DefectEvaluationMethod public

record DefectConsumerObligations (D : SumIntegralDefect) : Set₁ where
  field
    discreteObjectIdentified : Set
    continuumReferenceIdentified : Set
    subtractionSameCarrier : Set
    evaluationMethodApplicable : Set

open DefectConsumerObligations public

------------------------------------------------------------------------
-- Independent methods may target the same defect.  Equality of method names
-- or output dimensions is never sufficient; agreement must be proved on the
-- same defect object.
------------------------------------------------------------------------

record SameDefectMethodAgreement
    (D : SumIntegralDefect)
    (left right : DefectEvaluationMethod D) : Set₁ where
  field
    agreement : Set
    agreementReceipt : agreement

open SameDefectMethodAgreement public
