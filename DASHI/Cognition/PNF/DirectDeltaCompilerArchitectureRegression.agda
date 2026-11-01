module DASHI.Cognition.PNF.DirectDeltaCompilerArchitectureRegression where

open import Agda.Builtin.Equality using (refl)

open import DASHI.Cognition.PNF.DirectDeltaCompilerArchitectureExact

------------------------------------------------------------------------
-- Concrete normalization witnesses for the constitutional counters.
------------------------------------------------------------------------

zeroHotPathCrossings : DirectDeltaPhysicalConstitution
zeroHotPathCrossings =
  directDeltaPhysicalConstitution
    0
    0
    0
    0
    refl
    refl
    refl
    refl

singlePublicationBoundary : GenerationPublicationBoundary
singlePublicationBoundary =
  generationPublicationBoundary
    0
    1
    refl
    refl

closedFixedPoint : DirectDeltaFixedPointReceipt
closedFixedPoint = directDeltaFixedPointReceipt 0 refl

rollbackIndependentDiagnosticsRemainNonAuthoritative : DiagnosticPlaneBoundary
rollbackIndependentDiagnosticsRemainNonAuthoritative =
  diagnosticPlaneBoundary 7 0 refl

data SampleObservation : Set where
  sameAuthority : SampleObservation

directReferenceAgree : DirectReferenceParity SampleObservation
directReferenceAgree =
  directReferenceParity sameAuthority sameAuthority refl
