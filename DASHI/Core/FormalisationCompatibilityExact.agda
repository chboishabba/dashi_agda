module DASHI.Core.FormalisationCompatibilityExact where

------------------------------------------------------------------------
-- FORMALISATION COMPATIBILITY / METHODOLOGICAL TENSION
--
-- SOURCE CALIBRATION
-- Audre Lorde, "The Master's Tools Will Never Dismantle the Master's House",
-- remarks delivered 1979; collected in Sister Outsider, Crossing Press, 1984.
-- ISBN 9781580911863 (2007 edition). No DOI asserted.
--
-- Lorde motivates a methodological question about using dominant analytical
-- apparatuses for emancipatory projects. DASHI does not pretend this question
-- can be discharged by a Boolean proof. Tension/contestation are first-class
-- statuses and are not build failures.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.InterpretiveFormalisationCoreExact as IF

FormalisationCompatibility : Set
FormalisationCompatibility = IF.FormalisationCompatibility

compatibleBySource : FormalisationCompatibility
compatibleBySource = IF.compatibleBySource

boundedInterpretiveUse : FormalisationCompatibility
boundedInterpretiveUse = IF.boundedInterpretiveUse

methodologicalTension : FormalisationCompatibility
methodologicalTension = IF.methodologicalTension

contested : FormalisationCompatibility
contested = IF.contested

unknown : FormalisationCompatibility
unknown = IF.unknown

record CompatibilityAssessment : Set where
  constructor compatibility-assessment
  field
    status : FormalisationCompatibility
    formalConstructionMayProceed : Bool
    semanticExhaustivenessClaimed : Bool

canonicalMethodologicalTension : CompatibilityAssessment
canonicalMethodologicalTension =
  compatibility-assessment methodologicalTension true false

record FormalisationCompatibilityBoundary : Set where
  constructor formalisation-compatibility-boundary
  field
    explicitTensionIsFormalDefect : Bool
    explicitTensionIsFormalDefectIsFalse : explicitTensionIsFormalDefect ≡ false
    formalSuccessResolvesMethodologicalContest : Bool
    formalSuccessResolvesMethodologicalContestIsFalse :
      formalSuccessResolvesMethodologicalContest ≡ false
    contestedStatusMeansNoFormalWorkPossible : Bool
    contestedStatusMeansNoFormalWorkPossibleIsFalse :
      contestedStatusMeansNoFormalWorkPossible ≡ false

canonicalFormalisationCompatibilityBoundary : FormalisationCompatibilityBoundary
canonicalFormalisationCompatibilityBoundary =
  formalisation-compatibility-boundary false refl false refl false refl
