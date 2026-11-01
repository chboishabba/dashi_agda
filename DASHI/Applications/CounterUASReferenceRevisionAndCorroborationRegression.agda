module DASHI.Applications.CounterUASReferenceRevisionAndCorroborationRegression where

open import DASHI.Core.Prelude

import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Reasoning.PNFRevisionSelectiveReopeningExact as Reopening
import DASHI.Applications.CounterUASReferenceRevisionAndCorroborationExact as CounterUAS
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

record CounterUASReferenceRevisionAndCorroborationRegression : Set₁ where
  constructor counterUASReferenceRevisionAndCorroborationRegression
  field
    reusesCanonicalAppendOnlyRevision :
      CounterUAS.existingAppendOnlyRevisionBoundary ≡ Revision.canonicalAppendOnlyEvidenceRevisionBoundary
    reusesCanonicalSelectiveReopening :
      CounterUAS.existingSelectiveReopeningBoundary ≡ Reopening.canonicalPNFRevisionReopeningBoundary
    promotedReferenceCanLaterBeHeldWithoutHistoryDeletion :
      CounterUAS.promotedThenDefeatedRevisionIsCanonical ≡ true
    modalityCountHasIndependentCorroborationDefect :
      Adequacy.QueryAdequacyDefect
        CounterUAS.modalityCountProjection
        CounterUAS.corroborationSemantics
        CounterUAS.independentCorroborationQuery
    sharedUpstreamDoesNotPayIndependentCorroboration :
      CounterUAS.sharedUpstreamCorroborationPaid ≡ false
    independentLineagesPayIndependentCorroboration :
      CounterUAS.independentLineagesCorroborationPaid ≡ true
    revisionDoesNotCreateOperationalAuthority :
      CounterUAS.referenceRevisionCreatesOperationalAuthority ≡ false

canonicalCounterUASReferenceRevisionAndCorroborationRegression :
  CounterUASReferenceRevisionAndCorroborationRegression
canonicalCounterUASReferenceRevisionAndCorroborationRegression =
  counterUASReferenceRevisionAndCorroborationRegression
    refl
    refl
    refl
    CounterUAS.modalityCountCorroborationAdequacyDefect
    refl
    refl
    refl
