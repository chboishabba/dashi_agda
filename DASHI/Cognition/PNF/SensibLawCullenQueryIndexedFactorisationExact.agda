module DASHI.Cognition.PNF.SensibLawCullenQueryIndexedFactorisationExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Cognition.PNF.SensibLawCullenConsumerCollisionMissingCoordinateExact as Cullen

------------------------------------------------------------------------
-- CULLEN x INTERSECTIONAL FACTORISATION
--
-- No new adequacy calculus is introduced here.  The legal regression is put
-- directly on the repository's intersectional FactorsThrough carrier via the
-- query-indexed adequacy owner.
--
-- One coarse source observation is asked two different questions:
--
--   1. is the legacy bundled premise paid?
--   2. may the legacy rule be reused unchanged after the source split?
--
-- The first does not factor through police-function context; the second does.
-- Hence adequacy is consumer/query indexed, exactly as in the existing
-- Indigenous/intersectional machinery.
------------------------------------------------------------------------

data CullenQuery : Set where
  legacyBundledPremisePayment : CullenQuery
  legacyRuleReuseAudit : CullenQuery

data CullenAnswer : Set where
  bundledPremiseUnpaid : CullenAnswer
  bundledPremisePaid : CullenAnswer
  reconstructSourceCorrectRoute : CullenAnswer

answerCullenQuery : CullenQuery → Cullen.CullenFineWorld → CullenAnswer
answerCullenQuery legacyBundledPremisePayment
  Cullen.policeFunctionWithoutInvokedStatutoryPower = bundledPremiseUnpaid
answerCullenQuery legacyBundledPremisePayment
  Cullen.policeFunctionWithInvokedStatutoryPower = bundledPremisePaid
answerCullenQuery legacyRuleReuseAudit world = reconstructSourceCorrectRoute

cullenQuerySemantics :
  Query.QuerySemantics Cullen.CullenFineWorld CullenQuery CullenAnswer
cullenQuerySemantics = Query.querySemantics answerCullenQuery

------------------------------------------------------------------------
-- Literal FactorsThrough result for the reuse-audit consumer.
------------------------------------------------------------------------

reuseAuditFactorsThroughPoliceFunctionContext :
  Query.AdequateFor
    Cullen.observePoliceFunctionContext
    cullenQuerySemantics
    legacyRuleReuseAudit
reuseAuditFactorsThroughPoliceFunctionContext =
  Query.factorsForQuery
    (λ observation → reconstructSourceCorrectRoute)
    (λ state → refl)

------------------------------------------------------------------------
-- Literal non-factorability for the legacy bundled-premise consumer.
------------------------------------------------------------------------

legacyPaymentFactorisationDefect :
  Query.QueryAdequacyDefect
    Cullen.observePoliceFunctionContext
    cullenQuerySemantics
    legacyBundledPremisePayment
legacyPaymentFactorisationDefect =
  Query.queryAdequacyDefect
    Cullen.policeFunctionWithoutInvokedStatutoryPower
    Cullen.policeFunctionWithInvokedStatutoryPower
    refl
    (λ ())

legacyPaymentDoesNotFactorThroughPoliceFunctionContext :
  NonFactor.FactorsThrough
    Cullen.observePoliceFunctionContext
    (Query.answer cullenQuerySemantics legacyBundledPremisePayment) → ⊥
legacyPaymentDoesNotFactorThroughPoliceFunctionContext =
  Query.queryAdequacyDefectBlocksFactorisation legacyPaymentFactorisationDefect

------------------------------------------------------------------------
-- Recharting the same coarse observer cannot repair the erased distinction.
-- This is the original intersectional no-relabel theorem, now instantiated on
-- the legal source carrier.
------------------------------------------------------------------------

relabelledPoliceFunctionStillCannotPayLegacyPremise :
  ∀ {Recharted : Set} →
  (rechart : Cullen.PoliceFunctionObservation → Recharted) →
  NonFactor.FactorsThrough
    (λ state → rechart (Cullen.observePoliceFunctionContext state))
    (Query.answer cullenQuerySemantics legacyBundledPremisePayment) → ⊥
relabelledPoliceFunctionStillCannotPayLegacyPremise rechart =
  NonFactor.rechartingCannotRecoverErasedPhenomenon
    rechart legacyPaymentFactorisationDefect

------------------------------------------------------------------------
-- Boundary: this module says which source representation carries which
-- consumer.  It does not decide judicial authority or invent a duty element.
------------------------------------------------------------------------

data QueryAdequacyCreatesLegalAuthority : Set where

data NonFactorabilityIdentifiesUniqueLegalResidual : Set where

factorisationIsNotAuthority : QueryAdequacyCreatesLegalAuthority → ⊥
factorisationIsNotAuthority ()

collisionDoesNotNameUniqueResidual :
  NonFactorabilityIdentifiesUniqueLegalResidual → ⊥
collisionDoesNotNameUniqueResidual ()
