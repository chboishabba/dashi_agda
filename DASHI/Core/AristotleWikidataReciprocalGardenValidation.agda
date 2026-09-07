module DASHI.Core.AristotleWikidataReciprocalGardenValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Interop.AristotlePropertyFamilyQueryFibreBidiExact
import DASHI.Interop.AristotleRankVisibilityCommutingProvenanceBidiExact
import DASHI.Interop.AristotleSnakAbsenceInformationLossBidiExact
import DASHI.Interop.AristotleReliableSourceConsumerAdequacyBidiExact
import DASHI.Interop.AristotlePrunedGraphPromotionTransportBidiExact
import DASHI.Interop.AristotleSchemaCoverageProfileBidiExact
import DASHI.Interop.AristotleCoverageResidualSalienceBidiExact
import DASHI.Interop.AristotleWorklistDeliberativeMovesBidiExact
import DASHI.Interop.AristotleContentIdentityRevisionSyncBidiExact
import DASHI.Interop.AristotleWikibaseZelphBraidedPromotionBidiExact
import DASHI.Interop.SensibLawNatCoverageAcquisitionDemandExact as NatDemand

natDemandIsExactSubjectPropertyIndexed :
  NatDemand.NatCoverageAcquisitionBoundary.demandIndexedByExactSubjectPropertyResidual
    NatDemand.canonicalNatCoverageAcquisitionBoundary ≡ true
natDemandIsExactSubjectPropertyIndexed = refl

natTransportDoesNotPayCoverage :
  NatDemand.NatCoverageAcquisitionBoundary.transportEqualsCoveragePayment
    NatDemand.canonicalNatCoverageAcquisitionBoundary ≡ false
natTransportDoesNotPayCoverage = refl

natOtherPropertyDoesNotPayTargetResidual :
  NatDemand.NatCoverageAcquisitionBoundary.anotherPropertyCanPayTargetPropertyResidual
    NatDemand.canonicalNatCoverageAcquisitionBoundary ≡ false
natOtherPropertyDoesNotPayTargetResidual = refl

natDemandDoesNotCreateMigrationAuthority :
  NatDemand.NatCoverageAcquisitionBoundary.demandCreatesMigrationAuthority
    NatDemand.canonicalNatCoverageAcquisitionBoundary ≡ false
natDemandDoesNotCreateMigrationAuthority = refl

validationStatement : String
validationStatement =
  "Focused validation root for the Aristotle/Wikidata reciprocal garden: Q/P query fibres, rank/visibility commuting provenance, snak information loss, reliable-source adequacy, pruned-graph promotion transport, schema-scoped coverage, coverage residual salience, deliberative worklists, content/revision sync, braided Wikibase-Zelph-review-policy transport, and exact Q/P residual-bound Nat acquisition demands."
