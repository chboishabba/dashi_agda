module DASHI.Law.QueryWorldCoverageInvalidationRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.QueryWorldCoverageInvalidationExact as Coverage

boundary : Coverage.QueryWorldCoverageInvalidationBoundary
boundary = Coverage.canonicalQueryWorldCoverageInvalidationBoundary

revisionInvalidatesSource :
  Coverage.relevantRevisionInvalidatesSourcePayment boundary ≡ true
revisionInvalidatesSource =
  Coverage.relevantRevisionInvalidatesSourcePaymentIsTrue boundary

revisionInvalidatesSpan :
  Coverage.relevantRevisionInvalidatesSpanPayment boundary ≡ true
revisionInvalidatesSpan =
  Coverage.relevantRevisionInvalidatesSpanPaymentIsTrue boundary

revisionInvalidatesProvenance :
  Coverage.relevantRevisionInvalidatesProvenancePayment boundary ≡ true
revisionInvalidatesProvenance =
  Coverage.relevantRevisionInvalidatesProvenancePaymentIsTrue boundary

timeInvalidatesTemporal :
  Coverage.requiredTimeChangeInvalidatesTemporalPayment boundary ≡ true
timeInvalidatesTemporal =
  Coverage.requiredTimeChangeInvalidatesTemporalPaymentIsTrue boundary

jurisdictionInvalidatesJurisdiction :
  Coverage.requiredJurisdictionChangeInvalidatesJurisdictionPayment boundary ≡ true
jurisdictionInvalidatesJurisdiction =
  Coverage.requiredJurisdictionChangeInvalidatesJurisdictionPaymentIsTrue boundary

irrelevantPreserves :
  Coverage.irrelevantWorldChangeMayPreserveUnaffectedPayment boundary ≡ true
irrelevantPreserves =
  Coverage.irrelevantWorldChangeMayPreserveUnaffectedPaymentIsTrue boundary
