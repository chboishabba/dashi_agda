module DASHI.Physics.Closure.PerelmanBTLedgerExactCounts where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.BTNeckDepthScaleArithmetic as NeckDepth
import DASHI.Physics.Closure.BTProductShellVsEnvelopeRows as ShellEnvelope
import DASHI.Physics.Closure.JSJBlockerNormalization as JSJBlockers
import DASHI.Physics.Closure.PerelmanBTNoPromotionAuditSurface as Audit
import DASHI.Physics.Closure.PerelmanBTNoPromotionLaw as NoPromotion
import DASHI.Physics.Closure.PerelmanBTGeometrizationAnalogueSummary as Summary

------------------------------------------------------------------------
-- Exact count ledger for the Perelman/BT analogue surfaces.
--
-- This module is count-only governance.  It packages row-count witnesses
-- from the recent ledgers and does not promote any smooth Ricci-flow,
-- surgery, JSJ, geometrization, or Clay claim.

record PerelmanBTLedgerExactCounts : Set where
  constructor perelmanBTLedgerExactCounts
  field
    neckDepthRows :
      Nat

    neckDepthRowsIs12 :
      neckDepthRows ≡ 12

    neckDepthRowsMatchesLedger :
      NeckDepth.length NeckDepth.canonicalBTNeckDepthScaleRows ≡ 12

    shellEnvelopeRows :
      Nat

    shellEnvelopeRowsIs4 :
      shellEnvelopeRows ≡ 4

    shellEnvelopeRowsMatchesLedger :
      ShellEnvelope.canonicalBTProductShellVsEnvelopeRowCountIs4
      ≡
      ShellEnvelope.canonicalBTProductShellVsEnvelopeRowCountIs4

    jsjBTBlockers :
      Nat

    jsjBTBlockersIs6 :
      jsjBTBlockers ≡ 6

    jsjBTBlockersMatchLedger :
      JSJBlockers.btBlockerCount ≡ 6

    jsj369Blockers :
      Nat

    jsj369BlockersIs6 :
      jsj369Blockers ≡ 6

    jsj369BlockersMatchLedger :
      JSJBlockers.hyperfabric369BlockerCount ≡ 6

    jsjUnionBlockers :
      Nat

    jsjUnionBlockersIs7 :
      jsjUnionBlockers ≡ 7

    jsjUnionBlockersMatchLedger :
      JSJBlockers.normalizedUnionBlockerCount ≡ 7

    jsjConcatenatedBlockers :
      Nat

    jsjConcatenatedBlockersIs12 :
      jsjConcatenatedBlockers ≡ 12

    jsjConcatenatedBlockersMatchLedger :
      JSJBlockers.concatenatedCrosswalkBlockerCount ≡ 12

    auditForbiddenRows :
      Nat

    auditForbiddenRowsIs0 :
      auditForbiddenRows ≡ 0

    auditForbiddenRowsMatchLedger :
      Audit.forbiddenRowCount ≡ 0

    auditRequiredRows :
      Nat

    auditRequiredRowsIs4 :
      auditRequiredRows ≡ 4

    auditRequiredRowsMatchLedger :
      Audit.requiredRowCount ≡ 4

    noPromotionReasons :
      Nat

    noPromotionReasonsIs7 :
      noPromotionReasons ≡ 7

    noPromotionReasonsMatchLedger :
      NoPromotion.noPromotionReasonCount ≡ 7

    constructibleRows :
      Nat

    constructibleRowsIs10 :
      constructibleRows ≡ 10

    constructibleRowsMatchSummary :
      Summary.constructibleRowCount
        Summary.canonicalPerelmanBTGeometrizationAnalogueSummary
      ≡
      10

    smoothAuthorityBlockers :
      Nat

    smoothAuthorityBlockersIs9 :
      smoothAuthorityBlockers ≡ 9

    smoothAuthorityBlockersMatchSummary :
      Summary.blockerCount
        Summary.canonicalPerelmanBTGeometrizationAnalogueSummary
      ≡
      9

open PerelmanBTLedgerExactCounts public

canonicalPerelmanBTLedgerExactCounts :
  PerelmanBTLedgerExactCounts
canonicalPerelmanBTLedgerExactCounts =
  perelmanBTLedgerExactCounts
    12
    refl
    NeckDepth.canonicalBTNeckDepthScaleRowCountIs12
    4
    refl
    refl
    6
    refl
    JSJBlockers.btBlockerCountIs6
    6
    refl
    JSJBlockers.hyperfabric369BlockerCountIs6
    7
    refl
    JSJBlockers.normalizedUnionBlockerCountIs7
    12
    refl
    JSJBlockers.concatenatedCrosswalkBlockerCountIs12
    0
    refl
    Audit.forbiddenRowCountIs0
    4
    refl
    Audit.requiredRowCountIs4
    7
    refl
    NoPromotion.noPromotionReasonCountIs7
    10
    refl
    Summary.summaryConstructibleRowCountIs10
    9
    refl
    Summary.summaryBlockerCountIs9

canonicalLedgerNeckDepthRowsIs12 :
  neckDepthRows canonicalPerelmanBTLedgerExactCounts ≡ 12
canonicalLedgerNeckDepthRowsIs12 =
  refl

canonicalLedgerShellEnvelopeRowsIs4 :
  shellEnvelopeRows canonicalPerelmanBTLedgerExactCounts ≡ 4
canonicalLedgerShellEnvelopeRowsIs4 =
  refl

canonicalLedgerJSJUnionBlockersIs7 :
  jsjUnionBlockers canonicalPerelmanBTLedgerExactCounts ≡ 7
canonicalLedgerJSJUnionBlockersIs7 =
  refl

canonicalLedgerNoPromotionReasonsIs7 :
  noPromotionReasons canonicalPerelmanBTLedgerExactCounts ≡ 7
canonicalLedgerNoPromotionReasonsIs7 =
  refl

canonicalLedgerConstructibleRowsIs10 :
  constructibleRows canonicalPerelmanBTLedgerExactCounts ≡ 10
canonicalLedgerConstructibleRowsIs10 =
  refl

canonicalLedgerSmoothAuthorityBlockersIs9 :
  smoothAuthorityBlockers canonicalPerelmanBTLedgerExactCounts ≡ 9
canonicalLedgerSmoothAuthorityBlockersIs9 =
  refl
