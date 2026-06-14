module DASHI.Physics.Closure.PerelmanBTRoundFullImportSmoke where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)

import DASHI.Physics.Closure.BTGaussianDiagonalInputRows as GaussianRows
import DASHI.Physics.Closure.BTBoundaryCrossSectionRows as BoundaryRows
import DASHI.Physics.Closure.BTNeckDepthScaleArithmetic as NeckDepth
import DASHI.Physics.Closure.BTNeckSurgeryObligationComposite as NeckSurgery
import DASHI.Physics.Closure.BTProductShellVsEnvelopeRows as ShellEnvelope
import DASHI.Physics.Closure.JSJBlockerNormalization as JSJNorm
import DASHI.Physics.Closure.PerelmanBTAnalogueDashboard as Dashboard
import DASHI.Physics.Closure.PerelmanBTGeometrizationAnalogueIndex as Index
import DASHI.Physics.Closure.PerelmanBTGeometrizationAnalogueSummary as Summary
import DASHI.Physics.Closure.PerelmanBTLedgerExactCounts as Counts
import DASHI.Physics.Closure.PerelmanBTNoPromotionAuditSurface as Audit
import DASHI.Physics.Closure.PerelmanBTNoPromotionLaw as NoPromotion
import DASHI.Physics.Closure.SurgeryObligationBlockerNormalization as SurgeryBlockers
import DASHI.Physics.Probes.PerelmanBTAnalogueImportProbe as ImportProbe

------------------------------------------------------------------------
-- Full recent-round import smoke.
--
-- This module is deliberately not wired into Everything.agda.  It imports
-- the recent Perelman/BT closure surfaces plus the standalone import probe
-- and exposes only concrete count/false/self-equality witnesses.

canonicalIndex :
  Index.PerelmanBTGeometrizationAnalogueIndex
canonicalIndex =
  Index.canonicalPerelmanBTGeometrizationAnalogueIndex

canonicalSummary :
  Summary.PerelmanBTGeometrizationAnalogueSummary
canonicalSummary =
  Summary.canonicalPerelmanBTGeometrizationAnalogueSummary

canonicalNoPromotionLaw :
  NoPromotion.PerelmanBTNoPromotionLaw
canonicalNoPromotionLaw =
  NoPromotion.canonicalPerelmanBTNoPromotionLaw

canonicalAuditSurface :
  Audit.PerelmanBTNoPromotionAuditSurface
canonicalAuditSurface =
  Audit.canonicalPerelmanBTNoPromotionAuditSurface

canonicalLedgerExactCounts :
  Counts.PerelmanBTLedgerExactCounts
canonicalLedgerExactCounts =
  Counts.canonicalPerelmanBTLedgerExactCounts

canonicalJSJBlockerLedger :
  JSJNorm.JSJBlockerNormalizationLedger
canonicalJSJBlockerLedger =
  JSJNorm.canonicalJSJBlockerNormalizationLedger

canonicalDashboard :
  Dashboard.PerelmanBTAnalogueDashboard
canonicalDashboard =
  Dashboard.canonicalPerelmanBTAnalogueDashboard

canonicalImportProbe :
  ImportProbe.PerelmanBTAnalogueImportProbe
canonicalImportProbe =
  ImportProbe.canonicalPerelmanBTAnalogueImportProbe

------------------------------------------------------------------------
-- Concrete count witnesses from the imported surfaces.

indexConstructibleCountIs10 :
  Index.constructibleRowCountField canonicalIndex ≡ 10
indexConstructibleCountIs10 =
  Index.constructibleRowCountFieldIs10 canonicalIndex

indexBlockerCountIs9 :
  Index.smoothAuthorityBlockerCountField canonicalIndex ≡ 9
indexBlockerCountIs9 =
  Index.smoothAuthorityBlockerCountFieldIs9 canonicalIndex

summaryConstructibleCountIs10 :
  Summary.constructibleRowCount canonicalSummary ≡ 10
summaryConstructibleCountIs10 =
  Summary.summaryConstructibleRowCountIs10

summaryBlockerCountIs9 :
  Summary.blockerCount canonicalSummary ≡ 9
summaryBlockerCountIs9 =
  Summary.summaryBlockerCountIs9

noPromotionReasonCountIs7 :
  NoPromotion.noPromotionReasonCount ≡ 7
noPromotionReasonCountIs7 =
  NoPromotion.noPromotionReasonCountIs7

auditForbiddenRowCountIs0 :
  Audit.forbiddenHitRowCount canonicalAuditSurface ≡ 0
auditForbiddenRowCountIs0 =
  Audit.forbiddenHitRowCountIs0 canonicalAuditSurface

auditRequiredEvidenceRowCountIs4 :
  Audit.requiredEvidenceRowCount canonicalAuditSurface ≡ 4
auditRequiredEvidenceRowCountIs4 =
  Audit.requiredEvidenceRowCountIs4 canonicalAuditSurface

ledgerNeckDepthRowsIs12 :
  Counts.neckDepthRows canonicalLedgerExactCounts ≡ 12
ledgerNeckDepthRowsIs12 =
  Counts.canonicalLedgerNeckDepthRowsIs12

ledgerShellEnvelopeRowsIs4 :
  Counts.shellEnvelopeRows canonicalLedgerExactCounts ≡ 4
ledgerShellEnvelopeRowsIs4 =
  Counts.canonicalLedgerShellEnvelopeRowsIs4

ledgerJSJUnionBlockersIs7 :
  Counts.jsjUnionBlockers canonicalLedgerExactCounts ≡ 7
ledgerJSJUnionBlockersIs7 =
  Counts.canonicalLedgerJSJUnionBlockersIs7

ledgerConstructibleRowsIs10 :
  Counts.constructibleRows canonicalLedgerExactCounts ≡ 10
ledgerConstructibleRowsIs10 =
  Counts.canonicalLedgerConstructibleRowsIs10

gaussianInputRow2ShellWeightIs14112 :
  GaussianRows.shellWeightSurrogate GaussianRows.diagonalInputRow2 ≡ 14112
gaussianInputRow2ShellWeightIs14112 =
  refl

shellVsEnvelopeRowCountIs4 :
  length ShellEnvelope.canonicalBTProductShellVsEnvelopeRows ≡ 4
shellVsEnvelopeRowCountIs4 =
  ShellEnvelope.canonicalBTProductShellVsEnvelopeRowCountIs4

shellVsEnvelopeRow2BookkeepingOnly :
  ShellEnvelope.relationKind ShellEnvelope.shellVsEnvelopeRow2
  ≡
  ShellEnvelope.bookkeepingOnlyNoInequality
shellVsEnvelopeRow2BookkeepingOnly =
  ShellEnvelope.row2RelationIsBookkeepingOnly

neckDepthRowCountIs12 :
  NeckDepth.length NeckDepth.canonicalBTNeckDepthScaleRows ≡ 12
neckDepthRowCountIs12 =
  NeckDepth.canonicalBTNeckDepthScaleRowCountIs12

p2Depth3InverseScaleDenominatorIs8 :
  NeckDepth.inverseScaleDenominator NeckDepth.p2Depth3Row ≡ 8
p2Depth3InverseScaleDenominatorIs8 =
  NeckDepth.p2Depth3InverseScaleDenominatorIs8

p3Depth3InverseScaleDenominatorIs27 :
  NeckDepth.inverseScaleDenominator NeckDepth.p3Depth3Row ≡ 27
p3Depth3InverseScaleDenominatorIs27 =
  NeckDepth.p3Depth3InverseScaleDenominatorIs27

p7Depth3InverseScaleDenominatorIs343 :
  NeckDepth.inverseScaleDenominator NeckDepth.p7Depth3Row ≡ 343
p7Depth3InverseScaleDenominatorIs343 =
  NeckDepth.p7Depth3InverseScaleDenominatorIs343

neckSurgeryP2CrossSectionIs3 :
  NeckSurgery.crossSectionCardinality
    NeckSurgery.p2BTNeckSurgeryObligationCompositeRow
  ≡
  3
neckSurgeryP2CrossSectionIs3 =
  NeckSurgery.p2CrossSectionCardinalityIs3

neckSurgeryP3CrossSectionIs4 :
  NeckSurgery.crossSectionCardinality
    NeckSurgery.p3BTNeckSurgeryObligationCompositeRow
  ≡
  4
neckSurgeryP3CrossSectionIs4 =
  NeckSurgery.p3CrossSectionCardinalityIs4

neckSurgeryP7CrossSectionIs8 :
  NeckSurgery.crossSectionCardinality
    NeckSurgery.p7BTNeckSurgeryObligationCompositeRow
  ≡
  8
neckSurgeryP7CrossSectionIs8 =
  NeckSurgery.p7CrossSectionCardinalityIs8

boundaryCrossSectionRowCountIs3 :
  BoundaryRows.length BoundaryRows.canonicalBTBoundaryCrossSectionRows ≡ 3
boundaryCrossSectionRowCountIs3 =
  BoundaryRows.canonicalBTBoundaryCrossSectionRowCountIs3

boundaryP2CrossSectionCardinalityIs3 :
  BoundaryRows.crossSectionCardinality
    BoundaryRows.p2BoundaryCrossSectionRow
  ≡
  3
boundaryP2CrossSectionCardinalityIs3 =
  BoundaryRows.p2BoundaryCrossSectionCardinalityIs3

surgeryObligationBlockerRowCountIs3 :
  SurgeryBlockers.canonicalSurgeryObligationBlockerRowCount ≡ 3
surgeryObligationBlockerRowCountIs3 =
  SurgeryBlockers.canonicalSurgeryObligationBlockerRowCountIs3

jsjUnionBlockerCountIs7 :
  JSJNorm.unionRowsCount canonicalJSJBlockerLedger ≡ 7
jsjUnionBlockerCountIs7 =
  JSJNorm.unionRowsCountIs7 canonicalJSJBlockerLedger

jsjConcatenatedBlockerCountIs12 :
  JSJNorm.concatenatedRowsCount canonicalJSJBlockerLedger ≡ 12
jsjConcatenatedBlockerCountIs12 =
  JSJNorm.concatenatedRowsCountIs12 canonicalJSJBlockerLedger

importProbeConstructibleCountIs10 :
  ImportProbe.constructibleCount canonicalImportProbe ≡ 10
importProbeConstructibleCountIs10 =
  ImportProbe.constructibleCountIs10 canonicalImportProbe

importProbeBlockerCountIs9 :
  ImportProbe.blockerCount canonicalImportProbe ≡ 9
importProbeBlockerCountIs9 =
  ImportProbe.blockerCountIs9 canonicalImportProbe

importProbeJSJTheoremUnavailable :
  ImportProbe.jsjNormalizedTheoremAvailable canonicalImportProbe ≡ false
importProbeJSJTheoremUnavailable =
  ImportProbe.jsjNormalizedTheoremAvailableProofIsFalse canonicalImportProbe

dashboardConstructibleCountIs10 :
  Dashboard.constructibleCount canonicalDashboard ≡ 10
dashboardConstructibleCountIs10 =
  Dashboard.dashboardConstructibleCountIs10

dashboardBoundaryCrossSectionRowsIs3 :
  Dashboard.boundaryCrossSectionRows canonicalDashboard ≡ 3
dashboardBoundaryCrossSectionRowsIs3 =
  Dashboard.dashboardBoundaryCrossSectionRowsIs3

dashboardSurgeryBlockerRowsIs3 :
  Dashboard.surgeryBlockerRows canonicalDashboard ≡ 3
dashboardSurgeryBlockerRowsIs3 =
  Dashboard.dashboardSurgeryBlockerRowsIs3

record PerelmanBTRoundFullImportSmoke : Setω where
  constructor perelmanBTRoundFullImportSmoke
  field
    index :
      Index.PerelmanBTGeometrizationAnalogueIndex

    summary :
      Summary.PerelmanBTGeometrizationAnalogueSummary

    noPromotionLaw :
      NoPromotion.PerelmanBTNoPromotionLaw

    auditSurface :
      Audit.PerelmanBTNoPromotionAuditSurface

    exactCounts :
      Counts.PerelmanBTLedgerExactCounts

    jsjBlockerLedger :
      JSJNorm.JSJBlockerNormalizationLedger

    dashboard :
      Dashboard.PerelmanBTAnalogueDashboard

    importProbe :
      ImportProbe.PerelmanBTAnalogueImportProbe

    constructibleCount :
      Nat
    constructibleCountIs10 :
      constructibleCount ≡ 10

    blockerCount :
      Nat
    blockerCountIs9 :
      blockerCount ≡ 9

    noPromotionReasonCount :
      Nat
    noPromotionReasonCountProofIs7 :
      noPromotionReasonCount ≡ 7

    auditForbiddenHits :
      Nat
    auditForbiddenHitsAreZero :
      auditForbiddenHits ≡ 0

    exactLedgerConstructibleRows :
      Nat
    exactLedgerConstructibleRowsAre10 :
      exactLedgerConstructibleRows ≡ 10

    shellVsEnvelopeRowCount :
      Nat
    shellVsEnvelopeRowCountProofIs4 :
      shellVsEnvelopeRowCount ≡ 4

    neckDepthRowCount :
      Nat
    neckDepthRowCountProofIs12 :
      neckDepthRowCount ≡ 12

    jsjUnionBlockerCount :
      Nat
    jsjUnionBlockerCountProofIs7 :
      jsjUnionBlockerCount ≡ 7

    boundaryCrossSectionRowCount :
      Nat
    boundaryCrossSectionRowCountProofIs3 :
      boundaryCrossSectionRowCount ≡ 3

    surgeryObligationBlockerRowCount :
      Nat
    surgeryObligationBlockerRowCountProofIs3 :
      surgeryObligationBlockerRowCount ≡ 3

    dashboardBoundaryRows :
      Nat
    dashboardBoundaryRowsProofIs3 :
      dashboardBoundaryRows ≡ 3

    jsjTheoremAvailableHere :
      false ≡ false

open PerelmanBTRoundFullImportSmoke public

canonicalPerelmanBTRoundFullImportSmoke :
  PerelmanBTRoundFullImportSmoke
canonicalPerelmanBTRoundFullImportSmoke =
  perelmanBTRoundFullImportSmoke
    canonicalIndex
    canonicalSummary
    canonicalNoPromotionLaw
    canonicalAuditSurface
    canonicalLedgerExactCounts
    canonicalJSJBlockerLedger
    canonicalDashboard
    canonicalImportProbe
    (Index.constructibleRowCountField canonicalIndex)
    indexConstructibleCountIs10
    (Index.smoothAuthorityBlockerCountField canonicalIndex)
    indexBlockerCountIs9
    NoPromotion.noPromotionReasonCount
    noPromotionReasonCountIs7
    (Audit.forbiddenHitRowCount canonicalAuditSurface)
    auditForbiddenRowCountIs0
    (Counts.constructibleRows canonicalLedgerExactCounts)
    ledgerConstructibleRowsIs10
    (length ShellEnvelope.canonicalBTProductShellVsEnvelopeRows)
    shellVsEnvelopeRowCountIs4
    (NeckDepth.length NeckDepth.canonicalBTNeckDepthScaleRows)
    neckDepthRowCountIs12
    (JSJNorm.unionRowsCount canonicalJSJBlockerLedger)
    jsjUnionBlockerCountIs7
    (BoundaryRows.length BoundaryRows.canonicalBTBoundaryCrossSectionRows)
    boundaryCrossSectionRowCountIs3
    SurgeryBlockers.canonicalSurgeryObligationBlockerRowCount
    surgeryObligationBlockerRowCountIs3
    (Dashboard.boundaryCrossSectionRows canonicalDashboard)
    dashboardBoundaryCrossSectionRowsIs3
    refl
