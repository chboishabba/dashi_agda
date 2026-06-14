module DASHI.Physics.Closure.PerelmanBTAnalogueDashboard where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.PerelmanBTGeometrizationAnalogueSummary as Summary
import DASHI.Physics.Closure.PerelmanBTLedgerExactCounts as Counts
import DASHI.Physics.Closure.PerelmanBTNoPromotionLaw as NoPromotion
import DASHI.Physics.Closure.JSJBlockerNormalization as JSJ
import DASHI.Physics.Closure.BTBoundaryCrossSectionRows as BoundaryRows
import DASHI.Physics.Closure.BTNeckDepthScaleArithmetic as NeckDepth
import DASHI.Physics.Closure.BTProductShellVsEnvelopeRows as ShellRows
import DASHI.Physics.Closure.SurgeryObligationBlockerNormalization as SurgeryBlockers

------------------------------------------------------------------------
-- Compact dashboard for the current Perelman/BT analogue status.
--
-- This module aggregates already-checked closure surfaces only.  It is a
-- status dashboard, not a promotion layer: smooth Ricci flow, surgery,
-- JSJ/geometrization, and Clay authority remain explicitly false.

dashboardStatus : String
dashboardStatus =
  "Perelman/BT analogue dashboard: discrete rows present; smooth authority remains closed."

dashboardConstructibleStatus : String
dashboardConstructibleStatus =
  "Constructible analogue rows are counted by the summary surface."

dashboardBlockerStatus : String
dashboardBlockerStatus =
  "Smooth authority blockers and JSJ normalized blockers remain fail-closed."

dashboardGovernanceStatus : String
dashboardGovernanceStatus =
  "No Clay or smooth theorem promotion is represented by this dashboard."

record PerelmanBTAnalogueDashboard : Setω where
  constructor perelmanBTAnalogueDashboard
  field
    summary :
      Summary.PerelmanBTGeometrizationAnalogueSummary

    noPromotionLaw :
      NoPromotion.PerelmanBTNoPromotionLaw

    exactCounts :
      Counts.PerelmanBTLedgerExactCounts

    exactCountsAreCanonical :
      exactCounts ≡ Counts.canonicalPerelmanBTLedgerExactCounts

    jsjBlockerLedger :
      JSJ.JSJBlockerNormalizationLedger

    jsjBlockerLedgerIsCanonical :
      jsjBlockerLedger ≡ JSJ.canonicalJSJBlockerNormalizationLedger

    dashboardStatusText :
      String

    dashboardStatusTextIsCanonical :
      dashboardStatusText ≡ dashboardStatus

    constructibleStatusText :
      String

    constructibleStatusTextIsCanonical :
      constructibleStatusText ≡ dashboardConstructibleStatus

    blockerStatusText :
      String

    blockerStatusTextIsCanonical :
      blockerStatusText ≡ dashboardBlockerStatus

    governanceStatusText :
      String

    governanceStatusTextIsCanonical :
      governanceStatusText ≡ dashboardGovernanceStatus

    constructibleCount :
      Nat

    constructibleCountIs10 :
      constructibleCount ≡ 10

    constructibleCountMatchesSummary :
      constructibleCount ≡ Summary.constructibleRowCount summary

    smoothBlockerCount :
      Nat

    smoothBlockerCountIs9 :
      smoothBlockerCount ≡ 9

    smoothBlockerCountMatchesSummary :
      smoothBlockerCount ≡ Summary.blockerCount summary

    noPromotionReasonCount :
      Nat

    noPromotionReasonCountIs7 :
      noPromotionReasonCount ≡ 7

    noPromotionReasonCountMatchesLaw :
      noPromotionReasonCount
      ≡
      NoPromotion.noPromotionReasonCountField
        (NoPromotion.falseWitnesses noPromotionLaw)

    neckDepthRowCount :
      Nat

    neckDepthRowCountIs12 :
      neckDepthRowCount ≡ 12

    neckDepthRowsCountMatchesCanonical :
      NeckDepth.length NeckDepth.canonicalBTNeckDepthScaleRows
      ≡
      neckDepthRowCount

    shellRowCount :
      Nat

    shellRowCountIs4 :
      shellRowCount ≡ 4

    shellRowsCountWitnessIsCanonical :
      ShellRows.canonicalBTProductShellVsEnvelopeRowCountIs4 ≡ refl

    shellRowCountMatchesExactLedger :
      shellRowCount ≡ Counts.shellEnvelopeRows exactCounts

    boundaryCrossSectionRows :
      Nat

    boundaryCrossSectionRowsIs3 :
      boundaryCrossSectionRows ≡ 3

    boundaryCrossSectionRowsMatchLedger :
      BoundaryRows.length BoundaryRows.canonicalBTBoundaryCrossSectionRows
      ≡
      boundaryCrossSectionRows

    surgeryBlockerRows :
      Nat

    surgeryBlockerRowsIs3 :
      surgeryBlockerRows ≡ 3

    surgeryBlockerRowsMatchLedger :
      surgeryBlockerRows
      ≡
      SurgeryBlockers.canonicalSurgeryObligationBlockerRowCount

    jsjUnionBlockerCount :
      Nat

    jsjUnionBlockerCountIs7 :
      jsjUnionBlockerCount ≡ 7

    jsjUnionBlockerCountMatchesLedger :
      jsjUnionBlockerCount ≡ JSJ.unionRowsCount jsjBlockerLedger

    smoothPromotion :
      Bool

    smoothPromotionIsFalse :
      smoothPromotion ≡ false

    smoothPromotionMatchesSummary :
      smoothPromotion ≡ Summary.smoothPromotionStatus summary

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    clayPromotionMatchesSummary :
      clayPromotion ≡ Summary.clayPromotionStatus summary

    jsjPromotionStillFalse :
      JSJ.jsjTheoremAvailableHere jsjBlockerLedger ≡ false

open PerelmanBTAnalogueDashboard public

canonicalPerelmanBTAnalogueDashboard :
  PerelmanBTAnalogueDashboard
canonicalPerelmanBTAnalogueDashboard =
  perelmanBTAnalogueDashboard
    Summary.canonicalPerelmanBTGeometrizationAnalogueSummary
    NoPromotion.canonicalPerelmanBTNoPromotionLaw
    Counts.canonicalPerelmanBTLedgerExactCounts
    refl
    JSJ.canonicalJSJBlockerNormalizationLedger
    refl
    dashboardStatus
    refl
    dashboardConstructibleStatus
    refl
    dashboardBlockerStatus
    refl
    dashboardGovernanceStatus
    refl
    10
    refl
    refl
    9
    refl
    refl
    7
    refl
    refl
    12
    refl
    NeckDepth.canonicalBTNeckDepthScaleRowCountIs12
    4
    refl
    refl
    refl
    3
    refl
    BoundaryRows.canonicalBTBoundaryCrossSectionRowCountIs3
    3
    refl
    refl
    7
    refl
    refl
    false
    refl
    refl
    false
    refl
    refl
    JSJ.canonicalLedgerKeepsJSJUnavailable

dashboardConstructibleCountIs10 :
  constructibleCount canonicalPerelmanBTAnalogueDashboard ≡ 10
dashboardConstructibleCountIs10 =
  refl

dashboardSmoothBlockerCountIs9 :
  smoothBlockerCount canonicalPerelmanBTAnalogueDashboard ≡ 9
dashboardSmoothBlockerCountIs9 =
  refl

dashboardNoPromotionReasonCountIs7 :
  noPromotionReasonCount canonicalPerelmanBTAnalogueDashboard ≡ 7
dashboardNoPromotionReasonCountIs7 =
  refl

dashboardNeckDepthRowCountIs12 :
  neckDepthRowCount canonicalPerelmanBTAnalogueDashboard ≡ 12
dashboardNeckDepthRowCountIs12 =
  refl

dashboardShellRowCountIs4 :
  shellRowCount canonicalPerelmanBTAnalogueDashboard ≡ 4
dashboardShellRowCountIs4 =
  refl

dashboardBoundaryCrossSectionRowsIs3 :
  boundaryCrossSectionRows canonicalPerelmanBTAnalogueDashboard ≡ 3
dashboardBoundaryCrossSectionRowsIs3 =
  refl

dashboardSurgeryBlockerRowsIs3 :
  surgeryBlockerRows canonicalPerelmanBTAnalogueDashboard ≡ 3
dashboardSurgeryBlockerRowsIs3 =
  refl

dashboardJSJUnionBlockerCountIs7 :
  jsjUnionBlockerCount canonicalPerelmanBTAnalogueDashboard ≡ 7
dashboardJSJUnionBlockerCountIs7 =
  refl

dashboardSmoothPromotionFalse :
  smoothPromotion canonicalPerelmanBTAnalogueDashboard ≡ false
dashboardSmoothPromotionFalse =
  refl

dashboardClayPromotionFalse :
  clayPromotion canonicalPerelmanBTAnalogueDashboard ≡ false
dashboardClayPromotionFalse =
  refl
