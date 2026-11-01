module DASHI.Physics.Probes.PerelmanBTAnalogueImportProbe where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; List)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.BTGaussianDiagonalInputRows as GaussianRows
import DASHI.Physics.Closure.BTNeckSurgeryObligationComposite as NeckSurgery
import DASHI.Physics.Closure.JSJAnaloguePieceClassification as JSJ
import DASHI.Physics.Closure.JSJBlockerNormalization as JSJNorm
import DASHI.Physics.Closure.PerelmanBTGeometrizationAnalogueIndex as Index
import DASHI.Physics.Closure.PerelmanBTGeometrizationAnalogueSummary as Summary
import DASHI.Physics.Closure.PerelmanBTNoPromotionLaw as NoPromotion

------------------------------------------------------------------------
-- Standalone green import probe for the Perelman/BT analogue stack.
--
-- This probe intentionally stays out of AllProbes.agda and Everything.agda.
-- It imports the main closure surfaces from the recent Perelman/BT rounds
-- and exposes only concrete projection witnesses.  It does not promote any
-- smooth Ricci-flow, surgery, JSJ, geometrization, or Clay authority.

canonicalIndex :
  Index.PerelmanBTGeometrizationAnalogueIndex
canonicalIndex =
  Index.canonicalPerelmanBTGeometrizationAnalogueIndex

canonicalSummary :
  Summary.PerelmanBTGeometrizationAnalogueSummary
canonicalSummary =
  Summary.canonicalPerelmanBTGeometrizationAnalogueSummary

canonicalFalseWitnesses :
  NoPromotion.PerelmanBTFalseWitnesses
canonicalFalseWitnesses =
  NoPromotion.canonicalPerelmanBTFalseWitnesses

canonicalNoPromotionLaw :
  NoPromotion.PerelmanBTNoPromotionLaw
canonicalNoPromotionLaw =
  NoPromotion.canonicalPerelmanBTNoPromotionLaw

canonicalGaussianInputRow2 :
  GaussianRows.BTGaussianDiagonalInputRow
canonicalGaussianInputRow2 =
  GaussianRows.diagonalInputRow2

canonicalNeckSurgeryComposite :
  NeckSurgery.BTNeckSurgeryObligationComposite
canonicalNeckSurgeryComposite =
  NeckSurgery.canonicalBTNeckSurgeryObligationComposite

canonicalJSJBlockerNormalizationLedger :
  JSJNorm.JSJBlockerNormalizationLedger
canonicalJSJBlockerNormalizationLedger =
  JSJNorm.canonicalJSJBlockerNormalizationLedger

------------------------------------------------------------------------
-- Count projections.

indexConstructibleCountIs10 :
  Index.constructibleRowCountField canonicalIndex ≡ 10
indexConstructibleCountIs10 =
  Index.constructibleRowCountFieldIs10 canonicalIndex

summaryConstructibleCountIs10 :
  Summary.constructibleRowCount canonicalSummary ≡ 10
summaryConstructibleCountIs10 =
  Summary.summaryConstructibleRowCountIs10

indexBlockerCountIs9 :
  Index.smoothAuthorityBlockerCountField canonicalIndex ≡ 9
indexBlockerCountIs9 =
  Index.smoothAuthorityBlockerCountFieldIs9 canonicalIndex

summaryBlockerCountIs9 :
  Summary.blockerCount canonicalSummary ≡ 9
summaryBlockerCountIs9 =
  Summary.summaryBlockerCountIs9

noPromotionReasonCountIs7 :
  NoPromotion.noPromotionReasonCount ≡ 7
noPromotionReasonCountIs7 =
  NoPromotion.noPromotionReasonCountIs7

falseWitnessNoPromotionReasonCountIs7 :
  NoPromotion.noPromotionReasonCountField canonicalFalseWitnesses ≡ 7
falseWitnessNoPromotionReasonCountIs7 =
  NoPromotion.noPromotionReasonCountFieldIs7 canonicalFalseWitnesses

------------------------------------------------------------------------
-- BT neck cardinality projections.

indexP2CrossSectionCardinalityIs3 :
  Index.p2CrossSectionCardinalityIs3 canonicalIndex
  ≡
  Index.p2CrossSectionCardinalityIs3 canonicalIndex
indexP2CrossSectionCardinalityIs3 =
  refl

indexP3CrossSectionCardinalityIs4 :
  Index.p3CrossSectionCardinalityIs4 canonicalIndex
  ≡
  Index.p3CrossSectionCardinalityIs4 canonicalIndex
indexP3CrossSectionCardinalityIs4 =
  refl

indexP7CrossSectionCardinalityIs8 :
  Index.p7CrossSectionCardinalityIs8 canonicalIndex
  ≡
  Index.p7CrossSectionCardinalityIs8 canonicalIndex
indexP7CrossSectionCardinalityIs8 =
  refl

neckSurgeryP2CrossSectionCardinalityIs3 :
  NeckSurgery.crossSectionCardinality
    NeckSurgery.p2BTNeckSurgeryObligationCompositeRow
  ≡
  3
neckSurgeryP2CrossSectionCardinalityIs3 =
  NeckSurgery.p2CrossSectionCardinalityIs3

neckSurgeryP3CrossSectionCardinalityIs4 :
  NeckSurgery.crossSectionCardinality
    NeckSurgery.p3BTNeckSurgeryObligationCompositeRow
  ≡
  4
neckSurgeryP3CrossSectionCardinalityIs4 =
  NeckSurgery.p3CrossSectionCardinalityIs4

neckSurgeryP7CrossSectionCardinalityIs8 :
  NeckSurgery.crossSectionCardinality
    NeckSurgery.p7BTNeckSurgeryObligationCompositeRow
  ≡
  8
neckSurgeryP7CrossSectionCardinalityIs8 =
  NeckSurgery.p7CrossSectionCardinalityIs8

------------------------------------------------------------------------
-- Promotion-token and imported-row projections.

indexPromotionFlagsEmpty :
  JSJ.promotionFlags (Index.jsjPieceReceipt canonicalIndex) ≡ []
indexPromotionFlagsEmpty =
  Index.jsjPromotionFlagsEmpty canonicalIndex

summarySmoothPromotionFalse :
  Summary.smoothPromotionStatus canonicalSummary
  ≡
  false
summarySmoothPromotionFalse =
  Summary.summarySmoothPromotionFalse

summaryClayPromotionFalse :
  Summary.clayPromotionStatus canonicalSummary
  ≡
  false
summaryClayPromotionFalse =
  Summary.summaryClayPromotionFalse

gaussianInputRow2RadiusIs2 :
  GaussianRows.radius canonicalGaussianInputRow2 ≡ 2
gaussianInputRow2RadiusIs2 =
  refl

gaussianInputRow2ShellWeightIs14112 :
  GaussianRows.shellWeightSurrogate canonicalGaussianInputRow2 ≡ 14112
gaussianInputRow2ShellWeightIs14112 =
  refl

neckSurgeryCompositeRowsCanonical :
  NeckSurgery.rows canonicalNeckSurgeryComposite
  ≡
  NeckSurgery.canonicalBTNeckSurgeryObligationCompositeRows
neckSurgeryCompositeRowsCanonical =
  NeckSurgery.rowsAreCanonical canonicalNeckSurgeryComposite

jsjNormalizedBTBlockerCountIs6 :
  JSJNorm.btRowsCount canonicalJSJBlockerNormalizationLedger ≡ 6
jsjNormalizedBTBlockerCountIs6 =
  JSJNorm.btRowsCountIs6 canonicalJSJBlockerNormalizationLedger

jsjNormalized369BlockerCountIs6 :
  JSJNorm.hyperfabric369RowsCount canonicalJSJBlockerNormalizationLedger ≡ 6
jsjNormalized369BlockerCountIs6 =
  JSJNorm.hyperfabric369RowsCountIs6 canonicalJSJBlockerNormalizationLedger

jsjNormalizedUnionBlockerCountIs7 :
  JSJNorm.unionRowsCount canonicalJSJBlockerNormalizationLedger ≡ 7
jsjNormalizedUnionBlockerCountIs7 =
  JSJNorm.unionRowsCountIs7 canonicalJSJBlockerNormalizationLedger

jsjNormalizedConcatenatedBlockerCountIs12 :
  JSJNorm.concatenatedRowsCount canonicalJSJBlockerNormalizationLedger ≡ 12
jsjNormalizedConcatenatedBlockerCountIs12 =
  JSJNorm.concatenatedRowsCountIs12 canonicalJSJBlockerNormalizationLedger

jsjNormalizedTheoremUnavailable :
  JSJNorm.jsjTheoremAvailableHere canonicalJSJBlockerNormalizationLedger
  ≡
  false
jsjNormalizedTheoremUnavailable =
  JSJNorm.canonicalLedgerKeepsJSJUnavailable

record PerelmanBTAnalogueImportProbe : Set where
  field
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

    p2Cardinality :
      Nat
    p2CardinalityIs3 :
      p2Cardinality ≡ 3

    p3Cardinality :
      Nat
    p3CardinalityIs4 :
      p3Cardinality ≡ 4

    p7Cardinality :
      Nat
    p7CardinalityIs8 :
      p7Cardinality ≡ 8

    promotionFlags :
      List JSJ.PromotionFlag
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    jsjNormalizedUnionBlockerCount :
      Nat
    jsjNormalizedUnionBlockerCountProofIs7 :
      jsjNormalizedUnionBlockerCount ≡ 7

    jsjNormalizedTheoremAvailable :
      Bool
    jsjNormalizedTheoremAvailableProofIsFalse :
      jsjNormalizedTheoremAvailable ≡ false

open PerelmanBTAnalogueImportProbe public

canonicalPerelmanBTAnalogueImportProbe :
  PerelmanBTAnalogueImportProbe
canonicalPerelmanBTAnalogueImportProbe =
  record
    { constructibleCount =
        Index.constructibleRowCountField canonicalIndex
    ; constructibleCountIs10 =
        indexConstructibleCountIs10
    ; blockerCount =
        Index.smoothAuthorityBlockerCountField canonicalIndex
    ; blockerCountIs9 =
        indexBlockerCountIs9
    ; noPromotionReasonCount =
        NoPromotion.noPromotionReasonCountField canonicalFalseWitnesses
    ; noPromotionReasonCountProofIs7 =
        falseWitnessNoPromotionReasonCountIs7
    ; p2Cardinality =
        NeckSurgery.crossSectionCardinality
          NeckSurgery.p2BTNeckSurgeryObligationCompositeRow
    ; p2CardinalityIs3 =
        neckSurgeryP2CrossSectionCardinalityIs3
    ; p3Cardinality =
        NeckSurgery.crossSectionCardinality
          NeckSurgery.p3BTNeckSurgeryObligationCompositeRow
    ; p3CardinalityIs4 =
        neckSurgeryP3CrossSectionCardinalityIs4
    ; p7Cardinality =
        NeckSurgery.crossSectionCardinality
          NeckSurgery.p7BTNeckSurgeryObligationCompositeRow
    ; p7CardinalityIs8 =
        neckSurgeryP7CrossSectionCardinalityIs8
    ; promotionFlags =
        JSJ.promotionFlags (Index.jsjPieceReceipt canonicalIndex)
    ; promotionFlagsAreEmpty =
        indexPromotionFlagsEmpty
    ; jsjNormalizedUnionBlockerCount =
        JSJNorm.unionRowsCount canonicalJSJBlockerNormalizationLedger
    ; jsjNormalizedUnionBlockerCountProofIs7 =
        jsjNormalizedUnionBlockerCountIs7
    ; jsjNormalizedTheoremAvailable =
        JSJNorm.jsjTheoremAvailableHere canonicalJSJBlockerNormalizationLedger
    ; jsjNormalizedTheoremAvailableProofIsFalse =
        jsjNormalizedTheoremUnavailable
    }
