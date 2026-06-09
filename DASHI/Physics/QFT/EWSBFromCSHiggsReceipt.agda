module DASHI.Physics.QFT.EWSBFromCSHiggsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Electroweak-symmetry-breaking candidate from CS/Higgs transition data.
--
-- This receipt records the Higgs/EWSB line as a candidate topological
-- transition in Chern-Simons level/boundary data.  It deliberately keeps the
-- physical Higgs potential, VEV scale, Weinberg angle, exact W/Z masses, exact
-- Standard Model match, G_DHR ~= G_SM, and terminal promotion open/false.

data EWSBTransitionStatus : Set where
  csLevelTopologicalTransitionCandidate :
    EWSBTransitionStatus

data VEVScaleStatus : Set where
  vevScaleOpen :
    VEVScaleStatus

data HiggsMechanismStatus : Set where
  physicalHiggsMechanismOpen :
    HiggsMechanismStatus

csHiggsTransitionLabel : String
csHiggsTransitionLabel =
  "EWSB as a Chern-Simons level / topological transition candidate"

vevScaleOpenLabel : String
vevScaleOpenLabel =
  "The Higgs VEV scale is open; no numerical v=246 GeV scale is derived here"

higgsMechanismOpenLabel : String
higgsMechanismOpenLabel =
  "Physical Higgs potential, Weinberg angle, and W/Z mass splitting remain open"

record EWSBFromCSHiggsReceipt : Setω where
  field
    transitionStatus :
      EWSBTransitionStatus

    transitionStatusIsCandidate :
      transitionStatus ≡ csLevelTopologicalTransitionCandidate

    transitionStatement :
      String

    transitionStatementIsCanonical :
      transitionStatement ≡ csHiggsTransitionLabel

    csLevelTransitionCandidate :
      Bool

    csLevelTransitionCandidateIsTrue :
      csLevelTransitionCandidate ≡ true

    topologicalTransitionCandidate :
      Bool

    topologicalTransitionCandidateIsTrue :
      topologicalTransitionCandidate ≡ true

    ewSymmetryBreakingCandidate :
      Bool

    ewSymmetryBreakingCandidateIsTrue :
      ewSymmetryBreakingCandidate ≡ true

    vevStatus :
      VEVScaleStatus

    vevStatusIsOpen :
      vevStatus ≡ vevScaleOpen

    vevScaleConstructed :
      Bool

    vevScaleConstructedIsFalse :
      vevScaleConstructed ≡ false

    vevScaleBoundary :
      String

    vevScaleBoundaryIsCanonical :
      vevScaleBoundary ≡ vevScaleOpenLabel

    higgsMechanismStatus :
      HiggsMechanismStatus

    higgsMechanismStatusIsOpen :
      higgsMechanismStatus ≡ physicalHiggsMechanismOpen

    physicalHiggsPotentialConstructed :
      Bool

    physicalHiggsPotentialConstructedIsFalse :
      physicalHiggsPotentialConstructed ≡ false

    weinbergAngleConstructed :
      Bool

    weinbergAngleConstructedIsFalse :
      weinbergAngleConstructed ≡ false

    exactWZMassSplittingConstructed :
      Bool

    exactWZMassSplittingConstructedIsFalse :
      exactWZMassSplittingConstructed ≡ false

    higgsMechanismBoundary :
      String

    higgsMechanismBoundaryIsCanonical :
      higgsMechanismBoundary ≡ higgsMechanismOpenLabel

    exactPhysicalEWSB :
      Bool

    exactPhysicalEWSBIsFalse :
      exactPhysicalEWSB ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    exactGDHREqualsGSMPromoted :
      Bool

    exactGDHREqualsGSMPromotedIsFalse :
      exactGDHREqualsGSMPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    receiptBoundary :
      List String

open EWSBFromCSHiggsReceipt public

canonicalEWSBFromCSHiggsReceipt :
  EWSBFromCSHiggsReceipt
canonicalEWSBFromCSHiggsReceipt =
  record
    { transitionStatus =
        csLevelTopologicalTransitionCandidate
    ; transitionStatusIsCandidate =
        refl
    ; transitionStatement =
        csHiggsTransitionLabel
    ; transitionStatementIsCanonical =
        refl
    ; csLevelTransitionCandidate =
        true
    ; csLevelTransitionCandidateIsTrue =
        refl
    ; topologicalTransitionCandidate =
        true
    ; topologicalTransitionCandidateIsTrue =
        refl
    ; ewSymmetryBreakingCandidate =
        true
    ; ewSymmetryBreakingCandidateIsTrue =
        refl
    ; vevStatus =
        vevScaleOpen
    ; vevStatusIsOpen =
        refl
    ; vevScaleConstructed =
        false
    ; vevScaleConstructedIsFalse =
        refl
    ; vevScaleBoundary =
        vevScaleOpenLabel
    ; vevScaleBoundaryIsCanonical =
        refl
    ; higgsMechanismStatus =
        physicalHiggsMechanismOpen
    ; higgsMechanismStatusIsOpen =
        refl
    ; physicalHiggsPotentialConstructed =
        false
    ; physicalHiggsPotentialConstructedIsFalse =
        refl
    ; weinbergAngleConstructed =
        false
    ; weinbergAngleConstructedIsFalse =
        refl
    ; exactWZMassSplittingConstructed =
        false
    ; exactWZMassSplittingConstructedIsFalse =
        refl
    ; higgsMechanismBoundary =
        higgsMechanismOpenLabel
    ; higgsMechanismBoundaryIsCanonical =
        refl
    ; exactPhysicalEWSB =
        false
    ; exactPhysicalEWSBIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; exactGDHREqualsGSMPromoted =
        false
    ; exactGDHREqualsGSMPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; receiptBoundary =
        "EWSB is recorded as a CS-level/topological transition candidate"
        ∷ "The Higgs VEV scale remains open"
        ∷ "The physical Higgs potential, Weinberg angle, and exact W/Z mass split are not constructed"
        ∷ "No exact Standard Model, G_DHR ~= G_SM, or terminal promotion is asserted"
        ∷ []
    }

ewsbCSLevelTransitionCandidateTrue :
  csLevelTransitionCandidate canonicalEWSBFromCSHiggsReceipt
  ≡
  true
ewsbCSLevelTransitionCandidateTrue =
  refl

ewsbVEVScaleConstructedFalse :
  vevScaleConstructed canonicalEWSBFromCSHiggsReceipt
  ≡
  false
ewsbVEVScaleConstructedFalse =
  refl

ewsbExactPhysicalEWSBFalse :
  exactPhysicalEWSB canonicalEWSBFromCSHiggsReceipt
  ≡
  false
ewsbExactPhysicalEWSBFalse =
  refl
