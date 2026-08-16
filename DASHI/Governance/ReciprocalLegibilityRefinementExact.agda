module DASHI.Governance.ReciprocalLegibilityRefinementExact where

------------------------------------------------------------------------
-- SOURCE / CROSS-POLLINATION CALIBRATION
--
-- Author: Helen Nissenbaum.
-- Title: "Privacy as Contextual Integrity".
-- Venue: Washington Law Review 79(1):119--158 (2004).
-- DOI: no DOI listed in the cited journal record.
--
-- Author: David Blackwell.
-- Title: "Equivalent Comparisons of Experiments".
-- Venue: The Annals of Mathematical Statistics 24(2):265--272 (1953).
-- DOI: 10.1214/aoms/1177729032.
--
-- The sources motivate context-relative information flow and comparison of
-- information structures.  The exact directional refinement theorem is DASHI's
-- construction.
--
-- Central duality: adding a distinguishing coordinate to the institution-side
-- view while withholding it from the subject can create an exact legibility
-- gap; exposing the same full coordinate pair to the subject admits an exact
-- decoder.  This is an information theorem, not a rule requiring universal
-- disclosure or classifying asymmetric systems as abusive/illegal.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.AsymmetricLegibilityContestabilityExact as Legibility
import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

record DirectionalObservationRefinement : Set₁ where
  constructor directionalObservationRefinement
  field
    Case : Set
    Base : Set
    Extra : Set
    baseObservation : Case → Base
    extraObservation : Case → Extra

open DirectionalObservationRefinement public

------------------------------------------------------------------------
-- Institution-only refinement: institution sees Base × Extra; subject sees Base.
------------------------------------------------------------------------

institutionOnlyChannel :
  DirectionalObservationRefinement → Legibility.LegibilityChannel
institutionOnlyChannel R =
  Legibility.legibilityChannel
    (Case R)
    (Base R × Extra R)
    (Base R)
    (λ case → baseObservation R case , extraObservation R case)
    proj₁

------------------------------------------------------------------------
-- Reciprocal full-view channel: both sides receive Base × Extra.
------------------------------------------------------------------------

reciprocalFullViewChannel :
  DirectionalObservationRefinement → Legibility.LegibilityChannel
reciprocalFullViewChannel R =
  Legibility.legibilityChannel
    (Case R)
    (Base R × Extra R)
    (Base R × Extra R)
    (λ case → baseObservation R case , extraObservation R case)
    (λ view → view)

record DirectionalSplitWitness
  (R : DirectionalObservationRefinement) : Set where
  constructor directionalSplitWitness
  field
    left right : Case R
    baseSame : baseObservation R left ≡ baseObservation R right
    extraDifferent : extraObservation R left ≡ extraObservation R right → ⊥

open DirectionalSplitWitness public

institutionOnlyRefinementCreatesLegibilityGap :
  ∀ {R : DirectionalObservationRefinement} →
  DirectionalSplitWitness R →
  Legibility.AsymmetricLegibilityWitness (institutionOnlyChannel R)
institutionOnlyRefinementCreatesLegibilityGap split =
  Legibility.asymmetricLegibilityWitness
    (left split)
    (right split)
    institutionSeparates
    (baseSame split)
  where
    institutionSeparates :
      Legibility.inspect (institutionOnlyChannel _) (left split)
      ≡ Legibility.inspect (institutionOnlyChannel _) (right split)
      → ⊥
    institutionSeparates equalViews =
      extraDifferent split (cong proj₂ equalViews)

institutionOnlyGapBlocksExactSubjectRecovery :
  ∀ {R : DirectionalObservationRefinement}
    (split : DirectionalSplitWitness R) →
  Legibility.ExactInstitutionalViewDecoder (institutionOnlyChannel R) → ⊥
institutionOnlyGapBlocksExactSubjectRecovery split =
  Legibility.asymmetricGapBlocksExactSubjectRecovery
    (institutionOnlyRefinementCreatesLegibilityGap split)

reciprocalFullViewHasExactDecoder :
  ∀ {R : DirectionalObservationRefinement} →
  Legibility.ExactInstitutionalViewDecoder (reciprocalFullViewChannel R)
reciprocalFullViewHasExactDecoder =
  Legibility.exactInstitutionalViewDecoder
    (λ view → view)
    (λ subject → refl)

------------------------------------------------------------------------
-- Finite witness.
------------------------------------------------------------------------

data Case2 : Set where case0 case1 : Case2
data BaseOne : Set where sameBase : BaseOne
data Extra2 : Set where extra0 extra1 : Extra2

base2 : Case2 → BaseOne
base2 case0 = sameBase
base2 case1 = sameBase

extra2 : Case2 → Extra2
extra2 case0 = extra0
extra2 case1 = extra1

finiteDirectionalRefinement : DirectionalObservationRefinement
finiteDirectionalRefinement =
  directionalObservationRefinement Case2 BaseOne Extra2 base2 extra2

finiteDirectionalSplit : DirectionalSplitWitness finiteDirectionalRefinement
finiteDirectionalSplit =
  directionalSplitWitness case0 case1 refl (λ ())

finiteInstitutionOnlyDecoderImpossible :
  Legibility.ExactInstitutionalViewDecoder
    (institutionOnlyChannel finiteDirectionalRefinement) → ⊥
finiteInstitutionOnlyDecoderImpossible =
  institutionOnlyGapBlocksExactSubjectRecovery finiteDirectionalSplit

finiteReciprocalDecoderExists :
  Legibility.ExactInstitutionalViewDecoder
    (reciprocalFullViewChannel finiteDirectionalRefinement)
finiteReciprocalDecoderExists = reciprocalFullViewHasExactDecoder

------------------------------------------------------------------------
-- Boundary and source receipt.
------------------------------------------------------------------------

record ReciprocalLegibilityBoundary : Set where
  constructor reciprocalLegibilityBoundary
  field
    institutionOnlyRefinementCanCreateInformationGap : Bool
    reciprocalFullViewCanAdmitExactDecoder : Bool
    informationSymmetryAutomaticallyRequired : Bool
    asymmetryAutomaticallyProvesAbuse : Bool
    extraObservationAutomaticallyAuthorized : Bool

canonicalReciprocalLegibilityBoundary : ReciprocalLegibilityBoundary
canonicalReciprocalLegibilityBoundary =
  reciprocalLegibilityBoundary true true false false false

record ReciprocalLegibilityReceipt : Set where
  constructor reciprocalLegibilityReceipt
  field
    sources : List Sources.ScholarlySource
    boundary : ReciprocalLegibilityBoundary

canonicalReciprocalLegibilityReceipt : ReciprocalLegibilityReceipt
canonicalReciprocalLegibilityReceipt =
  reciprocalLegibilityReceipt
    (Sources.nissenbaumContextualIntegrity
      ∷ Sources.blackwellExperimentComparison
      ∷ [])
    canonicalReciprocalLegibilityBoundary
