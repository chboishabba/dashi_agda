module DASHI.Cognition.PNF.SensibLawCountryJuridicalHumanityButForRemedyEverything where

------------------------------------------------------------------------
-- COUNTRY / JURIDICAL HUMANITY / BUT-FOR REALISED-REPAIR CAPSTONE
--
-- Extends the existing Country/remedy capstone with counterfactual discipline.
-- Strong legal-functional classification and open causal counterfactuals are
-- deliberately allowed to coexist.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawCountryJuridicalHumanityRemedyActuationEverything as Prior
import DASHI.Cognition.PNF.SensibLawCountryButForRealisedRepairTwoEyedExact as ButFor
import DASHI.Core.CounterfactualRealisedRepairExact as RepairCF
import DASHI.Core.CounterfactualModelContractExact as Counterfactual

------------------------------------------------------------------------
-- Strong existing legal-functional classification remains intact.
------------------------------------------------------------------------

terraNulliusJuridicalClassificationRemainsStrong :
  Prior.terraNulliusIsJuridicallyNonHumanAtFoundationalRelation
  ≡ Prior.terraNulliusIsJuridicallyNonHumanAtFoundationalRelation
terraNulliusJuridicalClassificationRemainsStrong = refl

------------------------------------------------------------------------
-- But downstream material/history counterfactuals are not thereby identified.
------------------------------------------------------------------------

countryCounterfactualUnderidentified :
  RepairCF.CounterfactualRepairUnderidentification ButFor.countryCounterfactualFibre
countryCounterfactualUnderidentified = ButFor.countryCounterfactualCurrentlyUnderidentified

billyRemedyCounterfactualUnderidentified :
  RepairCF.CounterfactualRepairUnderidentification ButFor.billyCounterfactualFibre
billyRemedyCounterfactualUnderidentified = ButFor.billyCounterfactualCurrentlyUnderidentified

------------------------------------------------------------------------
-- Rejection/deletion is weaker than positive relation transformation.
------------------------------------------------------------------------

terraNulliusCounterfactualIsNotDeletionOnly :
  RepairCF.correctionIsMereDeletion ButFor.terraNulliusRelationCorrection ≡ false
terraNulliusCounterfactualIsNotDeletionOnly = refl

terraNulliusCounterfactualAddsPositiveRelationStructure :
  RepairCF.correctedRelationAddsPositiveStructure ButFor.terraNulliusRelationCorrection ≡ true
terraNulliusCounterfactualAddsPositiveRelationStructure = refl

billyCounterfactualIsNotDeclarationOnly :
  RepairCF.correctionIsMereDeletion ButFor.billyRemedyCorrection ≡ false
billyCounterfactualIsNotDeclarationOnly = refl

------------------------------------------------------------------------
-- Current reverse-search obligations.
------------------------------------------------------------------------

countryButForNeeds : List RepairCF.CounterfactualRepairNeed
countryButForNeeds = ButFor.needs ButFor.butForJuridicalNonConstitution

billyButForNeeds : List RepairCF.CounterfactualRepairNeed
billyButForNeeds = ButFor.needs ButFor.butForFailureToActuateBillyRemedy

------------------------------------------------------------------------
-- Cross-pollination with the legal but-for lane is structural, not doctrinal.
------------------------------------------------------------------------

legalButForCompatibility : ButFor.LegalButForCrossPollinationBoundary
legalButForCompatibility = ButFor.canonicalLegalButForCrossPollinationBoundary

sharesGenericCounterfactualContract :
  ButFor.sharedGenericCounterfactualContract legalButForCompatibility ≡ true
sharesGenericCounterfactualContract = refl

doesNotImportLegalFactualCausationDoctrine :
  ButFor.importsLegalFactualCausationDoctrine legalButForCompatibility ≡ false
doesNotImportLegalFactualCausationDoctrine = refl

------------------------------------------------------------------------
-- Counterfactual-model constitution remains inherited.
------------------------------------------------------------------------

counterfactualBoundary : Counterfactual.CounterfactualBoundary
counterfactualBoundary = Counterfactual.canonicalCounterfactualBoundary

arbitraryAlternativeStillNotCausalCounterfactual :
  Counterfactual.arbitraryAlternativeIsCausalCounterfactual counterfactualBoundary ≡ false
arbitraryAlternativeStillNotCausalCounterfactual = refl

heldFixedCoordinatesStillNeedJustification :
  Counterfactual.heldFixedCoordinatesNeedJustification counterfactualBoundary ≡ true
heldFixedCoordinatesStillNeedJustification = refl

------------------------------------------------------------------------
-- Headline boundary.
------------------------------------------------------------------------

record CountryButForHeadlineBoundary : Set where
  constructor country-but-for-headline-boundary
  field
    strongJuridicalClassificationRequiresClosedHistoricalCounterfactual : Bool
    strongJuridicalClassificationRequiresClosedHistoricalCounterfactualIsFalse :
      strongJuridicalClassificationRequiresClosedHistoricalCounterfactual ≡ false
    doctrinalRejectionEqualsMaterialTransformation : Bool
    doctrinalRejectionEqualsMaterialTransformationIsFalse :
      doctrinalRejectionEqualsMaterialTransformation ≡ false
    hrcMeritsFindingEqualsCounterfactualImplementationEffect : Bool
    hrcMeritsFindingEqualsCounterfactualImplementationEffectIsFalse :
      hrcMeritsFindingEqualsCounterfactualImplementationEffect ≡ false
    communityDefinedOutcomeRemainsIndependentCoordinate : Bool
    communityDefinedOutcomeRemainsIndependentCoordinateIsTrue :
      communityDefinedOutcomeRemainsIndependentCoordinate ≡ true

open CountryButForHeadlineBoundary public

canonicalCountryButForHeadlineBoundary : CountryButForHeadlineBoundary
canonicalCountryButForHeadlineBoundary = country-but-for-headline-boundary
  false refl
  false refl
  false refl
  true refl
