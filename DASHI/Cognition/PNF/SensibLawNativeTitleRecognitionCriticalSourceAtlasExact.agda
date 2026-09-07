module DASHI.Cognition.PNF.SensibLawNativeTitleRecognitionCriticalSourceAtlasExact where

------------------------------------------------------------------------
-- NATIVE TITLE RECOGNITION CRITICAL SOURCE ATLAS
--
-- STRICT SOURCE-ATTRIBUTION OWNER.
--
-- This file deliberately separates:
--   * primary court holdings / court-internal premises;
--   * statutory text;
--   * attributed Indigenous sovereignty positions;
--   * named authors' critical-theory / anthropological / historical arguments;
--   * DASHI/SensibLaw critical synthesis;
--   * structural comparison.
--
-- No citation imports proof. No critical source becomes a court holding. No
-- Indigenous political/legal position becomes an Australian municipal-law
-- holding merely because it is represented here. Shared formal structure does
-- not transfer historical authorship.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Claim authority layers.
------------------------------------------------------------------------

data ClaimLayer : Set where
  primaryCourtHolding : ClaimLayer
  primaryCourtInternalPremise : ClaimLayer
  primaryStatutoryText : ClaimLayer
  indigenousSovereignPosition : ClaimLayer
  sourceCriticalTheory : ClaimLayer
  sourceAnthropologicalTheory : ClaimLayer
  sourceHistoricalTheory : ClaimLayer
  dashCriticalSynthesis : ClaimLayer
  structuralAnalogy : ClaimLayer
  proceduralStatus : ClaimLayer


record LayeredClaimReceipt : Set where
  constructor layered-claim-receipt
  field
    claimId : String
    proposition : String
    sourceReference : String
    canonicalURL : String
    layer : ClaimLayer
    directSourceSupport : Bool
    sourceSaysThisDirectly : Bool
    courtHolding : Bool
    statutoryText : Bool
    attributedAuthorTheory : Bool
    affectedCommunityOrIndigenousPosition : Bool
    worldTruthAdjudicated : Bool
    worldTruthAdjudicatedIsFalse : worldTruthAdjudicated ≡ false
    crossLayerPromotionAllowed : Bool
    crossLayerPromotionAllowedIsFalse : crossLayerPromotionAllowed ≡ false

open LayeredClaimReceipt public

------------------------------------------------------------------------
-- Primary law: bounded propositions only.
------------------------------------------------------------------------

maboRejectsEnlargedTerraNullius : LayeredClaimReceipt
maboRejectsEnlargedTerraNullius = layered-claim-receipt
  "NTCR.1"
  "Mabo (No 2) rejected the enlarged terra-nullius/common-law consequence that acquisition of sovereignty automatically left the Crown beneficial owner free of antecedent native title"
  "Mabo v Queensland (No 2) [1992] HCA 23; Brennan J reasons and later High Court summary"
  "https://www.hcourt.gov.au/sites/default/files/assets/publications/speeches/former-justices/brennanj/brennanj_canada.htm"
  primaryCourtHolding
  true true true false false false
  false refl false refl

maboSovereigntyAcquisitionNonJusticiable : LayeredClaimReceipt
maboSovereigntyAcquisitionNonJusticiable = layered-claim-receipt
  "NTCR.2"
  "Mabo treated acquisition of Crown sovereignty as non-justiciable in a municipal court while treating its consequences for native title as justiciable"
  "Mabo v Queensland (No 2) [1992] HCA 23; Brennan J sovereignty architecture"
  "https://www.hcourt.gov.au/sites/default/files/assets/publications/speeches/former-justices/brennanj/brennanj_canada.htm"
  primaryCourtInternalPremise
  true true true false false false
  false refl false refl

maboRadicalTitleAndExtinguishmentArchitecture : LayeredClaimReceipt
maboRadicalTitleAndExtinguishmentArchitecture = layered-claim-receipt
  "NTCR.3"
  "Within Australian municipal law, Mabo retained Crown radical-title architecture and recognised Crown sovereign power capable of extinguishing native title subject to applicable law"
  "Mabo v Queensland (No 2) [1992] HCA 23; court-internal property/sovereignty consequences"
  "https://www.hcourt.gov.au/sites/default/files/assets/publications/speeches/former-justices/brennanj/brennanj_canada.htm"
  primaryCourtInternalPremise
  true true true false false false
  false refl false refl

nativeTitleActObjects : LayeredClaimReceipt
nativeTitleActObjects = layered-claim-receipt
  "NTCR.4"
  "Native Title Act 1993 s 3 recognises/protects native title, establishes future-dealing standards and determination machinery, and provides for or permits validation of specified past/intermediate acts"
  "Native Title Act 1993 (Cth), s 3"
  "https://www.legislation.gov.au/C2004A04665/latest/text"
  primaryStatutoryText
  true true false true false false
  false refl false refl

nativeTitleActCommonLawRecognitionGate : LayeredClaimReceipt
nativeTitleActCommonLawRecognitionGate = layered-claim-receipt
  "NTCR.5"
  "Native Title Act 1993 s 223(1)(c) includes, within the statutory definition, the requirement that the relevant rights and interests are recognised by the common law of Australia"
  "Native Title Act 1993 (Cth), s 223(1)(c)"
  "https://www.legislation.gov.au/C2004A04665/latest/text"
  primaryStatutoryText
  true true false true false false
  false refl false refl

------------------------------------------------------------------------
-- Indigenous sovereignty position: source-backed position != municipal holding.
------------------------------------------------------------------------

watsonCoeNeverCededPosition : LayeredClaimReceipt
watsonCoeNeverCededPosition = layered-claim-receipt
  "NTCR.6"
  "Isobell Coe states, in material reproduced with Irene Watson's work, that Aboriginal sovereignty has never been ceded and no treaty was signed"
  "Irene Watson / Isobell Coe, White Law/Black Deaths, reproduced in Parliamentary submission attachment"
  "https://www.aph.gov.au/DocumentStore.ashx?id=059fb232-ca02-4137-a7d7-6f610544e422&subId=760927"
  indigenousSovereignPosition
  true true false false false true
  false refl false refl

------------------------------------------------------------------------
-- Named critical sources. These are their arguments, not court holdings.
------------------------------------------------------------------------

coulthardRecognitionPowerArgument : LayeredClaimReceipt
coulthardRecognitionPowerArgument = layered-claim-receipt
  "NTCR.7"
  "Coulthard argues that liberal politics of recognition can reproduce settler-colonial power rather than transform the underlying relation, and develops this through Fanon and a place-based reworking of Marxian dispossession"
  "Glen Sean Coulthard, Red Skin, White Masks: Rejecting the Colonial Politics of Recognition (2014)"
  "https://www.upress.umn.edu/9780816679652/red-skin-white-masks/"
  sourceCriticalTheory
  true true false false true false
  false refl false refl

povinelliCunningRecognitionArgument : LayeredClaimReceipt
povinelliCunningRecognitionArgument = layered-claim-receipt
  "NTCR.8"
  "Povinelli argues that Australian liberal multicultural recognition can perpetuate unequal power by demanding Indigenous subjects satisfy an imposed standard of authentic traditional culture"
  "Elizabeth A. Povinelli, The Cunning of Recognition (2002)"
  "https://www.dukeupress.edu/The-Cunning-of-Recognition"
  sourceAnthropologicalTheory
  true true false false true false
  false refl false refl

moretonRobinsonPossessiveWhiteSovereigntyArgument : LayeredClaimReceipt
moretonRobinsonPossessiveWhiteSovereigntyArgument = layered-claim-receipt
  "NTCR.9"
  "Moreton-Robinson theorises patriarchal white sovereignty and a possessive logic through which Australian law and nationhood naturalise white possession, including a direct critique of the Yorta Yorta decision"
  "Aileen Moreton-Robinson, The Possessive Logic of Patriarchal White Sovereignty: The High Court and the Yorta Yorta Decision"
  "https://eprints.qut.edu.au/7690/"
  sourceCriticalTheory
  true true false false true false
  false refl false refl

wolfeLogicOfEliminationArgument : LayeredClaimReceipt
wolfeLogicOfEliminationArgument = layered-claim-receipt
  "NTCR.10"
  "Wolfe theorises settler colonialism as structured by a logic of elimination while explicitly distinguishing settler colonialism from genocide and noting that Native Title's deleterious features are not equivalent to frontier homicide"
  "Patrick Wolfe, Settler colonialism and the elimination of the native, Journal of Genocide Research 8(4) (2006) 387-409"
  "https://doi.org/10.1080/14623520601056240"
  sourceHistoricalTheory
  true true false false true false
  false refl false refl

nicholsRecursiveDispossessionArgument : LayeredClaimReceipt
nicholsRecursiveDispossessionArgument = layered-claim-receipt
  "NTCR.11"
  "Nichols argues that dispossession can be recursive: systematic theft may generate the property relations through which later possession and recognition are organised"
  "Robert Nichols, Theft Is Property! Dispossession and Critical Theory (2019/2020)"
  "https://www.dukeupress.edu/theft-is-property"
  sourceCriticalTheory
  true true false false true false
  false refl false refl

crenshawSingleAxisInstitutionalInvisibility : LayeredClaimReceipt
crenshawSingleAxisInstitutionalInvisibility = layered-claim-receipt
  "NTCR.12"
  "Crenshaw's intersectionality critique shows how single-axis institutional frames can render specifically intersectional injury invisible; the repository's factorisation theorem is a later DASHI mathematical translation"
  "Kimberle Crenshaw, Demarginalizing the Intersection of Race and Sex (1989); Mapping the Margins (1991)"
  "https://chicagounbound.uchicago.edu/uclf/vol1989/iss1/8/"
  sourceCriticalTheory
  true true false false true false
  false refl false refl

------------------------------------------------------------------------
-- DASHI/SensibLaw synthesis: deliberately NOT back-attributed.
------------------------------------------------------------------------

terraNulliusDehumanisationCriticalSynthesis : LayeredClaimReceipt
terraNulliusDehumanisationCriticalSynthesis = layered-claim-receipt
  "NTCR.S1"
  "DASHI/SensibLaw critical synthesis: the terra-nullius/non-recognition structure can be analysed as juridical-ontological dehumanisation insofar as the dominant order denied Indigenous law, political authority and land relation full legibility; this is not a quotation or holding that Indigenous people were literally declared non-human"
  "DASHI/SensibLaw synthesis over Mabo's account of the old doctrine plus anticolonial/settler-colonial critical sources"
  "repo:DASHI/Cognition/PNF/SensibLawNativeTitleRecognitionCriticalSourceAtlasExact.agda"
  dashCriticalSynthesis
  false false false false false false
  false refl false refl

nativeTitleInfantilisationCriticalSynthesis : LayeredClaimReceipt
nativeTitleInfantilisationCriticalSynthesis = layered-claim-receipt
  "NTCR.S2"
  "DASHI/SensibLaw critical characterisation: a recognition regime can be infantilising or invalidating when antecedent Indigenous law, sovereignty and Country relation become legally effective only to the extent the dominant Crown/common-law observer recognises them; this is a normative/critical interpretation, not statutory language or a court holding"
  "DASHI/SensibLaw synthesis informed by Coulthard, Povinelli, Moreton-Robinson, Watson/Coe and the statutory recognition interface"
  "repo:DASHI/Cognition/PNF/SensibLawNativeTitleRecognitionCriticalSourceAtlasExact.agda"
  dashCriticalSynthesis
  false false false false false false
  false refl false refl

nativeTitleAsManagedAccommodationSynthesis : LayeredClaimReceipt
nativeTitleAsManagedAccommodationSynthesis = layered-claim-receipt
  "NTCR.S3"
  "DASHI/SensibLaw synthesis: Native Title may be represented as a major doctrinal correction and a Crown-mediated accommodation at the same time; legal advance does not entail transformation of the underlying sovereignty/property relation"
  "cross-source synthesis; no single source is assigned authorship of this exact combined proposition"
  "repo:DASHI/Cognition/PNF/SensibLawNativeTitleRecognitionCriticalSourceAtlasExact.agda"
  dashCriticalSynthesis
  false false false false false false
  false refl false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CriticalTheoryIsCourtHolding : Set where
data IndigenousPoliticalPositionIsMunicipalHolding : Set where
data MaboSaysIndigenousPeopleLiterallyNonHuman : Set where
data MoretonRobinsonClaimIsMaboAuthorship : Set where
data SharedNonFactorabilityTransfersHistoricalAuthorship : Set where
data NativeTitleCritiqueErasesMaboLegalAdvance : Set where
data WolfeLogicOfEliminationEqualsGenocideEverywhere : Set where

criticalTheoryDoesNotBecomeCourtHolding : CriticalTheoryIsCourtHolding → ⊥
criticalTheoryDoesNotBecomeCourtHolding ()

indigenousPositionDoesNotBecomeMunicipalHolding :
  IndigenousPoliticalPositionIsMunicipalHolding → ⊥
indigenousPositionDoesNotBecomeMunicipalHolding ()

maboDidNotHoldLiteralNonHumanProposition :
  MaboSaysIndigenousPeopleLiterallyNonHuman → ⊥
maboDidNotHoldLiteralNonHumanProposition ()

moretonRobinsonDoesNotBecomeMaboAuthorship :
  MoretonRobinsonClaimIsMaboAuthorship → ⊥
moretonRobinsonDoesNotBecomeMaboAuthorship ()

sharedFormalPatternDoesNotTransferAuthorship :
  SharedNonFactorabilityTransfersHistoricalAuthorship → ⊥
sharedFormalPatternDoesNotTransferAuthorship ()

critiqueDoesNotEraseDoctrinalAdvance :
  NativeTitleCritiqueErasesMaboLegalAdvance → ⊥
critiqueDoesNotEraseDoctrinalAdvance ()

wolfeDoesNotCollapseSettlerColonialismIntoGenocide :
  WolfeLogicOfEliminationEqualsGenocideEverywhere → ⊥
wolfeDoesNotCollapseSettlerColonialismIntoGenocide ()
