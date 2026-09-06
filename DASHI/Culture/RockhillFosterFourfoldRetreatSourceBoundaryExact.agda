module DASHI.Culture.RockhillFosterFourfoldRetreatSourceBoundaryExact where

------------------------------------------------------------------------
-- ROCKHILL / FOSTER FOURFOLD-RETREAT SOURCE BOUNDARY
--
-- Publication carrier:
--   John Bellamy Foster and Gabriel Rockhill,
--   "Western Marxism and Imperialism: A Dialogue",
--   Monthly Review 76(10), March 2025, pp. 1-25.
--
-- Canonical publication URL:
--   https://monthlyreview.org/articles/western-marxism-and-imperialism-a-dialogue/
-- Public author-hosted access copy:
--   https://johnbellamyfoster.org/articles/western-marxism-and-imperialism-a-dialogue/
--
-- Attribution discipline:
--   upstream speaker/claim owner
--   != publication carrier
--   != access/mirror location
--   != DASHI interpretation/formalisation owner
--   != empirical authority
--   != promotion authority.
--
-- Exact locations below use speaker plus a recoverable paragraph incipit in
-- the author-hosted HTML.  This avoids inventing page precision that has not
-- independently been recovered while still making each bounded proposition
-- directly locatable.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- The four named coordinates in the dialogue.
------------------------------------------------------------------------

data RetreatAxis : Set where
  classRetreat
  imperialismCritiqueRetreat
  natureMaterialismScienceRetreat
  reasonRetreat
  : RetreatAxis

------------------------------------------------------------------------
-- Source roles are explicit rather than being inferred from a URL.
------------------------------------------------------------------------

data SourceCarrierRole : Set where
  canonicalPublicationCarrier
  authorHostedAccessCarrier
  : SourceCarrierRole

data AttributionLayer : Set where
  sourceOwnedArgument
  dashIBoundedInterpretation
  dashIFormalConstruction
  empiricalPopulationClaim
  : AttributionLayer

record SourceReceipt : Set where
  constructor source-receipt
  field
    upstreamAuthors : String
    speakerOrClaimOwner : String
    work : String
    publication : String
    date : String
    canonicalPublicationLocation : String
    accessLocation : String
    accessCarrierRole : SourceCarrierRole
    exactSourceLocation : String
    boundedProposition : String
    attributionLayer : AttributionLayer
    isPrimaryForSpeakerOwnArgument : Bool
    isEmpiricalPopulationStudy : Bool
    isDASHITheorem : Bool
    formalisationOwner : String
    promotionAuthority : String

open SourceReceipt public

------------------------------------------------------------------------
-- Foster owns the fourfold summary proposition at this source location.
------------------------------------------------------------------------

fourfoldRetreatReceipt : SourceReceipt
fourfoldRetreatReceipt =
  source-receipt
    "John Bellamy Foster; Gabriel Rockhill"
    "John Bellamy Foster"
    "Western Marxism and Imperialism: A Dialogue"
    "Monthly Review 76(10), 1-25"
    "March 2025"
    "monthlyreview.org/articles/western-marxism-and-imperialism-a-dialogue/"
    "johnbellamyfoster.org/articles/western-marxism-and-imperialism-a-dialogue/"
    authorHostedAccessCarrier
    "Foster reply; paragraph beginning: We can sum up much of our discussion so far"
    "Foster summarises much of the discussion as a fourfold retreat: from class, critique of imperialism, nature/materialism/science, and reason."
    sourceOwnedArgument
    true false false
    "DASHI repository, only for the typed receipt and later formalisation"
    "independent receipt required for any stronger historical or empirical promotion"

------------------------------------------------------------------------
-- Rockhill owns the explicit non-mechanical ideological-field qualification.
------------------------------------------------------------------------

nonMechanicalFieldReceipt : SourceReceipt
nonMechanicalFieldReceipt =
  source-receipt
    "John Bellamy Foster; Gabriel Rockhill"
    "Gabriel Rockhill"
    "Western Marxism and Imperialism: A Dialogue"
    "Monthly Review 76(10), 1-25"
    "March 2025"
    "monthlyreview.org/articles/western-marxism-and-imperialism-a-dialogue/"
    "johnbellamyfoster.org/articles/western-marxism-and-imperialism-a-dialogue/"
    authorHostedAccessCarrier
    "Rockhill reply; paragraph beginning: In order to maintain a thoroughly dialectical analysis"
    "Rockhill says the Four Retreats and abandonment of real-world socialism do not mechanically determine all aspects of every Western Marxist discourse; specific discourses occupy different positions in a broad ideological field."
    sourceOwnedArgument
    true false false
    "DASHI repository, only for the typed receipt and later formalisation"
    "independent receipt required for thinker-specific classification"

------------------------------------------------------------------------
-- The poststructuralism lane is split into two source-owned propositions.
-- Foster owns the claimed discursive-turn genealogy; Rockhill owns the later
-- characterization of the fourfold retreat as withdrawal from material reality.
------------------------------------------------------------------------

fosterDiscursiveTurnAssociationReceipt : SourceReceipt
fosterDiscursiveTurnAssociationReceipt =
  source-receipt
    "John Bellamy Foster; Gabriel Rockhill"
    "John Bellamy Foster"
    "Western Marxism and Imperialism: A Dialogue"
    "Monthly Review 76(10), 1-25"
    "March 2025"
    "monthlyreview.org/articles/western-marxism-and-imperialism-a-dialogue/"
    "johnbellamyfoster.org/articles/western-marxism-and-imperialism-a-dialogue/"
    authorHostedAccessCarrier
    "Foster reply; paragraph beginning: What remained was a circumscribed dialectic"
    "Foster says self-identified Western Marxists helped introduce a discursive turn that merged into post-Marxism, poststructuralism, postmodernism, posthumanism, postcolonialism and postcapitalism."
    sourceOwnedArgument
    true false false
    "DASHI repository, only for the typed receipt and later formalisation"
    "no genealogy or whole-tradition classification without independent evidence"

rockhillMaterialRealityWithdrawalReceipt : SourceReceipt
rockhillMaterialRealityWithdrawalReceipt =
  source-receipt
    "John Bellamy Foster; Gabriel Rockhill"
    "Gabriel Rockhill"
    "Western Marxism and Imperialism: A Dialogue"
    "Monthly Review 76(10), 1-25"
    "March 2025"
    "monthlyreview.org/articles/western-marxism-and-imperialism-a-dialogue/"
    "johnbellamyfoster.org/articles/western-marxism-and-imperialism-a-dialogue/"
    authorHostedAccessCarrier
    "Rockhill reply; paragraph beginning: This fourfold retreat constitutes a withdrawal"
    "Rockhill characterises the fourfold retreat as a withdrawal from material reality into discourse and ideas and links it to abandonment of real-world socialist construction."
    sourceOwnedArgument
    true false false
    "DASHI repository, only for the typed receipt and later formalisation"
    "independent receipt required before applying this characterization to a named thinker or tradition"

------------------------------------------------------------------------
-- Attribution / authority firewalls.
------------------------------------------------------------------------

data DialogueClaimIsUniversalClassification : Set where
data DialogueClaimIsEmpiricalPopulationLaw : Set where
data DialogueClaimIsDASHITheorem : Set where
data PoststructuralistLabelDeterminesFourRetreats : Set where
data AuthorHostedCopyCreatesAuthorship : Set where
data JointPublicationMakesEverySentenceJointlyOwned : Set where
data SourceArgumentOwnsDASHIFormalisation : Set where

dialogueDoesNotUniversallyClassifyEveryThinker :
  DialogueClaimIsUniversalClassification → ⊥
dialogueDoesNotUniversallyClassifyEveryThinker ()

dialogueIsNotEmpiricalPopulationLaw :
  DialogueClaimIsEmpiricalPopulationLaw → ⊥
dialogueIsNotEmpiricalPopulationLaw ()

dialogueIsNotDASHITheorem : DialogueClaimIsDASHITheorem → ⊥
dialogueIsNotDASHITheorem ()

poststructuralistLabelDoesNotDetermineFourRetreats :
  PoststructuralistLabelDeterminesFourRetreats → ⊥
poststructuralistLabelDoesNotDetermineFourRetreats ()

authorHostedCopyDoesNotCreateAuthorship : AuthorHostedCopyCreatesAuthorship → ⊥
authorHostedCopyDoesNotCreateAuthorship ()

jointPublicationDoesNotMakeEverySentenceJointlyOwned :
  JointPublicationMakesEverySentenceJointlyOwned → ⊥
jointPublicationDoesNotMakeEverySentenceJointlyOwned ()

sourceArgumentDoesNotOwnDASHIFormalisation :
  SourceArgumentOwnsDASHIFormalisation → ⊥
sourceArgumentDoesNotOwnDASHIFormalisation ()

record FourfoldRetreatSourceBoundary : Set where
  constructor fourfold-retreat-source-boundary
  field
    fourNamedAxesRecovered : Bool
    fieldIsExplicitlyNonMechanical : Bool
    fosterDiscursiveTurnAssociationRecovered : Bool
    rockhillMaterialWithdrawalCharacterizationRecovered : Bool
    sourceIsPrimaryForSpeakersOwnArguments : Bool
    sourceIsEmpiricalPopulationStudy : Bool
    everyPoststructuralistHasAllFourRetreats : Bool
    accessCarrierCreatesAuthorship : Bool
    jointPublicationErasesSpeakerOwnership : Bool
    DASHIFormalisationAttributedToAuthors : Bool
    strongerPromotionRequiresIndependentReceipt : Bool

canonicalFourfoldRetreatSourceBoundary : FourfoldRetreatSourceBoundary
canonicalFourfoldRetreatSourceBoundary =
  fourfold-retreat-source-boundary
    true true true true true false false false false false true
