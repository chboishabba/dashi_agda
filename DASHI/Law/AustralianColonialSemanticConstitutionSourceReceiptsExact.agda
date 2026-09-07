module DASHI.Law.AustralianColonialSemanticConstitutionSourceReceiptsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-attributed Australian colonial semantic constitution.
-- Court holdings, First Nations political statements, government/commission
-- histories, scholarship, and DASHI synthesis remain distinct proposition roles.
------------------------------------------------------------------------

data ColonialSourceRole : Set where
  highCourtHolding : ColonialSourceRole
  firstNationsPoliticalStatement : ColonialSourceRole
  governmentReconciliationHistory : ColonialSourceRole
  humanRightsCommissionFinding : ColonialSourceRole
  legalScholarship : ColonialSourceRole
  dashiAnalyticalSynthesis : ColonialSourceRole

data ColonialSemanticProposition : Set where
  preMaboSettledColonyAssumedNoRecognisedSovereign : ColonialSemanticProposition
  preMaboSettledColonyAssumedNoRecognisedSettledLaw : ColonialSemanticProposition
  terraNulliusEnabledOccupationSettlementClassification : ColonialSemanticProposition
  protectionActsImposedColonialIdentityClassification : ColonialSemanticProposition
  assimilationUsedClassificationAndAdministrativeControl : ColonialSemanticProposition
  indigenousSovereigntyNeverCededUluruPosition : ColonialSemanticProposition
  maboRejectedNoPriorLawFiction : ColonialSemanticProposition
  maboDidNotAdjudicateCrownAcquisitionOfSovereignty : ColonialSemanticProposition
  semanticDowngradingWasConstitutiveAdministrativeMechanism : ColonialSemanticProposition
  semanticDowngradingProvesSubjectiveColonialIntent : ColonialSemanticProposition

record ColonialSemanticReceipt : Set where
  constructor colonialSemanticReceipt
  field
    proposition : ColonialSemanticProposition
    sourceRole : ColonialSourceRole
    sourceReference : String
    boundedDescription : String

open ColonialSemanticReceipt public

settledColonySovereignReceipt : ColonialSemanticReceipt
settledColonySovereignReceipt = colonialSemanticReceipt
  preMaboSettledColonyAssumedNoRecognisedSovereign legalScholarship
  "Mabo (No 2) discussion as analysed by Ulla Secher, UWS Law Review 2007"
  "Pre-Mabo settled-colony orthodoxy treated Indigenous inhabitants as having no recognised sovereign for the reception-of-law framework; this describes the legal classification, not an empirical absence of Indigenous political authority."

settledColonyLawReceipt : ColonialSemanticReceipt
settledColonyLawReceipt = colonialSemanticReceipt
  preMaboSettledColonyAssumedNoRecognisedSettledLaw legalScholarship
  "Mabo (No 2) discussion; Secher 2007; Brennan/Gunn/Williams 2004"
  "The settled-colony framework depended on fictions of no prior law/no sovereign law-maker sufficiently recognised by the colonial legal order."

terraNulliusAdministrativeReceipt : ColonialSemanticReceipt
terraNulliusAdministrativeReceipt = colonialSemanticReceipt
  terraNulliusEnabledOccupationSettlementClassification governmentReconciliationHistory
  "Council for Aboriginal Reconciliation briefing, Terra nullius and sovereignty"
  "British colonisation and land laws were framed around acquisition by occupation/settlement, with Indigenous peoples acknowledged as present but denied recognised ownership/sovereignty on colonial criteria."

protectionClassificationReceipt : ColonialSemanticReceipt
protectionClassificationReceipt = colonialSemanticReceipt
  protectionActsImposedColonialIdentityClassification humanRightsCommissionFinding
  "Australian Human Rights Commission, Social Justice Report 2011, Protection Acts discussion"
  "Protection legislation imposed classificatory systems defining who was or was not Aboriginal for administrative control, based on coloniser-defined categories such as blood quantum."

assimilationClassificationReceipt : ColonialSemanticReceipt
assimilationClassificationReceipt = colonialSemanticReceipt
  assimilationUsedClassificationAndAdministrativeControl humanRightsCommissionFinding
  "Bringing Them Home; Social Justice Report 2011"
  "Segregation/protection and later assimilation policies used separate legislative and administrative regimes, identity classifications, child removal and controlled exemptions."

uluruNeverCededReceipt : ColonialSemanticReceipt
uluruNeverCededReceipt = colonialSemanticReceipt
  indigenousSovereigntyNeverCededUluruPosition firstNationsPoliticalStatement
  "Uluru Statement from the Heart, 2017"
  "The Uluru Statement states that First Nations sovereignty has never been ceded or extinguished and co-exists with Crown sovereignty. This is a First Nations political/constitutional statement, not a High Court holding that Crown sovereignty is legally invalid."

maboPriorLawReceipt : ColonialSemanticReceipt
maboPriorLawReceipt = colonialSemanticReceipt
  maboRejectedNoPriorLawFiction highCourtHolding
  "Mabo v Queensland (No 2) [1992] HCA 23; Brennan J and majority native-title reasoning"
  "Mabo rejected the legal assumptions that inhabited Australia could be treated as lacking prior law/property relations for native-title purposes and recognised surviving pre-existing land rights."

maboSovereigntyBoundaryReceipt : ColonialSemanticReceipt
maboSovereigntyBoundaryReceipt = colonialSemanticReceipt
  maboDidNotAdjudicateCrownAcquisitionOfSovereignty highCourtHolding
  "Mabo v Queensland (No 2) [1992] HCA 23; later sovereignty scholarship"
  "Mabo did not reopen the municipal justiciability of the Crown's acquisition of sovereignty; recognition of native title and rejection of terra-nullius property consequences are distinct from adjudicating the validity of sovereignty acquisition."

semanticConstitutionSynthesisReceipt : ColonialSemanticReceipt
semanticConstitutionSynthesisReceipt = colonialSemanticReceipt
  semanticDowngradingWasConstitutiveAdministrativeMechanism dashiAnalyticalSynthesis
  "DASHI synthesis over Mabo, reconciliation history, Protection/Assimilation sources and legal scholarship"
  "Where colonial legal operation depended on reclassifying inhabited Country with law/authority into categories such as settled territory, no recognised sovereign/law, protected subject or assimilable population, semantic downgrading functioned constitutively in the administrative mechanism. This is a sourced DASHI synthesis, not a quoted High Court finding of subjective colonial intent."

record ColonialSemanticBoundary : Set where
  constructor colonialSemanticBoundary
  field
    neverCededIsHighCourtHolding : Bool
    neverCededIsHighCourtHoldingIsFalse : neverCededIsHighCourtHolding ≡ false
    maboHeldCrownSovereigntyInvalid : Bool
    maboHeldCrownSovereigntyInvalidIsFalse : maboHeldCrownSovereigntyInvalid ≡ false
    semanticConstitutionEqualsSubjectiveIntentFinding : Bool
    semanticConstitutionEqualsSubjectiveIntentFindingIsFalse : semanticConstitutionEqualsSubjectiveIntentFinding ≡ false
    colonialAdministrativeClassificationWasMerelyRhetorical : Bool
    colonialAdministrativeClassificationWasMerelyRhetoricalIsFalse : colonialAdministrativeClassificationWasMerelyRhetorical ≡ false

canonicalColonialSemanticBoundary : ColonialSemanticBoundary
canonicalColonialSemanticBoundary =
  colonialSemanticBoundary false refl false refl false refl false refl
