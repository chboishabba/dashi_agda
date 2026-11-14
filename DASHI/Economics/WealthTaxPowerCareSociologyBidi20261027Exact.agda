module DASHI.Economics.WealthTaxPowerCareSociologyBidi20261027Exact where

-- Philosophy / sociology / political economy consumer of the preceding
-- finite tax-base model.  Concrete collision proofs here are DASHI-original
-- formal translations, NOT theorems authored by the cited philosophers.
-- Research direction Johl Brown; source-writing OpenAI ChatGPT, 2026-10-27.
-- Synthetic worlds below are not observations of firms, citizens, governments
-- or taxation.  No economic causal identification is inferred.

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Economics.WealthInheritanceVacancyTaxMaxCut20261027Exact as Tax
import DASHI.Governance.RecognitionDistributionRepresentationAxesExact as Fraser
import DASHI.Philosophy.PhilosophicalPromotionBoundary as Philosophy
import DASHI.Philosophy.MaterialFeedbackIntervention as Feedback
import DASHI.Philosophy.InhumanRelationalFork as Decentring
import DASHI.Culture.HistoricalSocialTotalityBidiExact as Totality
import DASHI.Reasoning.ComparativeInstitutionalMeaningExact as Institutional
import DASHI.Wikimedia.IbrahimEnglishSocialScienceFunnelBridgeExact as Funnel

------------------------------------------------------------------------
-- NO DUPLICATED FRAMEWORK. Existing Query uses the existing INF carrier.
-- Same assessed tax liability is compatible with different voting power
-- and care outcomes, even before behavioural adaptations are modelled.
------------------------------------------------------------------------

record FiscalSocialWorld : Set where
  constructor fiscal-social-world
  field
    assessedWealth : Nat
    controllingVotes : Nat
    accessibleCareCapacity : Nat
open FiscalSocialWorld public

worldA : FiscalSocialWorld
worldA = fiscal-social-world 5 1 0

worldB : FiscalSocialWorld
worldB = fiscal-social-world 5 7 0

worldC : FiscalSocialWorld
worldC = fiscal-social-world 5 1 9

assessedTax : FiscalSocialWorld → Nat
assessedTax state =
  Tax.hundredPercentWealthExcess 3
    (Tax.owned-net-wealth (assessedWealth state))

sameTaxAB : assessedTax worldA ≡ assessedTax worldB
sameTaxAB = refl

sameTaxAC : assessedTax worldA ≡ assessedTax worldC
sameTaxAC = refl

votesABNotEqual : controllingVotes worldA ≡ controllingVotes worldB → ⊥
votesABNotEqual ()

careACNotEqual :
  accessibleCareCapacity worldA ≡ accessibleCareCapacity worldC → ⊥
careACNotEqual ()

voteInformationLost :
  INF.NonFactorabilityWitness assessedTax controllingVotes
voteInformationLost =
  INF.nonFactorabilityWitness
    worldA worldB sameTaxAB votesABNotEqual

careInformationLost :
  INF.NonFactorabilityWitness assessedTax accessibleCareCapacity
careInformationLost =
  INF.nonFactorabilityWitness
    worldA worldC sameTaxAC careACNotEqual

votesCannotFactorThroughTaxReceipt :
  INF.FactorsThrough assessedTax controllingVotes → ⊥
votesCannotFactorThroughTaxReceipt =
  INF.witnessRulesOutEveryFlatFactorisation voteInformationLost

careCannotFactorThroughTaxReceipt :
  INF.FactorsThrough assessedTax accessibleCareCapacity → ⊥
careCannotFactorThroughTaxReceipt =
  INF.witnessRulesOutEveryFlatFactorisation careInformationLost

-- Even a relabelled or statistically reweighted tax receipt cannot
-- recover either lost coordinate. Only observing MORE may repair it.
anyTaxOnlyRechartCannotRecoverVoting :
  ∀ {Other : Set} →
  (rechart : Nat → Other) →
  INF.FactorsThrough
    (λ s → rechart (assessedTax s)) controllingVotes → ⊥
anyTaxOnlyRechartCannotRecoverVoting rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart voteInformationLost

------------------------------------------------------------------------
-- Query-indexed policy adequacy: the receipt is sufficient for one query,
-- demonstrably insufficient for distinct power / social-provision queries.
------------------------------------------------------------------------

data PublicPolicyQuery : Set where
  taxDueQuery : PublicPolicyQuery
  corporateVoteQuery : PublicPolicyQuery
  careProvisionQuery : PublicPolicyQuery

policyAnswer : PublicPolicyQuery → FiscalSocialWorld → Nat
policyAnswer taxDueQuery state = assessedTax state
policyAnswer corporateVoteQuery state = controllingVotes state
policyAnswer careProvisionQuery state = accessibleCareCapacity state

policySemantics : Query.QuerySemantics
  FiscalSocialWorld PublicPolicyQuery Nat
policySemantics = Query.querySemantics policyAnswer

receiptAdequateForTaxDue :
  Query.AdequateFor assessedTax policySemantics taxDueQuery
receiptAdequateForTaxDue =
  Query.factorsForQuery
    {project = assessedTax}
    {semantics = policySemantics}
    {query = taxDueQuery}
    (λ liability → liability)
    (λ _ → refl)

receiptVotingDefect :
  Query.QueryAdequacyDefect
    assessedTax policySemantics corporateVoteQuery
receiptVotingDefect =
  Query.queryAdequacyDefect
    {project = assessedTax}
    {semantics = policySemantics}
    {query = corporateVoteQuery}
    worldA worldB sameTaxAB votesABNotEqual

receiptCareDefect :
  Query.QueryAdequacyDefect
    assessedTax policySemantics careProvisionQuery
receiptCareDefect =
  Query.queryAdequacyDefect
    {project = assessedTax}
    {semantics = policySemantics}
    {query = careProvisionQuery}
    worldA worldC sameTaxAC careACNotEqual

receiptInadequateForVoting :
  Query.AdequateFor assessedTax policySemantics corporateVoteQuery → ⊥
receiptInadequateForVoting =
  Query.queryAdequacyDefectBlocksFactorisation receiptVotingDefect

receiptInadequateForCare :
  Query.AdequateFor assessedTax policySemantics careProvisionQuery → ⊥
receiptInadequateForCare =
  Query.queryAdequacyDefectBlocksFactorisation receiptCareDefect

------------------------------------------------------------------------
-- SOURCE GENEALOGY: ORIGINAL TEXT != REPOSITORY MATHEMATICS.
-- Prior institutional source owner for Collins and Arnstein is
-- CohnInstitutionalIbrahimDeweyAcquisitionExtensionThreeExact;
-- prior Crenshaw / Fraser owners should not be duplicated as theories.
------------------------------------------------------------------------

data PhilosophicalSourceRole : Set where
  politicalTransitionProposal : PhilosophicalSourceRole
  criticalSocialReproductionTheory : PhilosophicalSourceRole
  feministLabourPoliticalArgument : PhilosophicalSourceRole
  participationPowerTypology : PhilosophicalSourceRole
  situatedStandpointTheory : PhilosophicalSourceRole
  landRentDistributionTheory : PhilosophicalSourceRole
  criticalNarrativeLegitimation : PhilosophicalSourceRole
  leftAccelerationistInstitutionalProposal : PhilosophicalSourceRole
  rightAccelerationistTechnocapitalInterpretation : PhilosophicalSourceRole
  effectiveAccelerationismMovementText : PhilosophicalSourceRole
  platformCloudRentCriticalTheory : PhilosophicalSourceRole
  corporateSovereigntyNormativeProposal : PhilosophicalSourceRole
  pluralAnarchistPropertyPositions : PhilosophicalSourceRole
  onlineFatalismDescription : PhilosophicalSourceRole
  criticalFeministPoliticalTheory : PhilosophicalSourceRole
  signValueSimulationTheory : PhilosophicalSourceRole

record PhilosophicalSourceReceipt : Set where
  constructor philosophical-source-receipt
  field
    originalAuthor : String
    datedOriginalWork : String
    locator : String
    role : PhilosophicalSourceRole
    boundedInterpretation : String
    noFormalTheoremImport : Bool
open PhilosophicalSourceReceipt public

marxEngelsPrimary : PhilosophicalSourceReceipt
marxEngelsPrimary = philosophical-source-receipt
  "Karl Marx; Friedrich Engels"
  "Manifesto of the Communist Party, Part II; 1848"
  "https://www.marxists.org/archive/marx/works/1848/communist-manifesto/ch02.htm"
  politicalTransitionProposal
  "graduated income tax and abolition of inheritance are context-bound proposed transitional measures, not observed policy effects"
  true

fraserCarePrimary : PhilosophicalSourceReceipt
fraserCarePrimary = philosophical-source-receipt
  "Nancy Fraser"
  "Contradictions of Capital and Care; New Left Review 100 (2016)"
  "https://newleftreview.org/issues/ii100/articles/nancy-fraser-contradictions-of-capital-and-care"
  criticalSocialReproductionTheory
  "care and social reproduction are conditions of economic life in Fraser's theory; no optimal tax rate is deduced"
  true

federiciHouseworkPrimary : PhilosophicalSourceReceipt
federiciHouseworkPrimary = philosophical-source-receipt
  "Silvia Federici"
  "Wages against Housework; first edition April 1975"
  "https://books.google.com/books?id=6hzVAAAAIAAJ"
  feministLabourPoliticalArgument
  "original work on unwaged housework and the political perspective of wages for housework; not evidence for a universal billionaire tax rate"
  true

arnsteinParticipationPrimary : PhilosophicalSourceReceipt
arnsteinParticipationPrimary = philosophical-source-receipt
  "Sherry R. Arnstein"
  "A Ladder of Citizen Participation; JAIP 35(4), 1969"
  "https://doi.org/10.1080/01944366908977225"
  participationPowerTypology
  "consultation/inclusion and actual decision power differ; typology is not a universal voting-rights theorem"
  true

collinsStandpointPrimary : PhilosophicalSourceReceipt
collinsStandpointPrimary = philosophical-source-receipt
  "Patricia Hill Collins"
  "Learning from the Outsider Within; Social Problems 33(6), 1986"
  "https://doi.org/10.2307/800672"
  situatedStandpointTheory
  "original sociological claim for outsider-within positionality and knowledge; not a rule that social location itself certifies truth"
  true

------------------------------------------------------------------------
-- PHILOSOPHY / SOCIOLOGY SOURCE-ORIGINAL SEPARATION
-- The following source texts are competing interpretations, not reusable
-- empirical causal identifications or universal tax/AI prescriptions.
------------------------------------------------------------------------

bellHooks2000 : PhilosophicalSourceReceipt
bellHooks2000 = philosophical-source-receipt
  "bell hooks (Gloria Jean Watkins)"
  "Feminism Is for Everybody: Passionate Politics; South End Press 2000"
  "https://www.plutobooks.com/product/feminism-is-for-everybody/"
  criticalFeministPoliticalTheory
  "original critique of sexism, class, race, feminism and social institutions; not a mathematical demonstration of an optimal billionaire tax"
  true

baudrillard1981 : PhilosophicalSourceReceipt
baudrillard1981 = philosophical-source-receipt
  "Jean Baudrillard"
  "Simulacres et simulation; Editions Galilee, Paris, 1981"
  "https://catalogue.bnf.fr/ark:/12148/cb34681600h"
  signValueSimulationTheory
  "original philosophical treatment of simulacra/simulation; does not imply share ownership, accounting assets or public institutions are legally imaginary"
  true

kropotkin1892 : PhilosophicalSourceReceipt
kropotkin1892 = philosophical-source-receipt
  "Peter Kropotkin"
  "The Conquest of Bread; French La Conquete du pain 1892"
  "https://www.marxists.org/reference/archive/kropotkin-peter/1892/bread.htm"
  pluralAnarchistPropertyPositions
  "original anarchist-communist case for social possession of production and provision of housing, bread and basic needs; it is not an enacted 2026 tax system"
  true

lyotard1979 : PhilosophicalSourceReceipt
lyotard1979 = philosophical-source-receipt
  "Jean-Francois Lyotard"
  "La Condition postmoderne: Rapport sur le savoir (1979)"
  "https://plato.stanford.edu/entries/lyotard/"
  criticalNarrativeLegitimation
  "critique of universal metanarrative/knowledge legitimation; SEP provides historical bibliographic and interpretive context; it does not deny the material existence of shares"
  true

williamsSrnicek2013 : PhilosophicalSourceReceipt
williamsSrnicek2013 = philosophical-source-receipt
  "Alex Williams; Nick Srnicek"
  "A #ACCELERATE MANIFESTO for an Accelerationist Politics (14 May 2013)"
  "https://criticallegalthinking.com/2013/05/14/accelerate-manifesto-for-an-accelerationist-politics/"
  leftAccelerationistInstitutionalProposal
  "explicit left accelerationist strategy against austerity and for transforming technological and institutional capacity; not Nick Land's doctrine"
  true

landMeltdown1994 : PhilosophicalSourceReceipt
landMeltdown1994 = philosophical-source-receipt
  "Nick Land"
  "Meltdown, delivered Warwick Virtual Futures May 1994; first published Abstract Culture/CCRU 1997"
  "https://ccru.pw/posts/essays/"
  rightAccelerationistTechnocapitalInterpretation
  "speculative technocapital and runaway-process narrative; distinguish original reading, later edits, and any predictive tests"
  true

effectiveAccelerationism2022 : PhilosophicalSourceReceipt
effectiveAccelerationism2022 = philosophical-source-receipt
  "BasedBeffJezos; bayeslord; earlier co-credit zestular and creatine_cycle"
  "Notes on e/acc principles and tenets, 2022; repost dated 31 October 2022"
  "https://effectiveaccelerationism.substack.com/p/repost-notes-on-eacc-principles-and"
  effectiveAccelerationismMovementText
  "optimistic energy/market/technology acceleration; pseudonymous source lineage, not same-object equivalence with Land or a legislative tax proposal"
  true

varoufakis2023 : PhilosophicalSourceReceipt
varoufakis2023 = philosophical-source-receipt
  "Yanis Varoufakis"
  "Technofeudalism: What Killed Capitalism (2023), author-hosted preface 7 September 2023"
  "https://www.yanisvaroufakis.eu/2023/09/07/technofeudalism-has-just-arrived/"
  platformCloudRentCriticalTheory
  "hypothesis concerning cloud capital, cloud rent and corporate platform sovereignty; no measured conclusion for every platform"
  true

yarvinPatchwork2008 : PhilosophicalSourceReceipt
yarvinPatchwork2008 = philosophical-source-receipt
  "Curtis Yarvin (published as Mencius Moldbug)"
  "Patchwork: a positive vision, Part 1, 13 November 2008"
  "https://www.unqualified-reservations.org/2008/11/patchwork-positive-vision-part-1/"
  corporateSovereigntyNormativeProposal
  "original pro-corporate sovereign realms proposal explicitly mentions self-assessed property taxes; NOT a universal no-tax claim; objectionable statements are authored positions, not prescriptions here"
  true

stanfordAnarchism : PhilosophicalSourceReceipt
stanfordAnarchism = philosophical-source-receipt
  "Andrew Fiala; Stanford Encyclopedia of Philosophy"
  "Anarchism, original 2017; substantive revision 4 December 2025"
  "https://plato.stanford.edu/entries/anarchism/"
  pluralAnarchistPropertyPositions
  "secondary scholarly taxonomy differentiating socialist/communist, individualist, market and philosophical anarchisms; not every participant holds the same property or fiscal stance"
  true

-- Broad internet labels are tracked as the USER'S inquiry, not as an
-- original school with one identified canonical author or tax conclusion.
data InternetFatalismSourceProvesGlobalInevitability : Set where
data PostmodernNarrativeCritiqueProvesAssetValueZero : Set where
data AllAnarchistsChooseOneTaxProgramme : Set where
data AccelerationismsHaveIdenticalPolitics : Set where
data HistoricalParetoFrequencyImposesMoralRule : Set where
data CorporateSovereigntyIsDemocraticRepresentation : Set where

fatalismDoesNotProveWorldTrajectory :
  InternetFatalismSourceProvesGlobalInevitability → ⊥
fatalismDoesNotProveWorldTrajectory ()

postmodernismDoesNotDeleteAssets :
  PostmodernNarrativeCritiqueProvesAssetValueZero → ⊥
postmodernismDoesNotDeleteAssets ()

anarchismIsNotOneProgramme :
  AllAnarchistsChooseOneTaxProgramme → ⊥
anarchismIsNotOneProgramme ()

accelerationismsNeedSeparateAuthors :
  AccelerationismsHaveIdenticalPolitics → ⊥
accelerationismsNeedSeparateAuthors ()

paretoLawCannotAuthoriseOligarchy :
  HistoricalParetoFrequencyImposesMoralRule → ⊥
paretoLawCannotAuthoriseOligarchy ()

corporateSovereigntyIsNotAutomaticallyRepresentation :
  CorporateSovereigntyIsDemocraticRepresentation → ⊥
corporateSovereigntyIsNotAutomaticallyRepresentation ()

------------------------------------------------------------------------
-- REUSE / NON-PROMOTION BOUNDARIES FROM PHILOSOPHY + SOCIAL THEORY.
------------------------------------------------------------------------

noAutomaticPoliticalAuthority :
  Philosophy.noPoliticalAuthority
    Philosophy.canonicalPhilosophyNonClaimBoundary ≡ true
noAutomaticPoliticalAuthority = refl

taxInterventionDoesNotProveSystemicClosure :
  Feedback.removingOneOutputProvesSystemicClosure
    Feedback.canonicalInterventionBoundary ≡ false
taxInterventionDoesNotProveSystemicClosure = refl

noMachineSovereigntyFromAccelerationMetaphor :
  Decentring.impersonalSystemsReceiveMoralSovereignty
    Decentring.canonicalDecentringForkBoundary ≡ false
noMachineSovereigntyFromAccelerationMetaphor = refl

singleClassCannotFixIdeology :
  INF.FactorsThrough
    Totality.economicObserver Totality.ideologicalPosition → ⊥
singleClassCannotFixIdeology =
  Totality.economyCannotRecoverCompleteIdeology

recognitionAloneCannotDetermineRedistribution :
  INF.FactorsThrough Fraser.recognition Fraser.distribution → ⊥
recognitionAloneCannotDetermineRedistribution =
  Fraser.recognitionCannotRecoverDistribution

-- Reuse the entire canonical boundary record rather than re-exporting its
-- fields. The source module does not globally open its record projections.
comparativeInstitutionalBoundary :
  Institutional.ComparativeInstitutionalMeaningBoundary
comparativeInstitutionalBoundary =
  Institutional.canonicalComparativeInstitutionalMeaningBoundary

sociologyIsIndexedNotInvented :
  Funnel.SocialScienceChild
sociologyIsIndexedNotInvented = Funnel.sociology

------------------------------------------------------------------------
-- BIDI CLAIM AUTHORITY. Tax numbers cannot certify social or political
-- consequences; conversely political theory does not make tax unnecessary.
------------------------------------------------------------------------

data FiniteTaxCounterexampleProvesCausalOutcome : Set where
data SocialTheoryDictatesOneTaxRate : Set where
data ActualWealthDistributionIsFullyMeasuredHere : Set where

finiteWitnessDoesNotCertifyRealWorldCausation :
  FiniteTaxCounterexampleProvesCausalOutcome → ⊥
finiteWitnessDoesNotCertifyRealWorldCausation ()

socialTheoryDoesNotDictateOneTaxRate :
  SocialTheoryDictatesOneTaxRate → ⊥
socialTheoryDoesNotDictateOneTaxRate ()

syntheticSnapshotsAreNotEmpiricalReceipts :
  ActualWealthDistributionIsFullyMeasuredHere → ⊥
syntheticSnapshotsAreNotEmpiricalReceipts ()
