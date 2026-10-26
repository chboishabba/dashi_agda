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
