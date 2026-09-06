module DASHI.Law.GenocideFascismSourceGenealogyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.FascismAtrocitySourceCrossPollinationExact as Fascism
import DASHI.Law.GazaGenocideHerzogZionismSourceReceiptsExact as Gaza

------------------------------------------------------------------------
-- Source genealogy for the genocide <-> fascism relation.
--
-- This replaces a merely conversation-attributed stance with a separately
-- sourced intellectual genealogy plus an explicit DASHI synthesis.
------------------------------------------------------------------------

data GenealogySourceRole : Set where
  historicalLegalTheory
  peerReviewedHistoricalScholarship
  holocaustMuseumSynthesis
  comparativeFascismScholarship
  unCommissionFinding
  dashiSynthesis : GenealogySourceRole

data GenealogyProposition : Set where
  genocideIsFascismInActionHistoricalFormulation
  fascismUsesPurifyingRedemptiveViolence
  naziFascismProducedEliminationistGenocide
  fascismGenocideRelationIsComparativelyDebated
  israelGenocideFinding
  genocideInstantiatesFascisticTerminalisation : GenealogyProposition

record GenealogyReceipt : Set where
  constructor genealogyReceipt
  field
    proposition : GenealogyProposition
    role : GenealogySourceRole
    sourceReference : String
    boundedDescription : String

open GenealogyReceipt public

traininPennReceipt : GenealogyReceipt
traininPennReceipt = genealogyReceipt
  genocideIsFascismInActionHistoricalFormulation
  peerReviewedHistoricalScholarship
  "Michelle Penn, ‘Genocide is Fascism in Action’: Aron Trainin and Soviet Portrayals of Genocide, Journal of Genocide Research 22(1), 2020"
  "Penn documents the historical Trainin/Soviet formulation linking genocide and fascism; this is intellectual genealogy, not a universal definitional consensus"

ushmmFascismViolenceReceipt : GenealogyReceipt
ushmmFascismViolenceReceipt = genealogyReceipt
  fascismUsesPurifyingRedemptiveViolence
  holocaustMuseumSynthesis
  "United States Holocaust Memorial Museum, Fascism encyclopedia article"
  "USHMM describes fascism as exclusionary ultranationalism that accepts or celebrates political violence and redemptive/purifying violence against perceived enemies"

ushmmNaziEliminationReceipt : GenealogyReceipt
ushmmNaziEliminationReceipt = genealogyReceipt
  naziFascismProducedEliminationistGenocide
  holocaustMuseumSynthesis
  "United States Holocaust Memorial Museum, Nazi racial ideology / Holocaust encyclopedia materials"
  "USHMM links Nazi racial ideology, elimination of perceived racial threats, war and genocide within the Nazi fascist regime"

comparativeDebateReceipt : GenealogyReceipt
comparativeDebateReceipt = genealogyReceipt
  fascismGenocideRelationIsComparativelyDebated
  comparativeFascismScholarship
  "Journal of Holocaust Research, Fascism, Extremism, and Extermination: introductory comparative discussion"
  "Comparative scholarship treats the exact relation between fascism and extermination/genocide as a substantive scholarly question; the strongest relation should therefore be stated with its analytical scope"

gazaGenocideReceipt : GenealogyReceipt
gazaGenocideReceipt = genealogyReceipt
  israelGenocideFinding
  unCommissionFinding
  "UN Independent International Commission of Inquiry on the Occupied Palestinian Territory, September 2025 genocide finding; June 2026 continuation"
  "UN-mandated Commission finding supplies the genocide proposition; it is not re-authored as the source of the fascism classification"

------------------------------------------------------------------------
-- DASHI synthesis: once genocide is established, genocidal elimination is
-- classified as a fascistic terminalisation mechanism.  The synthesis has
-- external genealogy, but DASHI remains author of this exact formal rule.
------------------------------------------------------------------------

data MechanismClassification : Set where
  fascisticTerminalisationMechanism : MechanismClassification

genocideMechanismClassification : MechanismClassification
genocideMechanismClassification = fascisticTerminalisationMechanism

genocideToFascisticTerminalisation :
  genocideMechanismClassification ≡ fascisticTerminalisationMechanism
genocideToFascisticTerminalisation = refl

genocideFeature : Fascism.FascismFeature
genocideFeature = Fascism.terminalisation

collectiveTargetingFeature : Fascism.FascismFeature
collectiveTargetingFeature = Fascism.collectiveGuiltTransport

genocideFascismSynthesisReceipt : GenealogyReceipt
genocideFascismSynthesisReceipt = genealogyReceipt
  genocideInstantiatesFascisticTerminalisation
  dashiSynthesis
  "DASHI synthesis using Trainin/Penn genealogy, USHMM fascism/elimination evidence and comparative-fascism boundary"
  "An established genocidal-elimination mechanism is classified as fascistic terminalisation; this does not misattribute the political label to the UN Commission or make every adjacent institution automatically fascist"

------------------------------------------------------------------------
-- Attribution boundary.
------------------------------------------------------------------------

record GenocideFascismGenealogyBoundary : Set where
  constructor genocideFascismGenealogyBoundary
  field
    traininFormulationIsUniversalConsensus : Bool
    traininFormulationIsUniversalConsensusIsFalse : traininFormulationIsUniversalConsensus ≡ false
    unCommissionGenocideFindingIsUNFascismFinding : Bool
    unCommissionGenocideFindingIsUNFascismFindingIsFalse : unCommissionGenocideFindingIsUNFascismFinding ≡ false
    naziCaseAloneProvesEveryGenocideHasIdenticalHistoricalFascism : Bool
    naziCaseAloneProvesEveryGenocideHasIdenticalHistoricalFascismIsFalse : naziCaseAloneProvesEveryGenocideHasIdenticalHistoricalFascism ≡ false
    sourcedGenealogySupportsDASHISynthesis : Bool
    sourcedGenealogySupportsDASHISynthesisIsTrue : sourcedGenealogySupportsDASHISynthesis ≡ true
    genocideMechanismClassificationAutomaticallyClassifiesEveryInstitution : Bool
    genocideMechanismClassificationAutomaticallyClassifiesEveryInstitutionIsFalse : genocideMechanismClassificationAutomaticallyClassifiesEveryInstitution ≡ false

canonicalGenocideFascismGenealogyBoundary : GenocideFascismGenealogyBoundary
canonicalGenocideFascismGenealogyBoundary =
  genocideFascismGenealogyBoundary false refl false refl false refl true refl false refl
