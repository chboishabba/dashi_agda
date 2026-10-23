module DASHI.Cognition.AquinoMaxwellEpsteinCAMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact as CA
import DASHI.Cognition.EpsteinMasterPlanAttributionBoundaryExact as Plan
import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy

------------------------------------------------------------------------
-- AQUINO / MAXWELL / EPSTEIN / CA: EXISTING-CARRIER ATTRIBUTION MAX-CUT
--
-- Historical claims are about what a bounded source establishes. A court
-- decision, sworn testimony, a self-authored proposal, an agency statement
-- and an investigative allegation are different evidentiary acts. They do
-- not vote as independent witnesses just because documents repeat them.
--
-- This is a typed provenance/claim-promotion boundary, NOT a proof of
-- events in the external world or of the absence of unknown records.
-- The case reuses the existing CA and MasterPlan owners.
------------------------------------------------------------------------

data Person : Set where
  robertMaxwell : Person
  robertMercer : Person
  ghislaineMaxwell : Person
  jeffreyEpstein : Person
  michaelAquino : Person
  paulVallely : Person
  steveBannon : Person

robertMaxwellIsNotRobertMercer : robertMaxwell ≡ robertMercer → ⊥
robertMaxwellIsNotRobertMercer ()

data ResearchProgramme : Set where
  mindWarProposal : ResearchProgramme
  projectStargate : ResearchProgramme

mindWarIsNotStargate : mindWarProposal ≡ projectStargate → ⊥
mindWarIsNotStargate ()

data SourceRole : Set where
  contemporaryCorporateRecord : SourceRole
  attributedFirstPersonTestimony : SourceRole
  attributedAuthorProposal : SourceRole
  retrospectiveSelfAccount : SourceRole
  regulatoryFinding : SourceRole
  judicialProceduralDecision : SourceRole
  congressionalFinding : SourceRole
  disputedAgencyReview : SourceRole
  releasedCorrespondence : SourceRole
  crossSourceHypothesis : SourceRole

-- Source roots represent original authors or record-producing bodies.
-- Reposting a witness statement does not create another witness.
data OriginRoot : Set where
  wylieRoot : OriginRoot
  aquinoVallelyRoot : OriginRoot
  fourthCircuitRoot : OriginRoot
  ftcRoot : OriginRoot
  houseJudiciaryRoot : OriginRoot
  buaDOJRoot : OriginRoot
  dojFBIMemoRoot : OriginRoot
  epsteinCorrespondenceRoot : OriginRoot

data CaseClaim : Set where
  sclCAOperatingContinuity : CaseClaim
  mindWarAuthored : CaseClaim
  presidioAdministrativeDisposition : CaseClaim
  deceptiveFacebookCollection : CaseClaim
  inslawCongressionalFinding : CaseClaim
  inslawSpecialCounselCounterFinding : CaseClaim
  dojFBI2025ReviewPosition : CaseClaim
  bannonEpsteinMediaContact : CaseClaim

record BoundedSource : Set where
  constructor bounded-source
  field
    proposition : CaseClaim
    root : OriginRoot
    role : SourceRole
    locator : String
    sourceDate : String
    describedEventPeriod : String
    boundedFinding : String
    sourceStatementLocated : Bool
    specificOperationalTransferPaid : Bool
    unifiedIntelligenceCommandPaid : Bool
    criminalConductOfNamedUnchargedPersonsPaid : Bool
open BoundedSource public

canonicalSources : List BoundedSource
canonicalSources =
  bounded-source sclCAOperatingContinuity wylieRoot
    attributedFirstPersonTestimony
    "https://committees.parliament.uk/writtenevidence/89475/html/"
    "2018" "2013-2014"
    "Christopher Wylie testified to SCL/CA corporate and technique continuity and Mercer's/Bannon's roles. This is attributed testimony, not proof that Aquino's particular 1980 paper was adopted."
    true false false false
  ∷ bounded-source mindWarAuthored aquinoVallelyRoot
    attributedAuthorProposal
    "From PSYOP to MindWar, Paul E. Vallely / Michael A. Aquino, 1980; 2003 Aquino annotations"
    "1980 (2003 author retrospective is SAME origin)" "1980"
    "The named authors produced a discussion proposal. Aquino's later account is not an independent witness or a source of an executed command."
    true false false false
  ∷ bounded-source presidioAdministrativeDisposition fourthCircuitRoot
    judicialProceduralDecision
    "https://law.justia.com/cases/federal/appellate-courts/F2/957/139/2044/"
    "1992-02-26" "1986-1990"
    "Aquino v Stone affirmed refusal to alter CID records; the appellate holding is administrative, not a finding of criminal guilt. San Francisco police had ended their investigation for insufficient evidence."
    true false false false
  ∷ bounded-source deceptiveFacebookCollection ftcRoot
    regulatoryFinding
    "https://www.ftc.gov/legal-library/browse/cases-proceedings/182-3107-cambridge-analytica-llc-matter"
    "2019-12" "2014 onward"
    "FTC found Cambridge Analytica used deceptive collection of Facebook personal data; this does not establish election causation or a specific Aquino-to-SCL transfer."
    true false false false
  ∷ bounded-source inslawCongressionalFinding houseJudiciaryRoot
    congressionalFinding
    "House Judiciary Committee, The INSLAW Affair, H. Rept. 102-857 (1992)"
    "1992" "1980s-1992"
    "House investigators criticised DOJ conduct in the PROMIS dispute. Alleged Robert Maxwell intelligence distribution is a separate claim, not paid by this congressional finding."
    true false false false
  ∷ bounded-source inslawSpecialCounselCounterFinding buaDOJRoot
    disputedAgencyReview
    "Nicholas Bua, Report of Special Counsel Regarding INSLAW, 1993"
    "1993" "1980s-1993"
    "A separate DOJ-commissioned investigation contested significant INSLAW allegations. Distinct institutional author root; neither its findings nor House findings alone establish the Maxwell backdoor claim."
    true false false false
  ∷ bounded-source dojFBI2025ReviewPosition dojFBIMemoRoot
    disputedAgencyReview
    "https://www.justice.gov/opa/media/1407001/dl"
    "2025-07" "Epstein investigative holdings through 2025"
    "DOJ/FBI said its review found no credible evidence Epstein blackmailed prominent individuals. This is an attributed agency conclusion, not a proof that blackmail was logically impossible."
    true false false false
  ∷ bounded-source bannonEpsteinMediaContact epsteinCorrespondenceRoot
    releasedCorrespondence
    "DOJ-released Bannon/Epstein communications; canonical prior owner TrumpMarALagoBannonBridgeExact"
    "released 2025-2026" "2018-2019"
    "Direct correspondence documents media/political collaboration; neither personnel overlap with Cambridge Analytica nor a shared influence vocabulary pays transfer of its software or techniques."
    true false false false
  ∷ []

-- Case-specific negative closure is a current-source-state statement.
-- It does not assert that no additional witness or document can ever exist.
record CrossNetworkBoundary : Set where
  constructor cross-network-boundary
  field
    sclToCACorporateContinuityPaid : Bool
    caDeceptiveCollectionFindingPaid : Bool
    bannonEpsteinCorrespondencePaid : Bool
    aquinoAuthoredMindWarPaid : Bool
    aquinoDirectEpsteinWorkPaid : Bool
    aquinoDirectMaxwellWorkPaid : Bool
    aquinoSpecificTechniqueTransferredToSCLPaid : Bool
    aquinoProjectStargateOperationalIdentityPaid : Bool
    promisBackdoorMaxwellDistributionPaid : Bool
    epsteinIntelligenceBlackmailTaskingPaid : Bool
    unifiedSponsorAndHierarchyPaid : Bool
open CrossNetworkBoundary public

canonicalBoundary : CrossNetworkBoundary
canonicalBoundary = cross-network-boundary
  true true true true false false false false false false false

aquinoToSCLUnpaid :
  aquinoSpecificTechniqueTransferredToSCLPaid canonicalBoundary ≡ false
aquinoToSCLUnpaid = refl

aquinoToEpsteinUnpaid : aquinoDirectEpsteinWorkPaid canonicalBoundary ≡ false
aquinoToEpsteinUnpaid = refl

promisMaxwellUnpaid : promisBackdoorMaxwellDistributionPaid canonicalBoundary ≡ false
promisMaxwellUnpaid = refl

unifiedHierarchyUnpaid : unifiedSponsorAndHierarchyPaid canonicalBoundary ≡ false
unifiedHierarchyUnpaid = refl

existingCAMediaReuseUnpaid :
  CA.laterEpsteinMediaWorkProvesTechniqueReuse
    CA.canonicalBannonInfluenceInfrastructureBoundary ≡ false
existingCAMediaReuseUnpaid = refl

existingMasterPlanHierarchyUnpaid :
  Plan.unifiedCommandHierarchyPaid Plan.canonicalMasterPlanCoordinates ≡ false
existingMasterPlanHierarchyUnpaid = refl

existingGenealogyDoesNotPromoteAnalogy :
  Genealogy.historicalContinuityEqualsCentralCommand
    Genealogy.canonicalEvidenceGradedGenealogyBoundary ≡ false
existingGenealogyDoesNotPromoteAnalogy = refl

-- These token types are deliberately uninhabited. Their rejection is a
-- type-level API constraint, not an empirical proof of nonparticipation.
data SourceRepetitionImpliesIndependentCorroboration : Set where
data CommonMethodImpliesDirectTransfer : Set where
data AllegationImpliesAdjudicatedConduct : Set where
data NetworkPathImpliesUnifiedCommand : Set where

noWitnessMultiplication :
  SourceRepetitionImpliesIndependentCorroboration → ⊥
noWitnessMultiplication ()

noTechniquePromotion : CommonMethodImpliesDirectTransfer → ⊥
noTechniquePromotion ()

noGuiltByAllegation : AllegationImpliesAdjudicatedConduct → ⊥
noGuiltByAllegation ()

noUnifiedCommandFromNetworkPath : NetworkPathImpliesUnifiedCommand → ⊥
noUnifiedCommandFromNetworkPath ()
