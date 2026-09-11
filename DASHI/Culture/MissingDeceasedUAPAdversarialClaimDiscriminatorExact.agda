module DASHI.Culture.MissingDeceasedUAPAdversarialClaimDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Culture.AmyEskridgeAntigravityObservationBidiCrossPollinationExact as AmyAnti
import DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact as Reza
import DASHI.Physics.Materials.RezaFangAlloyMetamaterialDiscriminationExact as MaterialDisc
import DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyBidiExact as Maiwald
import DASHI.Physics.Materials.FangDainingActiveMechanicalMetamaterialBidiExact as Fang
import DASHI.Culture.MissingDeceasedStrategicRoleCapabilityFibreExact as Role
import DASHI.Culture.MissingDeceasedTernaryAdversarialObserverExact as Observer

------------------------------------------------------------------------
-- UAP / AREA-51 ADVERSARIAL CLAIM DISCRIMINATOR
--
-- Speculative narratives are retained as hypotheses with explicit paid kernels,
-- missing bridges, counter-readings and discriminating acquisitions.  Existing
-- physics/material/science owners remain authoritative for their domains.
------------------------------------------------------------------------

data SpeculativeClaimClass : Set where
  zeroPointSuppression
  mondaloyS4Metamaterial
  maiwaldNhiSampleAnalysis
  personnelCleanup
  breakawayRelocation
  reactiveInquiryCoverStory : SpeculativeClaimClass

record ClaimDiscriminator : Set where
  constructor claim-discriminator
  field
    claimClass : SpeculativeClaimClass
    speculativeClaim : String
    paidScientificKernel : String
    existingOwnerReference : String
    missingCausalBridge : String
    adversarialPrediction : String
    ordinaryOrControlPrediction : String
    discriminatingAcquisition : String
    currentBridgePaid : Bool
    sourceRepetitionPaysBridge : Bool
    strategicPlausibilityEqualsEvidence : Bool

open ClaimDiscriminator public

zeroPointSuppressionDiscriminator : ClaimDiscriminator
zeroPointSuppressionDiscriminator = claim-discriminator
  zeroPointSuppression
  "operational vacuum/zero-point antigravity exists and civilian replication was intentionally suppressed"
  "DASHI already types vacuum-regime antigravity requests, vacuum-persistent-thrust observables and Amy-associated coherent-superconductor/inertial/metric reverse-search lanes"
  "AntigravityMaterialBidiCrossPollinationExact + AmyEskridgeAntigravityObservationBidiCrossPollinationExact"
  "primary source establishing zero-point-energy extraction as the claimed mechanism; exact operational apparatus receipt; causal suppression action tied to the cohort"
  "pre-public programme records, security actions, access restrictions or personnel tasking should precede and target the same technical object"
  "vacuum/thrust/gravity research can exist as ordinary experimental science without operational zero-point extraction or coordinated suppression"
  "acquire mechanism-specific source, apparatus record, replication history and dated security/personnel action; do not infer from the coarse word antigravity"
  false false false

mondaloyMetamaterialDiscriminator : ClaimDiscriminator
mondaloyMetamaterialDiscriminator = claim-discriminator
  mondaloyS4Metamaterial
  "Mondaloy is a public spin-off of reverse-engineered metamaterial work associated with S4/Area 51"
  "Reza/Jacinto burn-resistant nickel-alloy design is formalised; Fang Daining pays an independent published active-mechanical-metamaterial class; the new discrimination owner proves that alloy performance alone does not classify the Reza object as a metamaterial"
  "RezaBurnResistantAlloyBidiExact + FangDainingActiveMechanicalMetamaterialBidiExact + RezaFangAlloyMetamaterialDiscriminationExact"
  "for the same Reza/Mondaloy object: an architecture-based metamaterial classification receipt, architecture-derived effective-property receipt, and same-object provenance chain to a classified reverse-engineering programme or S4 predecessor"
  "classified programme records should contain the same alloy/material object, architecture or composition/process lineage, custody chain or predecessor artifact before public patenting"
  "advanced composition/process alloys and structured mechanical metamaterials are both established terrestrial engineering classes and must not be merged by the word 'advanced'"
  "trace patent assignment, precursor compositions, architecture/effective-property evidence, funding/contract lineage, process notebooks and exact programme/material provenance"
  false false false

maiwaldNhiDiscriminator : ClaimDiscriminator
maiwaldNhiDiscriminator = claim-discriminator
  maiwaldNhiSampleAnalysis
  "Maiwald action spectroscopy was deployed to identify residues or biological material associated with alleged NHI/craft retrieval"
  "messenger photodissociation action spectroscopy and QIT biosignature/isomer discrimination are formalised from public JPL/CU science"
  "MaiwaldActionSpectroscopyBidiExact"
  "deployment/custody record for terrestrial classified samples plus same-instrument or same-method identity and NHI/craft-retrieval provenance"
  "secure-facility deployment, classified sample manifests, funding/work-package lineage or access records should intersect the same apparatus/team"
  "the same spectroscopy capability has ordinary terrestrial chemistry and planetary-science applications without classified NHI use"
  "acquire instrument deployment logs, sample manifests, funding/work-package lineage, lab notebooks/data custody and collaborator programme history"
  false false false

personnelCleanupDiscriminator : ClaimDiscriminator
personnelCleanupDiscriminator = claim-discriminator
  personnelCleanup
  "a coordinated operation targeted not only scientists but managers, administrators, custodians and technicians with programme knowledge"
  "role-capability fibres make technical knowledge, access, routing, inventory visibility, coordination and clearance independent of occupational label"
  "MissingDeceasedStrategicRoleCapabilityFibreExact"
  "common programme/object plus dated capability and common operational action across otherwise heterogeneous roles"
  "targets should share programme topology, access/custody coordinates or pre-event tasking more strongly than matched controls"
  "large laboratories naturally contain many role classes; role diversity alone does not identify a common programme or operation"
  "recover dated duty/access/custody objects and matched controls for comparable staff who were not selected into the media roster"
  false false false

houseCoverStoryDiscriminator : ClaimDiscriminator
houseCoverStoryDiscriminator = claim-discriminator
  reactiveInquiryCoverStory
  "the public investigation is reactive cover/distraction after a prior coordinated operation against the cohort"
  "a congressional inquiry and agency information requests are real public events"
  "HouseOversightScientistRosterScopeExact + MissingDeceasedTernaryAdversarialObserverExact"
  "evidence of cross-case government tasking, records access, personnel action or common identifiers predating public/media convergence"
  "internal linkage or tasking should be observable before the public inquiry if the inquiry is downstream cover rather than first-stage reaction"
  "public officials can react to viral reporting and constituent/media pressure without possessing a prior common-cause operation"
  "build event-time chronology of first media aggregation, first agency cross-case linkage, FOIA/classification actions, internal tasking and congressional requests"
  false false false

------------------------------------------------------------------------
-- Named firewalls requested by the focused validation contract.
------------------------------------------------------------------------

zeroPointSuppressionIsNotVacuumThrust : Bool
zeroPointSuppressionIsNotVacuumThrust = true

mondaloyToMetamaterialBridgeUnpaid : Bool
mondaloyToMetamaterialBridgeUnpaid = true

houseInquiryDoesNotPayCommonCause : Bool
houseInquiryDoesNotPayCommonCause = true

existingAntigravityBoundary : Anti.AntigravityPromotionBoundary
existingAntigravityBoundary = Anti.canonicalAntigravityPromotionBoundary

existingFangMetamaterialBoundary : Fang.FangMetamaterialBoundary
existingFangMetamaterialBoundary = Fang.canonicalFangMetamaterialBoundary

existingAlloyMetamaterialBoundary : MaterialDisc.AlloyMetamaterialDiscriminationBoundary
existingAlloyMetamaterialBoundary = MaterialDisc.canonicalAlloyMetamaterialDiscriminationBoundary

existingRoleCapabilityBoundary : Role.RoleCapabilityBoundary
existingRoleCapabilityBoundary = Role.canonicalRoleCapabilityBoundary

existingObserverBoundary : Observer.TernaryObserverBoundary
existingObserverBoundary = Observer.canonicalTernaryObserverBoundary

record UAPDiscriminatorBoundary : Set where
  constructor uap-discriminator-boundary
  field
    paidKernelPaysSpeculativeBridge : Bool
    absenceOfPublicRecordProvesSuppression : Bool
    adversarialHypothesisMayNominateSearch : Bool
    adversarialHypothesisMaySelfSealAgainstCounterEvidence : Bool
    primarySameObjectReceiptRequiredForPromotion : Bool

canonicalUAPDiscriminatorBoundary : UAPDiscriminatorBoundary
canonicalUAPDiscriminatorBoundary = uap-discriminator-boundary
  false false true false true
