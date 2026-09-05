module DASHI.Culture.MissingDeceasedCriticalKnowledgeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CriticalKnowledgeConcentrationBidiExact as K

------------------------------------------------------------------------
-- PRIORITY-ROSTER CRITICAL KNOWLEDGE PROFILES
--
-- These are evidence-gathering fixtures.  They do not assert targeting or
-- perpetration.  Unsupported coordinates remain explicit notLocated targets.
------------------------------------------------------------------------

loureiroProfile : K.CriticalKnowledgeProfile
loureiroProfile = K.critical-knowledge-profile
  "Nuno F. G. Loureiro"
  (K.knowledge-coordinate-receipt
      "Nuno F. G. Loureiro" K.publicKnowledge K.coordinateSourceBacked
      "MIT Physics / PSFC profile; Viriato DOI 10.1016/j.cpc.2016.05.004"
      "Magnetic reconnection, plasma turbulence, and fusion confinement/transport are public/source-backed."
   ∷ K.knowledge-coordinate-receipt
      "Nuno F. G. Loureiro" K.tacitImplementationKnowledge K.coordinateNotLocated
      "not located"
      "Deep expertise is plausible but a source proving unique tacit implementation knowledge has not been located."
   ∷ K.knowledge-coordinate-receipt
      "Nuno F. G. Loureiro" K.sensitiveOrRestrictedKnowledge K.coordinateNotLocated
      "not located"
      "No source-backed receipt currently establishes that Loureiro personally held restricted/classified information relevant to this hypothesis."
   ∷ [])
  (K.criticality-receipt
      "Nuno F. G. Loureiro" K.integrationBreadth K.coordinatePartial
      "MIT PSFC directorship and scientific profile"
      "Leadership plus cross-cutting fusion/plasma expertise supports breadth, not uniqueness."
   ∷ K.criticality-receipt
      "Nuno F. G. Loureiro" K.replacementDifficulty K.coordinatePartial
      "MIT installed Stephen Wukitch as interim PSFC director; programme continued"
      "Centre-level leadership was replaced; scientific/tacit replacement remains unresolved."
   ∷ K.criticality-receipt
      "Nuno F. G. Loureiro" K.strategicCapabilityRelevance K.coordinateSourceBacked
      "MIT Physics / PSFC"
      "Fusion confinement/transport and magnetic reconnection are directly relevant to fusion capability."
   ∷ [])
  "empirical ledger + MIT/PSFC source lineage"
  "Strong 'knew too much' claim remains unclosed because uniqueness, nonpublicness and person-specific replacement difficulty are not yet owned."

chavezProfile : K.CriticalKnowledgeProfile
chavezProfile = K.critical-knowledge-profile
  "Anthony Chavez"
  (K.knowledge-coordinate-receipt
      "Anthony Chavez" K.tacitImplementationKnowledge K.coordinatePartial
      "LANL National Security Science, Summer 2025"
      ">25 years at DARHT and Scorpius design work support deep implementation exposure; uniqueness is unproved."
   ∷ K.knowledge-coordinate-receipt
      "Anthony Chavez" K.configurationSpecificKnowledge K.coordinatePartial
      "LANL Scorpius/DARHT role profile"
      "Design work on a large accelerator motivates configuration-specific knowledge acquisition."
   ∷ K.knowledge-coordinate-receipt
      "Anthony Chavez" K.failureModeKnowledge K.coordinateNotLocated
      "not located"
      "Long tenure does not itself prove ownership of unusual failure-mode knowledge."
   ∷ [])
  (K.criticality-receipt
      "Anthony Chavez" K.uniqueness K.coordinateNotLocated
      "not located"
      "Exact subsystem ownership and rarity of his responsibilities remain unknown."
   ∷ K.criticality-receipt
      "Anthony Chavez" K.replacementDifficulty K.coordinatePartial
      "Scorpius continued scheduled deliveries after disappearance"
      "No whole-programme paralysis; local responsibility-transfer difficulty remains unresolved."
   ∷ K.criticality-receipt
      "Anthony Chavez" K.strategicCapabilityRelevance K.coordinateSourceBacked
      "LANL/NNSA Scorpius and DARHT descriptions"
      "Accelerator radiography supports stockpile-stewardship capability."
   ∷ [])
  "LANL profile + Scorpius continuity evidence"
  "Criticality claim is live only at the local subsystem/tacit-knowledge level."

mccaslandProfile : K.CriticalKnowledgeProfile
mccaslandProfile = K.critical-knowledge-profile
  "William N. McCasland"
  (K.knowledge-coordinate-receipt
      "William N. McCasland" K.integrationKnowledge K.coordinateSourceBacked
      "U.S. Air Force biography; Applied Technology Associates / Hertz Foundation role descriptions"
      "Career spans GPS, Space Based Laser, AFRL Space Vehicles, AFRL command, and later technology strategy/IRAD."
   ∷ K.knowledge-coordinate-receipt
      "William N. McCasland" K.networkKnowledge K.coordinatePartial
      "official biography and private-sector technology-strategy role"
      "Breadth supports likely programme/network visibility, but specific nonpublic network knowledge is not independently established."
   ∷ K.knowledge-coordinate-receipt
      "William N. McCasland" K.sensitiveOrRestrictedKnowledge K.coordinateNotLocated
      "not located"
      "Historical special-program/acquisition roles do not by themselves prove event-time possession of particular restricted information."
   ∷ [])
  (K.criticality-receipt
      "William N. McCasland" K.integrationBreadth K.coordinateSourceBacked
      "USAF biography; ATA technology-strategy role"
      "Cross-programme systems and technology integration breadth is directly documented."
   ∷ K.criticality-receipt
      "William N. McCasland" K.replacementDifficulty K.coordinateNotLocated
      "not located"
      "Need successor/IRAD responsibility-transfer evidence at the 2026 event-time role."
   ∷ K.criticality-receipt
      "William N. McCasland" K.strategicCapabilityRelevance K.coordinateSourceBacked
      "USAF / AFRL role record"
      "Strategic space, acquisition and technology-development relevance is source-backed."
   ∷ [])
  "USAF + ATA/Hertz event-time role lineage"
  "Among current rows, integration breadth is strongest here; uniqueness/nonpublicness/replacement remain open."

leblancProfile : K.CriticalKnowledgeProfile
leblancProfile = K.critical-knowledge-profile
  "Joshua Kyle LeBlanc"
  (K.knowledge-coordinate-receipt
      "Joshua Kyle LeBlanc" K.publicKnowledge K.coordinateSourceBacked
      "NASA NTRS 20250008475"
      "Fission Surface Power I&C technology-development work and SNP I&C TechMat team leadership are public/source-backed."
   ∷ K.knowledge-coordinate-receipt
      "Joshua Kyle LeBlanc" K.configurationSpecificKnowledge K.coordinatePartial
      "NASA FSP/SNP I&C role"
      "I&C technology-maturation work motivates system-specific knowledge, but exact nonpublic configuration ownership is not established."
   ∷ K.knowledge-coordinate-receipt
      "Joshua Kyle LeBlanc" K.sensitiveOrRestrictedKnowledge K.coordinateNotLocated
      "not located"
      "No receipt currently establishes classified/restricted holdings."
   ∷ [])
  (K.criticality-receipt
      "Joshua Kyle LeBlanc" K.uniqueness K.coordinatePartial
      "NASA I&C executive structure"
      "LeBlanc held a specific TechMat lead role inside a multi-lead I&C structure, cutting against sole-owner narratives."
   ∷ K.criticality-receipt
      "Joshua Kyle LeBlanc" K.replacementDifficulty K.coordinateNotLocated
      "not located"
      "Need the post-July-2025 SNP I&C TechMat successor and responsibility-transfer record."
   ∷ K.criticality-receipt
      "Joshua Kyle LeBlanc" K.strategicCapabilityRelevance K.coordinateSourceBacked
      "NASA NTRS 20250008475"
      "Space fission power/propulsion I&C is source-backed."
   ∷ [])
  "NASA FSP/SNP I&C lineage"
  "The evidence supports a specific technical role, not sole possession of the programme's knowledge."

rezaProfile : K.CriticalKnowledgeProfile
rezaProfile = K.critical-knowledge-profile
  "Monica Jacinto / Monica Reza"
  (K.knowledge-coordinate-receipt
      "Monica Jacinto / Monica Reza" K.publicKnowledge K.coordinateSourceBacked
      "US20040208777A1 / US10/769,195"
      "Burn-resistant high-strength nickel-alloy work is public and inventor-attributed."
   ∷ K.knowledge-coordinate-receipt
      "Monica Jacinto / Monica Reza" K.tacitImplementationKnowledge K.coordinateNotLocated
      "not located"
      "The patent does not establish sole ownership of manufacturing/scale-up know-how."
   ∷ K.knowledge-coordinate-receipt
      "Monica Jacinto / Monica Reza" K.sensitiveOrRestrictedKnowledge K.coordinateNotLocated
      "not located"
      "No primary receipt currently establishes restricted/exotic-material knowledge."
   ∷ [])
  (K.criticality-receipt
      "Monica Jacinto / Monica Reza" K.uniqueness K.coordinateNotLocated
      "not located"
      "Sole-holder/unique manufacturing-lineage claims remain unsupported."
   ∷ K.criticality-receipt
      "Monica Jacinto / Monica Reza" K.integrationBreadth K.coordinatePartial
      "reported JPL Materials Processing Group leadership; primary JPL role record still preferred"
      "A materials-group leadership role would support breadth if same-object institutionally confirmed."
   ∷ K.criticality-receipt
      "Monica Jacinto / Monica Reza" K.replacementDifficulty K.coordinateNotLocated
      "not located"
      "Need successor and group/programme continuity evidence."
   ∷ [])
  "patent + event-time role acquisition frontier"
  "Public rhetoric currently outruns the source-backed uniqueness/nonpublicness evidence."

maiwaldProfile : K.CriticalKnowledgeProfile
maiwaldProfile = K.critical-knowledge-profile
  "Frank W. Maiwald"
  (K.knowledge-coordinate-receipt
      "Frank W. Maiwald" K.tacitImplementationKnowledge K.coordinatePartial
      "colleague memorial testimony in published obituary"
      "Testimony describes process qualification, assembly/screening techniques, cost/schedule management, and service-centre process knowledge."
   ∷ K.knowledge-coordinate-receipt
      "Frank W. Maiwald" K.integrationKnowledge K.coordinatePartial
      "obituary and JPL project-role lineage"
      "Instrument-development management plus technical/process responsibility supports integration knowledge."
   ∷ K.knowledge-coordinate-receipt
      "Frank W. Maiwald" K.publicKnowledge K.coordinateSourceBacked
      "JPL Principal registry; JPL SURP 2023"
      "Planetary mass spectrometry and biosignature action-spectroscopy roles are source-backed."
   ∷ [])
  (K.criticality-receipt
      "Frank W. Maiwald" K.uniqueness K.coordinateNotLocated
      "not located"
      "Need evidence that process/instrument expertise was rare rather than merely deep."
   ∷ K.criticality-receipt
      "Frank W. Maiwald" K.replacementDifficulty K.coordinateNotLocated
      "not located"
      "SBG-VSWIR programme continued; exact management-successor latency remains unresolved."
   ∷ K.criticality-receipt
      "Frank W. Maiwald" K.integrationBreadth K.coordinatePartial
      "instrument-management and group-supervisor role"
      "Technical plus process/management breadth is better supported here than in most rows."
   ∷ [])
  "JPL role + memorial testimony lineage"
  "Maiwald is presently one of the stronger tacit/process-knowledge candidates, but uniqueness and replacement difficulty remain open."

------------------------------------------------------------------------
-- Reverse acquisition targets generated by the strong-claim firewall.
------------------------------------------------------------------------

loureiroNonPublicnessTarget : K.CriticalKnowledgeAcquisitionTarget
loureiroNonPublicnessTarget = K.critical-knowledge-acquisition-target
  "Nuno F. G. Loureiro"
  K.needNonPublicnessEvidence
  "authenticated advisory, programme, grant, security/access, unpublished project or institutional record identifying specific nonpublic knowledge"
  "credible role-specific institutional testimony"
  "upgrade nonpublicness only; never targeting or causation"

chavezUniquenessTarget : K.CriticalKnowledgeAcquisitionTarget
chavezUniquenessTarget = K.critical-knowledge-acquisition-target
  "Anthony Chavez"
  K.needUniquenessEvidence
  "Scorpius subsystem ownership, design-authority matrix, successor assignment, rare facility qualification or technical-responsibility record"
  "institutional testimony naming unique or difficult-to-substitute responsibilities"
  "upgrade uniqueness/replaceability only if same-object and role-specific"

mccaslandReplacementTarget : K.CriticalKnowledgeAcquisitionTarget
mccaslandReplacementTarget = K.critical-knowledge-acquisition-target
  "William N. McCasland"
  K.needReplacementDifficultyEvidence
  "ATA/BlueHalo succession, IRAD portfolio-transfer, technology-strategy reassignment or programme-risk records after disappearance"
  "contemporaneous corporate leadership announcement or role redistribution"
  "upgrade event-time replacement difficulty only"

leblancReplacementTarget : K.CriticalKnowledgeAcquisitionTarget
leblancReplacementTarget = K.critical-knowledge-acquisition-target
  "Joshua Kyle LeBlanc"
  K.needReplacementDifficultyEvidence
  "NASA/Marshall post-July-2025 SNP I&C TechMat lead roster, responsibility-transfer or milestone record"
  "subsequent webinar/org-chart/team roster naming successor"
  "upgrade local role replacement difficulty only"

rezaUniquenessTarget : K.CriticalKnowledgeAcquisitionTarget
rezaUniquenessTarget = K.critical-knowledge-acquisition-target
  "Monica Jacinto / Monica Reza"
  K.needUniquenessEvidence
  "primary JPL group-role record, manufacturing/scale-up ownership, patent follow-on, programme documentation or successor record"
  "authenticated colleague/institutional testimony tied to a specific technical object"
  "do not upgrade from repeated media claims alone"

maiwaldReplacementTarget : K.CriticalKnowledgeAcquisitionTarget
maiwaldReplacementTarget = K.critical-knowledge-acquisition-target
  "Frank W. Maiwald"
  K.needReplacementDifficultyEvidence
  "SBG-VSWIR management successor, schedule/budget transfer, staffing/reorganisation or process-qualification handover record"
  "JPL project archive or colleague/institutional testimony"
  "upgrade local replacement difficulty only"

record CurrentCriticalKnowledgeAssessment : Set where
  constructor current-critical-knowledge-assessment
  field
    rosterWideStrongKnewTooMuchClaimClosed : Bool
    rosterWideStrongKnewTooMuchClaimClosedIsFalse :
      rosterWideStrongKnewTooMuchClaimClosed ≡ false
    mccaslandIntegrationBreadthSourceBacked : Bool
    mccaslandIntegrationBreadthSourceBackedIsTrue :
      mccaslandIntegrationBreadthSourceBacked ≡ true
    maiwaldTacitProcessKnowledgeHasPrimaryOrNearPrimaryTestimony : Bool
    maiwaldTacitProcessKnowledgeHasPrimaryOrNearPrimaryTestimonyIsTrue :
      maiwaldTacitProcessKnowledgeHasPrimaryOrNearPrimaryTestimony ≡ true
    leblancWasSoleICKnowledgeHolderEstablished : Bool
    leblancWasSoleICKnowledgeHolderEstablishedIsFalse :
      leblancWasSoleICKnowledgeHolderEstablished ≡ false
    rezaSoleSecretManufacturingHolderEstablished : Bool
    rezaSoleSecretManufacturingHolderEstablishedIsFalse :
      rezaSoleSecretManufacturingHolderEstablished ≡ false
    reverseAcquisitionFrontierIsLive : Bool
    reverseAcquisitionFrontierIsLiveIsTrue : reverseAcquisitionFrontierIsLive ≡ true

canonicalCurrentCriticalKnowledgeAssessment : CurrentCriticalKnowledgeAssessment
canonicalCurrentCriticalKnowledgeAssessment = current-critical-knowledge-assessment
  false refl
  true refl
  true refl
  false refl
  false refl
  true refl
