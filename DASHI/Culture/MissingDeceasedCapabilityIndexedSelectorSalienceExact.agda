module DASHI.Culture.MissingDeceasedCapabilityIndexedSelectorSalienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CapabilityIndexedSelectorSalienceExact as S
import DASHI.Core.CapabilitySynthesisHypergraphExact as C
import DASHI.Core.ScientificWorkAttributionExact as A

------------------------------------------------------------------------
-- Contribution hypervoxels: sourced person/work roles mapped into higher-order
-- capability families.  The mapping is DASHI inference, not a historical claim
-- that the people collaborated.
------------------------------------------------------------------------

loureiroWork : A.PersonWorkHypervoxel
loureiroWork = A.person-work-hypervoxel
  "Nuno F. G. Loureiro"
  "fusion confinement, transport, turbulence and magnetic reconnection"
  A.institutionalResearchRole
  A.primaryInstitutionalRecord
  A.externalSourceOwner

leblancWork : A.PersonWorkHypervoxel
leblancWork = A.person-work-hypervoxel
  "Joshua LeBlanc"
  "space nuclear propulsion instrumentation and controls / fission surface power"
  A.namedTechnicalLead
  A.primaryInstitutionalRecord
  A.externalSourceOwner

rezaWork : A.PersonWorkHypervoxel
rezaWork = A.person-work-hypervoxel
  "Monica Jacinto / Monica Reza"
  "burn-resistant high-strength alloys for oxygen-rich environments"
  A.namedInventor
  A.primaryPatentRecord
  A.externalSourceOwner

mccaslandWork : A.PersonWorkHypervoxel
mccaslandWork = A.person-work-hypervoxel
  "William N. McCasland"
  "space systems, payload development, navigation and programme integration"
  A.institutionalLeadershipRole
  A.primaryInstitutionalRecord
  A.externalSourceOwner

hicksWork : A.PersonWorkHypervoxel
hicksWork = A.person-work-hypervoxel
  "Michael David Hicks"
  "asteroid/comet science, DART and near-Earth-object mission science"
  A.namedTeamMember
  A.primaryInstitutionalRecord
  A.externalSourceOwner

maiwaldWork : A.PersonWorkHypervoxel
maiwaldWork = A.person-work-hypervoxel
  "Frank W. Maiwald"
  "planetary mass spectrometry and biosignature action spectroscopy"
  A.namedPrincipalInvestigator
  A.primaryInstitutionalRecord
  A.externalSourceOwner

chavezWork : A.PersonWorkHypervoxel
chavezWork = A.person-work-hypervoxel
  "Anthony Chavez"
  "DARHT and Scorpius accelerator design / radiographic diagnostics"
  A.institutionalResearchRole
  A.primaryInstitutionalRecord
  A.externalSourceOwner

loureiroHighPowerContribution : S.CapabilityContribution
loureiroHighPowerContribution = S.capability-contribution
  loureiroWork
  C.multiMissionStrategicSpaceArchitecture
  C.fusionPhysics
  "MIT/PSFC fusion-plasma source lineage + DASHI capability synthesis"
  "Contributes fusion/plasma physics to the capability family; does not assert participation in one historical space architecture."

leblancHighPowerContribution : S.CapabilityContribution
leblancHighPowerContribution = S.capability-contribution
  leblancWork
  C.multiMissionStrategicSpaceArchitecture
  C.fissionPowerAndPropulsion
  "NASA NTRS 20250008475 + DASHI capability synthesis"
  "Contributes nuclear-space power/control expertise to the capability family."

rezaHighPowerContribution : S.CapabilityContribution
rezaHighPowerContribution = S.capability-contribution
  rezaWork
  C.multiMissionStrategicSpaceArchitecture
  C.extremeEnvironmentMaterials
  "US20040208777A1 + DASHI capability synthesis"
  "Contributes extreme-environment materials expertise; no shared programme is inferred."

mccaslandHighPowerContribution : S.CapabilityContribution
mccaslandHighPowerContribution = S.capability-contribution
  mccaslandWork
  C.multiMissionStrategicSpaceArchitecture
  C.spacecraftSystemsEngineering
  "U.S. Air Force official biography + DASHI capability synthesis"
  "Contributes systems/programme integration knowledge at the architecture level."

hicksHighPowerContribution : S.CapabilityContribution
hicksHighPowerContribution = S.capability-contribution
  hicksWork
  C.multiMissionStrategicSpaceArchitecture
  C.planetaryDefenseAndNEOScience
  "JPL / University of Arizona Hicks source lineage + DASHI capability synthesis"
  "Contributes mission/target knowledge for NEO interception/characterisation applications."

maiwaldHighPowerContribution : S.CapabilityContribution
maiwaldHighPowerContribution = S.capability-contribution
  maiwaldWork
  C.multiMissionStrategicSpaceArchitecture
  C.planetaryMassSpectrometryAndBiosignatures
  "JPL SURP / principal registry + DASHI capability synthesis"
  "Contributes advanced planetary sensing/science payload knowledge."

chavezDiagnosticsContribution : S.CapabilityContribution
chavezDiagnosticsContribution = S.capability-contribution
  chavezWork
  C.highEnergyTestAndDiagnosticsEcosystem
  C.acceleratorRadiographyDiagnostics
  "LANL/NNSA Scorpius-DARHT source lineage + DASHI capability synthesis"
  "Maps primarily to the ground-test/diagnostics ecosystem rather than a flight subsystem."

record CurrentCapabilitySalienceAssessment : Set where
  constructor current-capability-salience-assessment
  field
    severalRosterWorkFibresContributeToOneCapabilityFamily : Bool
    severalRosterWorkFibresContributeToOneCapabilityFamilyIsTrue :
      severalRosterWorkFibresContributeToOneCapabilityFamily ≡ true

    contributionRequiresRosterPeopleToKnowEachOther : Bool
    contributionRequiresRosterPeopleToKnowEachOtherIsFalse :
      contributionRequiresRosterPeopleToKnowEachOther ≡ false

    capabilityAwareCommonSelectorEstablished : Bool
    capabilityAwareCommonSelectorEstablishedIsFalse :
      capabilityAwareCommonSelectorEstablished ≡ false

    publicVisibilityAloneEstablishesCapabilityAwareSelection : Bool
    publicVisibilityAloneEstablishesCapabilityAwareSelectionIsFalse :
      publicVisibilityAloneEstablishesCapabilityAwareSelection ≡ false

    capabilityIndexedSelectorSearchIsLive : Bool
    capabilityIndexedSelectorSearchIsLiveIsTrue :
      capabilityIndexedSelectorSearchIsLive ≡ true

canonicalCurrentCapabilitySalienceAssessment : CurrentCapabilitySalienceAssessment
canonicalCurrentCapabilitySalienceAssessment = current-capability-salience-assessment
  true refl
  false refl
  false refl
  false refl
  true refl
