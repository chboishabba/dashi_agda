module DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.SensibLawWoogarooAdmissibleFactorsWrongTypeAtomBridgeExact as AFW
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Wrong

------------------------------------------------------------------------
-- WOOGAROO LEGAL CONSUMER ATOM COMPLETION
--
-- This is not a second legal calculus.  It completes the current Woogaroo
-- execution consumers that post-date the original AFW bridge, while reusing
-- the original AFW atoms wherever the same proposition is already owned.
------------------------------------------------------------------------

data LegalExecutionConsumer : Set where
  epbc8575MeritsConsumer : LegalExecutionConsumer
  epbc8575OffsetAdequacyConsumer : LegalExecutionConsumer
  nca13EssentialityConsumer : LegalExecutionConsumer
  nca102InterimOrderConsumer : LegalExecutionConsumer
  nca49NatureRefugeConsumer : LegalExecutionConsumer
  planningExemptionScopeConsumer : LegalExecutionConsumer
  enforcementRestraintConsumer : LegalExecutionConsumer

-- Atomic propositions required by the live legal roadmap.  Existing AFW
-- atoms are referenced through ExistingAtomReuse below rather than copied.
data LegalExecutionAtom : Set where
  finalPDActionPolygonAtom : LegalExecutionAtom
  impactedHabitatQuantityAtom : LegalExecutionAtom
  retainedHabitatQuantityAtom : LegalExecutionAtom
  avoidanceAlternativesAtom : LegalExecutionAtom
  residualImpactAtom : LegalExecutionAtom
  conservationAdviceConsistencyAtom : LegalExecutionAtom
  offsetParcelIdentityAtom : LegalExecutionAtom
  offsetBaselineRiskOfLossAtom : LegalExecutionAtom
  offsetExistingProtectionAtom : LegalExecutionAtom
  offsetPriorObligationAtom : LegalExecutionAtom
  offsetVegetationMaturityAtom : LegalExecutionAtom
  offsetRestorationLagAtom : LegalExecutionAtom
  habitatPopulationEssentialityAtom : LegalExecutionAtom
  approvedClearingFootprintAtom : LegalExecutionAtom
  worksCommencementTimingAtom : LegalExecutionAtom
  affectedWildlifeHabitatAtom : LegalExecutionAtom
  likelySignificantDetrimentalEffectAtom : LegalExecutionAtom
  exactParcelTenureAtom : LegalExecutionAtom
  natureRefugeSuitabilityAtom : LegalExecutionAtom
  executiveInitiationAtom : LegalExecutionAtom
  planningExemptionInstrumentAtom : LegalExecutionAtom
  exemptionTemporalScopeAtom : LegalExecutionAtom
  exemptionParcelStageScopeAtom : LegalExecutionAtom
  exactThreatenedConductAtom : LegalExecutionAtom
  exactContraventionAtom : LegalExecutionAtom
  standingProcedureAtom : LegalExecutionAtom

record ExistingAtomReuse : Set where
  constructor existing-atom-reuse
  field
    threatenedSpeciesPresence : AFW.WoogarooAtom
    exactParcelHabitatFunction : AFW.WoogarooAtom
    activeFederalDecisionWindow : AFW.WoogarooAtom
    authorisedEPBCDelegate : AFW.WoogarooAtom

open ExistingAtomReuse public

canonicalExistingAtomReuse : ExistingAtomReuse
canonicalExistingAtomReuse = existing-atom-reuse
  AFW.threatenedSpeciesPresenceAtom
  AFW.exactParcelHabitatFunctionAtom
  AFW.activeFederalDecisionWindowAtom
  AFW.authorisedEPBCDelegateAtom

------------------------------------------------------------------------
-- Atom admission is consumer indexed.  Admission means relevant input, not
-- sufficiency, FactorsThrough, authority, adjudication, or realised outcome.
------------------------------------------------------------------------

data LegalAtomAdmissibleFor : LegalExecutionAtom → LegalExecutionConsumer → Set where
  finalPDPolygonForMerits : LegalAtomAdmissibleFor finalPDActionPolygonAtom epbc8575MeritsConsumer
  impactedHabitatForMerits : LegalAtomAdmissibleFor impactedHabitatQuantityAtom epbc8575MeritsConsumer
  retainedHabitatForMerits : LegalAtomAdmissibleFor retainedHabitatQuantityAtom epbc8575MeritsConsumer
  avoidanceForMerits : LegalAtomAdmissibleFor avoidanceAlternativesAtom epbc8575MeritsConsumer
  residualForMerits : LegalAtomAdmissibleFor residualImpactAtom epbc8575MeritsConsumer
  adviceForMerits : LegalAtomAdmissibleFor conservationAdviceConsistencyAtom epbc8575MeritsConsumer

  offsetIdentityForOffset : LegalAtomAdmissibleFor offsetParcelIdentityAtom epbc8575OffsetAdequacyConsumer
  offsetRiskForOffset : LegalAtomAdmissibleFor offsetBaselineRiskOfLossAtom epbc8575OffsetAdequacyConsumer
  offsetProtectionForOffset : LegalAtomAdmissibleFor offsetExistingProtectionAtom epbc8575OffsetAdequacyConsumer
  offsetPriorForOffset : LegalAtomAdmissibleFor offsetPriorObligationAtom epbc8575OffsetAdequacyConsumer
  offsetMaturityForOffset : LegalAtomAdmissibleFor offsetVegetationMaturityAtom epbc8575OffsetAdequacyConsumer
  offsetLagForOffset : LegalAtomAdmissibleFor offsetRestorationLagAtom epbc8575OffsetAdequacyConsumer

  essentialityForS13 : LegalAtomAdmissibleFor habitatPopulationEssentialityAtom nca13EssentialityConsumer

  clearingFootprintForS102 : LegalAtomAdmissibleFor approvedClearingFootprintAtom nca102InterimOrderConsumer
  timingForS102 : LegalAtomAdmissibleFor worksCommencementTimingAtom nca102InterimOrderConsumer
  affectedHabitatForS102 : LegalAtomAdmissibleFor affectedWildlifeHabitatAtom nca102InterimOrderConsumer
  detrimentalEffectForS102 : LegalAtomAdmissibleFor likelySignificantDetrimentalEffectAtom nca102InterimOrderConsumer

  tenureForS49 : LegalAtomAdmissibleFor exactParcelTenureAtom nca49NatureRefugeConsumer
  suitabilityForS49 : LegalAtomAdmissibleFor natureRefugeSuitabilityAtom nca49NatureRefugeConsumer
  initiationForS49 : LegalAtomAdmissibleFor executiveInitiationAtom nca49NatureRefugeConsumer

  exemptionInstrumentForAudit : LegalAtomAdmissibleFor planningExemptionInstrumentAtom planningExemptionScopeConsumer
  exemptionTemporalForAudit : LegalAtomAdmissibleFor exemptionTemporalScopeAtom planningExemptionScopeConsumer
  exemptionParcelForAudit : LegalAtomAdmissibleFor exemptionParcelStageScopeAtom planningExemptionScopeConsumer

  conductForEnforcement : LegalAtomAdmissibleFor exactThreatenedConductAtom enforcementRestraintConsumer
  contraventionForEnforcement : LegalAtomAdmissibleFor exactContraventionAtom enforcementRestraintConsumer
  standingForEnforcement : LegalAtomAdmissibleFor standingProcedureAtom enforcementRestraintConsumer

------------------------------------------------------------------------
-- Current source-payment state.  These are bounded repository readings, not
-- adjudicated legal conclusions.
------------------------------------------------------------------------

data AtomPaymentState : Set where
  sourcePaid : AtomPaymentState
  partiallyPaid : AtomPaymentState
  open : AtomPaymentState
  conditional : AtomPaymentState

record LegalAtomPayment : Set where
  constructor legal-atom-payment
  field
    atom : LegalExecutionAtom
    consumer : LegalExecutionConsumer
    state : AtomPaymentState
    currentReceipt : String
    residual : String

open LegalAtomPayment public

s102ClearingFootprintPayment : LegalAtomPayment
s102ClearingFootprintPayment = legal-atom-payment
  approvedClearingFootprintAtom
  nca102InterimOrderConsumer
  partiallyPaid
  "9281/2024/OW is an approved operational-works object expressly covering vegetation clearing."
  "Acquire the approved vegetation-clearing drawing/polygon and bind it to the exact habitat/species geometry."

s102TimingPayment : LegalAtomPayment
s102TimingPayment = legal-atom-payment
  worksCommencementTimingAtom
  nca102InterimOrderConsumer
  open
  "Approval exists, but approval is not commencement."
  "Acquire dated commencement notices, works program, site evidence or other same-object timing receipt."

s13EssentialityPayment : LegalAtomPayment
s13EssentialityPayment = legal-atom-payment
  habitatPopulationEssentialityAtom
  nca13EssentialityConsumer
  partiallyPaid
  "Landscape-function evidence includes the Scenic/Peninsula 675 ha connected-landscape analysis, Woogaroo/Bellevue connectivity evidence, corridor context, historical wooded-cover evidence and current occurrence evidence."
  "Bind that landscape function to the exact Springview parcel and the viable-population/native-wildlife-community essentiality proposition."

offsetIdentityPayment : LegalAtomPayment
offsetIdentityPayment = legal-atom-payment
  offsetParcelIdentityAtom
  epbc8575OffsetAdequacyConsumer
  partiallyPaid
  "Candidate names/areas exist at secondary-source level for Avonvale, Esk and Mt Walker West."
  "Acquire exact lot/plan and GIS polygon for every proposed offset; same place name is not same parcel."

offsetRiskPayment : LegalAtomPayment
offsetRiskPayment = legal-atom-payment
  offsetBaselineRiskOfLossAtom
  epbc8575OffsetAdequacyConsumer
  open
  "Regional development/conservation context exists but does not determine parcel-specific without-offset loss risk."
  "Determine lawful development/clearing pathways, existing constraints and realistic counterfactual loss for each exact offset parcel."

planningExemptionPayment : LegalAtomPayment
planningExemptionPayment = legal-atom-payment
  planningExemptionInstrumentAtom
  planningExemptionScopeConsumer
  partiallyPaid
  "Council material records mapped koala habitat together with an exempted/approved Springview development outcome and the local approval chain is identified."
  "Acquire the exact exemption/grandfathering instrument and test temporal, parcel, stage and variation scope."

enforcementContraventionPayment : LegalAtomPayment
enforcementContraventionPayment = legal-atom-payment
  exactContraventionAtom
  enforcementRestraintConsumer
  conditional
  "Enforcement mechanisms are source-paid; no current repository receipt automatically establishes an exact contravention."
  "Activate only when exact threatened/actual conduct is mapped to an exact applicable prohibition, condition, offence or other enforceable obligation."

------------------------------------------------------------------------
-- Legal WrongTypes exposed by the present roadmap.
------------------------------------------------------------------------

data ControlledActionEqualsRefusal : Set where
data SpeciesPresenceEqualsS13Essentiality : Set where
data ConnectedLandscapeEqualsExactParcelEssentiality : Set where
data WorksApprovalEqualsWorksCommenced : Set where
data ClearingEntitlementEqualsS102DetrimentalEffect : Set where
data VegetationClearingEqualsContravention : Set where
data MappedKoalaHabitatEqualsPlanningProhibition : Set where
data ExemptionHistoryEqualsCurrentExemptionScope : Set where
data OffsetNameEqualsOffsetParcelIdentity : Set where
data ExistingConservationContextEqualsExactOffsetProtection : Set where
data RemoteOffsetEqualsFunctionalEquivalence : Set where
data RestorationCommitmentEqualsImmediateMatureHabitat : Set where
data ResearchGradeOccurrenceEqualsAgencyFinding : Set where
data ObserverOccurrenceEqualsCriticalHabitat : Set where
data S13EvidenceEqualsS49Declaration : Set where
data EnvironmentalHarmEqualsEnforceableContravention : Set where

noControlledActionRefusalCollapse : ControlledActionEqualsRefusal → ⊥
noControlledActionRefusalCollapse ()

noSpeciesEssentialityCollapse : SpeciesPresenceEqualsS13Essentiality → ⊥
noSpeciesEssentialityCollapse ()

noLandscapeParcelEssentialityCollapse : ConnectedLandscapeEqualsExactParcelEssentiality → ⊥
noLandscapeParcelEssentialityCollapse ()

noApprovalCommencementCollapse : WorksApprovalEqualsWorksCommenced → ⊥
noApprovalCommencementCollapse ()

noClearingDetrimentalEffectCollapse : ClearingEntitlementEqualsS102DetrimentalEffect → ⊥
noClearingDetrimentalEffectCollapse ()

noClearingContraventionCollapse : VegetationClearingEqualsContravention → ⊥
noClearingContraventionCollapse ()

noMappedHabitatProhibitionCollapse : MappedKoalaHabitatEqualsPlanningProhibition → ⊥
noMappedHabitatProhibitionCollapse ()

noExemptionScopeCollapse : ExemptionHistoryEqualsCurrentExemptionScope → ⊥
noExemptionScopeCollapse ()

noOffsetNameIdentityCollapse : OffsetNameEqualsOffsetParcelIdentity → ⊥
noOffsetNameIdentityCollapse ()

noRegionalProtectionParcelCollapse : ExistingConservationContextEqualsExactOffsetProtection → ⊥
noRegionalProtectionParcelCollapse ()

noRemoteFunctionalEquivalenceCollapse : RemoteOffsetEqualsFunctionalEquivalence → ⊥
noRemoteFunctionalEquivalenceCollapse ()

noRestorationMaturityCollapse : RestorationCommitmentEqualsImmediateMatureHabitat → ⊥
noRestorationMaturityCollapse ()

noResearchGradeAgencyCollapse : ResearchGradeOccurrenceEqualsAgencyFinding → ⊥
noResearchGradeAgencyCollapse ()

noOccurrenceCriticalHabitatCollapse : ObserverOccurrenceEqualsCriticalHabitat → ⊥
noOccurrenceCriticalHabitatCollapse ()

noS13S49Collapse : S13EvidenceEqualsS49Declaration → ⊥
noS13S49Collapse ()

noHarmContraventionCollapse : EnvironmentalHarmEqualsEnforceableContravention → ⊥
noHarmContraventionCollapse ()

------------------------------------------------------------------------
-- Consumer adequacy: a bundle must contain the right atom family.  This is a
-- compact routing surface for counsel; it is not a proof that the legal test
-- is satisfied.
------------------------------------------------------------------------

record ConsumerAtomResidual : Set where
  constructor consumer-atom-residual
  field
    consumer : LegalExecutionConsumer
    strongestPaidAtoms : String
    missingAtoms : String
    principalWrongType : String

open ConsumerAtomResidual public

federalResidual : ConsumerAtomResidual
federalResidual = consumer-atom-residual
  epbc8575MeritsConsumer
  "controlled action; listed matters; delegate/deadline; neighbouring primary habitat/connectivity evidence"
  "final-PD action polygon; impacted/retained habitat; avoidance; residual impact; offsets; conservation/recovery-plan correspondence"
  "controlled action != refusal; species occurrence != significant-impact conclusion"

s13Residual : ConsumerAtomResidual
s13Residual = consumer-atom-residual
  nca13EssentialityConsumer
  "threatened-species/habitat evidence; connected-landscape and corridor-function evidence"
  "exact Springview parcel x habitat function x viable-population/community essentiality"
  "connected landscape != exact-parcel statutory essentiality"

s102Residual : ConsumerAtomResidual
s102Residual = consumer-atom-residual
  nca102InterimOrderConsumer
  "approved 9281/2024/OW vegetation-clearing works object; threatened wildlife/habitat context"
  "approved clearing polygon; commencement timing; affected wildlife/habitat; likely significant detrimental effect"
  "approval != commencement; clearing entitlement != statutory detrimental effect"

offsetResidual : ConsumerAtomResidual
offsetResidual = consumer-atom-residual
  epbc8575OffsetAdequacyConsumer
  "candidate offset names/areas; regional conservation/development context; restoration-lag evidence"
  "exact parcel identity; baseline risk of loss; existing protection/prior obligations; maturity; functional/time equivalence"
  "same name != same parcel; restoration commitment != immediate mature habitat"

planningResidual : ConsumerAtomResidual
planningResidual = consumer-atom-residual
  planningExemptionScopeConsumer
  "mapped koala habitat; approved/exempted outcome; identified LAP/ADP/OW chain"
  "exact exemption instrument; temporal scope; parcel/stage/variation scope"
  "mapped habitat != prohibition; historic exemption != current scope"

enforcementResidual : ConsumerAtomResidual
enforcementResidual = consumer-atom-residual
  enforcementRestraintConsumer
  "statutory enforcement routes"
  "exact conduct; exact contravention; standing/procedure; chronology"
  "environmental harm != enforceable statutory contravention"

------------------------------------------------------------------------
-- Canonical WrongType algebra remains authoritative: labels/strings do not
-- manufacture legal elements.
------------------------------------------------------------------------

legalElementStringStillDoesNotPayExecutionAtom :
  Wrong.ElementStringReferenceIsElementProof → ⊥
legalElementStringStillDoesNotPayExecutionAtom = Wrong.stringReferenceDoesNotProveElement

wrongTypeIdStillDoesNotGenerateExecutionElements :
  Wrong.WrongTypeIdAloneDeterminesAllElements → ⊥
wrongTypeIdStillDoesNotGenerateExecutionElements = Wrong.wrongTypeIdDoesNotGenerateElements
