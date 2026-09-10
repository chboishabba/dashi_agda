module DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.SensibLawWoogarooAdmissibleFactorsWrongTypeAtomBridgeExact as AFW
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Wrong

------------------------------------------------------------------------
-- WOOGAROO LEGAL CONSUMER ATOM COMPLETION
--
-- This is not a second legal calculus. It completes the current Woogaroo
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

-- Atomic propositions required by the live legal roadmap. Existing AFW
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
-- Atom admission is consumer indexed. Admission means relevant input, not
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
-- Current source-payment state. These are bounded repository readings, not
-- adjudicated legal conclusions. The newly acquired 2019 referral-era ecology
-- is kept distinct from the 2026 final-PD state: historical source payment is
-- not silently promoted into a claim that nothing changed by 2026.
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

federalActionPolygonPayment : LegalAtomPayment
federalActionPolygonPayment = legal-atom-payment
  finalPDActionPolygonAtom
  epbc8575MeritsConsumer
  partiallyPaid
  "Primary 2019 referral identifies Lot 9999 SP292760 (158.2 ha), 162 ha referral area and 136 ha impact area; SHG Attachment 1 supplies site-locality/aerial geometry and Plan 6 maps the 136 ha critical-habitat impact area."
  "Compare these referral-era geometries with the 2026 final Preliminary Documentation action/clearing polygon and record any delta rather than assuming identity through time."

federalImpactedHabitatPayment : LegalAtomPayment
federalImpactedHabitatPayment = legal-atom-payment
  impactedHabitatQuantityAtom
  epbc8575MeritsConsumer
  sourcePaid
  "SHG's 2019 MNES report states approximately 136 ha direct clearing of native Koala habitat plus 26 ha indirect impact; habitat score 7/10; Plan 6 labels the 136 ha referral-site critical-habitat impact area."
  "The 2019 proposition is source-paid as a proponent/consultant proposition; acquire the 2026 final-PD corresponding quantity to test persistence, revision or supersession."

federalResidualImpactPayment : LegalAtomPayment
federalResidualImpactPayment = legal-atom-payment
  residualImpactAtom
  epbc8575MeritsConsumer
  partiallyPaid
  "SHG's 2019 report concludes the clearing and functional loss of 136 ha of habitat score 7 is a significant impact on Koala habitat critical to survival, while its Table 15 separately argues some recovery-pathway impacts can be mitigated/no residual impact identified."
  "Extract the complete 2026 final-PD residual-impact analysis and distinguish significant habitat-loss conclusion from later mitigation/offset conclusions."

s102ClearingFootprintPayment : LegalAtomPayment
s102ClearingFootprintPayment = legal-atom-payment
  approvedClearingFootprintAtom
  nca102InterimOrderConsumer
  partiallyPaid
  "9281/2024/OW is an approved operational-works object expressly covering vegetation clearing; the 2019 EPBC material independently maps a 136 ha Springview impact/critical-habitat footprint."
  "Acquire the approved 9281 vegetation-clearing drawing/polygon and prove its exact intersection with the EPBC habitat geometry; one approval's footprint is not another approval's footprint."

s102TimingPayment : LegalAtomPayment
s102TimingPayment = legal-atom-payment
  worksCommencementTimingAtom
  nca102InterimOrderConsumer
  open
  "Approval exists, but approval is not commencement."
  "Acquire dated commencement notices, works program, site evidence or other same-object timing receipt."

s102AffectedHabitatPayment : LegalAtomPayment
s102AffectedHabitatPayment = legal-atom-payment
  affectedWildlifeHabitatAtom
  nca102InterimOrderConsumer
  partiallyPaid
  "Primary SHG ecology for the same Springview parcel maps Koala critical habitat score 7, Koala food trees, scat evidence, >500 ha connectivity analysis and Woogaroo/Opossum Creek habitat values; this identifies a strong candidate affected-habitat object."
  "Bind the exact 9281 clearing polygon to these habitat/wildlife surfaces and update with current ecology rather than assuming every 2019 habitat feature persists unchanged."

s13EssentialityPayment : LegalAtomPayment
s13EssentialityPayment = legal-atom-payment
  habitatPopulationEssentialityAtom
  nca13EssentialityConsumer
  partiallyPaid
  "Same-project evidence is now strong on habitat function: Lot 9999 SP292760/162 ha referral object; mostly remnant vegetation; recognised Koala food trees; scat evidence; Woogaroo/Opossum Creek connectivity; Plan 5 maps habitat connectivity >500 ha; SHG scores connectivity 2 and total habitat 7/10."
  "The statutory essentiality proposition remains open. The same SHG report argues recovery value 0 and says the site is not viable to support a Koala population; counsel/ecology must stress-test that adverse proposition against the report's own >500 ha connectivity, planned surrounding loss, current corridor evidence and current species evidence."

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
  "The 2019 referral itself identifies a Planning Regulation 2017 urban-purpose/urban-area vegetation-clearing exemption theory for least-concern/of-concern vegetation, while Council material records later mapped-koala-habitat plus approved/exempted outcomes and the LAP/ADP/OW chain is identified."
  "Counsel should identify the exact historical and current instruments, their transition rules, vegetation classes and parcel/stage/variation scope; the proponent's 2019 legal characterisation is not an adjudicated current exemption."

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
data KoalaGuidelineCriticalHabitatEqualsNCA13CriticalHabitat : Set where
data SignificantEPBCHabitatImpactEqualsPart9Refusal : Set where
data ReferralEraGeometryEqualsFinalPDGeometry : Set where
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

noEPBCCriticalNCA13Collapse : KoalaGuidelineCriticalHabitatEqualsNCA13CriticalHabitat → ⊥
noEPBCCriticalNCA13Collapse ()

noSignificantImpactRefusalCollapse : SignificantEPBCHabitatImpactEqualsPart9Refusal → ⊥
noSignificantImpactRefusalCollapse ()

noReferralFinalGeometryCollapse : ReferralEraGeometryEqualsFinalPDGeometry → ⊥
noReferralFinalGeometryCollapse ()

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
-- Consumer adequacy: a bundle must contain the right atom family. This is a
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
  "controlled action; listed matters; delegate/deadline; Lot 9999 SP292760; 162 ha referral geometry; 136 ha impact; 136 ha direct plus 26 ha indirect Koala habitat impact; habitat score 7; SHG significant-impact conclusion; Plan 5/6 connectivity and critical-habitat maps"
  "2026 final-PD delta: final action/clearing polygon; retained habitat; avoidance/alternatives; complete residual-impact treatment; final offsets; conservation/recovery-plan correspondence"
  "2019 referral evidence != unchanged 2026 final-PD state; significant EPBC habitat impact != automatic Part 9 refusal"

s13Residual : ConsumerAtomResidual
s13Residual = consumer-atom-residual
  nca13EssentialityConsumer
  "exact Springview parcel; mostly remnant vegetation; Koala food trees/scats; habitat score 7; SHG >500 ha connectivity surface; Woogaroo/Opossum creek function; connected-landscape and corridor evidence"
  "viable-population/community essentiality and rebuttal/stress-test of SHG's adverse recovery-value/viability reasoning"
  "EPBC Koala-guideline critical habitat != NCA s13 critical habitat; connectivity != statutory essentiality"

s102Residual : ConsumerAtomResidual
s102Residual = consumer-atom-residual
  nca102InterimOrderConsumer
  "approved 9281/2024/OW vegetation-clearing works object; exact same-parcel 2019 habitat/impact evidence; 136 ha critical-habitat impact geometry candidate"
  "exact 9281 approved clearing polygon; commencement timing; current affected wildlife/habitat; likely significant detrimental effect"
  "EPBC/referral impact geometry != 9281 works geometry; approval != commencement; clearing entitlement != statutory detrimental effect"

offsetResidual : ConsumerAtomResidual
offsetResidual = consumer-atom-residual
  epbc8575OffsetAdequacyConsumer
  "candidate offset names/areas; regional conservation/development context; restoration-lag evidence"
  "exact parcel identity; baseline risk of loss; existing protection/prior obligations; maturity; functional/time equivalence"
  "same name != same parcel; restoration commitment != immediate mature habitat"

planningResidual : ConsumerAtomResidual
planningResidual = consumer-atom-residual
  planningExemptionScopeConsumer
  "2019 referral's urban-clearing exemption theory; mapped koala habitat; approved/exempted outcome; identified LAP/ADP/OW chain"
  "exact current exemption instrument; transition/temporal scope; vegetation class; parcel/stage/variation scope"
  "proponent legal characterisation != current adjudicated scope; mapped habitat != prohibition; historic exemption != current scope"

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
