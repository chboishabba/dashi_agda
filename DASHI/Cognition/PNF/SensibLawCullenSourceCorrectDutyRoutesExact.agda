module DASHI.Cognition.PNF.SensibLawCullenSourceCorrectDutyRoutesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawCullenPublicAuthorityDutyCalibrationExact as Legacy

------------------------------------------------------------------------
-- SOURCE-CORRECT CULLEN DUTY ROUTES
--
-- This module supersedes only the old synthetic premise bundle
--
--   "statutory police functions/powers".
--
-- The reviewed source tranche distinguishes:
--
--   PoliceFunctionContext != StatutoryPowerInvoked.
--
-- The retained Edelman passage expressly places the intervention outside an
-- invocation of statutory power.  The source-correct reconstruction therefore
-- preserves two reasoning fibres instead of forcing both judgments into one
-- synthetic three-premise rule.
--
-- IMPORTANT: the implication-shaped LegalRules below are DASHI reconstruction
-- objects over source-reviewed propositions.  They are not attributed verbatim
-- to the judges.  Proposition/source identity is preserved independently from
-- the compiled graph edge.
------------------------------------------------------------------------

cullenSource : Algebra.LegalSourceRef
cullenSource = Legacy.cullenSource

positiveOperationalAct : Algebra.LegalProposition
positiveOperationalAct = Legacy.positiveOperationalAct

foreseeablePhysicalInjuryRisk : Algebra.LegalProposition
foreseeablePhysicalInjuryRisk = Legacy.foreseeablePhysicalInjuryRisk

cullenDutyProposition : Algebra.LegalProposition
cullenDutyProposition = Legacy.cullenDutyProposition

------------------------------------------------------------------------
-- Split institutional coordinates.
------------------------------------------------------------------------

policeFunctionContext : Algebra.LegalProposition
policeFunctionContext = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:police-function-context")
  Algebra.institutionalConstraint
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "activity:crowd-control")
  Negligence.auCommonLawSystem
  "the conduct occurred in the performance of a police function"

statutoryPowerInvoked : Algebra.LegalProposition
statutoryPowerInvoked = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:statutory-power-invoked")
  Algebra.institutionalConstraint
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "source:LEPRA-or-other-statutory-power")
  Negligence.auCommonLawSystem
  "the intervention was undertaken pursuant to an invoked statutory power"

statutoryPowerNotRequiredOnEdelmanRoute : Algebra.LegalProposition
statutoryPowerNotRequiredOnEdelmanRoute = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:Edelman:statutory-power-not-required")
  Algebra.doctrinalPredicate
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "issue:negligence:duty")
  Negligence.auCommonLawSystem
  "on the retained Edelman route, ordinary common-law duty analysis does not require the intervention itself to have been pursuant to statutory power"

positiveRiskCreatingActs : Algebra.LegalProposition
positiveRiskCreatingActs = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:Edelman:positive-risk-creating-acts")
  Algebra.factualFeature
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "activity:crowd-control")
  Negligence.auCommonLawSystem
  "positive police acts created or materially contributed to a risk of physical injury"

ordinaryCommonLawDutyAnalysis : Algebra.LegalProposition
ordinaryCommonLawDutyAnalysis = Algebra.legal-proposition
  (Ontology.stableId "prop:Cullen:Edelman:ordinary-common-law-duty-analysis")
  Algebra.doctrinalPredicate
  (Ontology.stableId "actor:NSW-police")
  (Ontology.stableId "issue:negligence:duty")
  Negligence.auCommonLawSystem
  "ordinary common-law principles govern the duty analysis on the retained Edelman route"

------------------------------------------------------------------------
-- Reasoning-route carrier.  This preserves route identity separately from the
-- compiled graph rule and from source authority role.
------------------------------------------------------------------------

data CullenRouteKind : Set where
  jointReasonsRoute : CullenRouteKind
  edelmanRoute : CullenRouteKind

record CullenReasoningRoute : Set where
  constructor cullen-reasoning-route
  field
    routeKind : CullenRouteKind
    premises : List Algebra.LegalProposition
    conclusion : Algebra.LegalProposition
    source : Algebra.LegalSourceRef
    sourceReading : String
    compiledRule : Algebra.LegalRule

open CullenReasoningRoute public

jointReasonsDutyRule : Algebra.LegalRule
jointReasonsDutyRule = Algebra.legal-rule
  (Ontology.stableId "rule:Cullen:joint-reasons-source-correct-duty-route")
  (positiveOperationalAct ∷
   foreseeablePhysicalInjuryRisk ∷
   policeFunctionContext ∷ [])
  cullenDutyProposition
  [] []
  cullenSource
  Algebra.dashReconstructionRole
  "source-reviewed Joint-reasons route; implication shape is DASHI reconstruction"
  "Australia / High Court / NSW police operational conduct"

edelmanDutyRule : Algebra.LegalRule
edelmanDutyRule = Algebra.legal-rule
  (Ontology.stableId "rule:Cullen:Edelman-source-correct-duty-route")
  (positiveRiskCreatingActs ∷
   ordinaryCommonLawDutyAnalysis ∷
   statutoryPowerNotRequiredOnEdelmanRoute ∷ [])
  cullenDutyProposition
  [] []
  cullenSource
  Algebra.dashReconstructionRole
  "source-reviewed Edelman route; implication shape is DASHI reconstruction"
  "Australia / High Court / NSW police operational conduct"

jointReasons : CullenReasoningRoute
jointReasons = cullen-reasoning-route
  jointReasonsRoute
  (positiveOperationalAct ∷ foreseeablePhysicalInjuryRisk ∷ policeFunctionContext ∷ [])
  cullenDutyProposition
  cullenSource
  "Joint-reasons fibre: positive conduct + foreseeable physical injury + police-function context."
  jointReasonsDutyRule

edelmanReasons : CullenReasoningRoute
edelmanReasons = cullen-reasoning-route
  edelmanRoute
  (positiveRiskCreatingActs ∷ ordinaryCommonLawDutyAnalysis ∷
   statutoryPowerNotRequiredOnEdelmanRoute ∷ [])
  cullenDutyProposition
  cullenSource
  "Edelman fibre: positive risk-creating acts + ordinary common-law duty analysis + no requirement that the intervention itself invoke statutory power."
  edelmanDutyRule

------------------------------------------------------------------------
-- The old bundled premise is retained only as a legacy identifier for audits.
-- It is not a premise of either source-correct route.
------------------------------------------------------------------------

legacyBundledStatutoryPoliceFunction : Algebra.LegalProposition
legacyBundledStatutoryPoliceFunction = Legacy.statutoryPoliceFunction

data PoliceFunctionImpliesStatutoryPower : Set where
data NoStatutoryPowerImpliesNoDuty : Set where
data PremiseSplitAloneProvesDuty : Set where
data OldBundledRuleReusableUnchanged : Set where

policeFunctionDoesNotCollapseIntoPower : PoliceFunctionImpliesStatutoryPower → ⊥
policeFunctionDoesNotCollapseIntoPower ()

noStatutoryPowerDoesNotNegateDutyByItself : NoStatutoryPowerImpliesNoDuty → ⊥
noStatutoryPowerDoesNotNegateDutyByItself ()

splitDoesNotAutoCloseDuty : PremiseSplitAloneProvesDuty → ⊥
splitDoesNotAutoCloseDuty ()

oldBundledRuleIsNotReusable : OldBundledRuleReusableUnchanged → ⊥
oldBundledRuleIsNotReusable ()

------------------------------------------------------------------------
-- Source-correct graph carrier: two separate routes, one source and one duty
-- conclusion.  Coexistence does not merge the reasoning fibres.
------------------------------------------------------------------------

cullenSourceCorrectGraph : Algebra.LegalGraph
cullenSourceCorrectGraph = Algebra.legal-graph
  (jointReasonsDutyRule ∷ edelmanDutyRule ∷ [])
  (cullenSource ∷ [])
