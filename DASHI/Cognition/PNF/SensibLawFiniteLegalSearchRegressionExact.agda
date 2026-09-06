module DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact where

------------------------------------------------------------------------
-- COMPUTED MABO / PABAI / CULLEN REGRESSION FIXTURES
--
-- These are deliberately small finite legal-graph calibrations. They exercise
-- the executable engine on source-calibrated structures while preserving the
-- boundary between a computed Boolean candidate and a proof-relevant legal
-- derivation/precedent holding.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate
import DASHI.Cognition.PNF.SensibLawCullenPublicAuthorityDutyCalibrationExact as Cullen
import DASHI.Cognition.PNF.SensibLawPrecedentApplicabilityDistinguishingExact as Precedent
import DASHI.Cognition.PNF.SensibLawAuthorityTransformationMinimalCutExact as LegacyCut
import DASHI.Cognition.PNF.SensibLawMaboRecognitionCreationFootholdExact as MaboFoothold

------------------------------------------------------------------------
-- Shared source constructors for executable regression graphs.
------------------------------------------------------------------------

maboSystem : Ontology.StableId
maboSystem = Ontology.stableId "legal-system:AU.common-law.native-title"

maboSource : Algebra.LegalSourceRef
maboSource = Algebra.legal-source-ref
  (Ontology.legalSource
    (Ontology.stableId "source:Mabo:[1992]HCA23")
    maboSystem
    Ontology.caseLaw
    "Mabo v Queensland (No 2) [1992] HCA 23; (1992) 175 CLR 1"
    "1992-06-03"
    "Australia / High Court")
  "High Court of Australia"
  "Mabo v Queensland (No 2)"
  "[1992] HCA 23"

pabaiSource : Algebra.LegalSourceRef
pabaiSource = Algebra.legal-source-ref
  (Ontology.legalSource
    (Ontology.stableId "source:Pabai:[2025]FCA796")
    Negligence.auCommonLawSystem
    Ontology.caseLaw
    "Pabai v Commonwealth of Australia (No 2) [2025] FCA 796"
    "2025"
    "Australia / Federal Court")
  "Federal Court of Australia"
  "Pabai v Commonwealth of Australia (No 2)"
  "[2025] FCA 796"

------------------------------------------------------------------------
-- MABO: computed positive route.
--
-- The finite fixture encodes the known-positive structural calibration:
-- sovereignty yields radical title, not automatic beneficial ownership of all
-- land; pre-existing native title can survive subject to the encoded
-- recognition/non-extinguishment premises. This is DASHI reconstruction of the
-- route, not a claim that the following two rules are verbatim judicial tests.
------------------------------------------------------------------------

maboSovereignty : Algebra.LegalProposition
maboSovereignty = Algebra.legal-proposition
  (Ontology.stableId "prop:Mabo:sovereignty-acquired")
  Algebra.institutionalConstraint
  (Ontology.stableId "actor:Crown")
  (Ontology.stableId "territory:Australia")
  maboSystem
  "Crown sovereignty is treated as acquired for municipal-law purposes"

maboRadicalTitle : Algebra.LegalProposition
maboRadicalTitle = Algebra.legal-proposition
  (Ontology.stableId "prop:Mabo:radical-title")
  Algebra.doctrinalPredicate
  (Ontology.stableId "actor:Crown")
  (Ontology.stableId "territory:Australia")
  maboSystem
  "acquisition of sovereignty carries radical title"

maboPreExistingNativeTitle : Algebra.LegalProposition
maboPreExistingNativeTitle = Algebra.legal-proposition
  (Ontology.stableId "prop:Mabo:pre-existing-native-title")
  Algebra.factualFeature
  (Ontology.stableId "community:Meriam")
  (Ontology.stableId "land:Murray-Islands")
  maboSystem
  "pre-existing native title rights/interests are established for the fixture"

maboNotExtinguished : Algebra.LegalProposition
maboNotExtinguished = Algebra.legal-proposition
  (Ontology.stableId "prop:Mabo:not-extinguished")
  Algebra.doctrinalPredicate
  (Ontology.stableId "community:Meriam")
  (Ontology.stableId "land:Murray-Islands")
  maboSystem
  "the relevant native title has not been validly extinguished for the fixture"

maboSurvival : Algebra.LegalProposition
maboSurvival = Algebra.legal-proposition
  (Ontology.stableId "prop:Mabo:native-title-survives")
  Algebra.doctrinalPredicate
  (Ontology.stableId "community:Meriam")
  (Ontology.stableId "land:Murray-Islands")
  maboSystem
  "pre-existing native title survives recognition in Australian common law"

maboRadicalTitleRule : Algebra.LegalRule
maboRadicalTitleRule = Algebra.legal-rule
  (Ontology.stableId "rule:Mabo:sovereignty-to-radical-title")
  (maboSovereignty ∷ [])
  maboRadicalTitle
  [] []
  maboSource Algebra.bindingRatioRole
  "from 1992-06-03"
  "Australia / High Court common law"

maboSurvivalRule : Algebra.LegalRule
maboSurvivalRule = Algebra.legal-rule
  (Ontology.stableId "rule:Mabo:survival")
  (maboRadicalTitle ∷ maboPreExistingNativeTitle ∷ maboNotExtinguished ∷ [])
  maboSurvival
  [] []
  maboSource Algebra.dashReconstructionRole
  "Mabo calibration"
  "Australia / native-title fixture"

maboGraph : Algebra.LegalGraph
maboGraph = Algebra.legal-graph
  (maboRadicalTitleRule ∷ maboSurvivalRule ∷ [])
  (maboSource ∷ [])

maboFacts : Algebra.FactSet
maboFacts = Algebra.fact-set
  (maboSovereignty ∷ maboPreExistingNativeTitle ∷ maboNotExtinguished ∷ [])

maboComputedReachable :
  Search.reachable 2 maboGraph maboFacts maboSurvival ≡ true
maboComputedReachable = refl

maboComputedMinimalCut :
  Search.searchMinimalCut 2 maboGraph maboFacts maboSurvival
  ≡ Search.found (Search.ruleKey maboSurvivalRule ∷ [])
maboComputedMinimalCut = refl

maboLegacyCalibrationAgreesOnReachability :
  LegacyCut.reachableUnderCurrentAuthorities LegacyCut.maboPositiveCalibration ≡ true
maboLegacyCalibrationAgreesOnReachability = refl

maboFixtureRetainsKnownFoothold :
  MaboFoothold.resultAlreadyEstablished MaboFoothold.maboKnownPositive ≡ true
maboFixtureRetainsKnownFoothold = refl

------------------------------------------------------------------------
-- PABAI: computed currently blocked route plus an ordered transformation search.
--
-- The core-policy defeater here is an executable DASHI reconstruction of the
-- current no-duty obstruction surface. It is not promoted to a universal rule
-- that all government policy defeats every duty claim.
------------------------------------------------------------------------

pabaiForeseeability : Algebra.LegalProposition
pabaiForeseeability = Negligence.compileDutyIssue Climate.reasonableForeseeability

pabaiKnowledge : Algebra.LegalProposition
pabaiKnowledge = Negligence.compileDutyIssue Climate.knowledge

pabaiControl : Algebra.LegalProposition
pabaiControl = Negligence.compileDutyIssue Climate.control

pabaiCorePolicy : Algebra.LegalProposition
pabaiCorePolicy = Negligence.compileDutyIssue Climate.coreGovernmentPolicy

pabaiDutyRule : Algebra.LegalRule
pabaiDutyRule = Algebra.legal-rule
  (Ontology.stableId "rule:Pabai:candidate-duty-with-core-policy-defeater")
  (pabaiForeseeability ∷ pabaiKnowledge ∷ pabaiControl ∷ [])
  Negligence.dutyProposition
  []
  (pabaiCorePolicy ∷ [])
  pabaiSource Algebra.dashReconstructionRole
  "Pabai current-route calibration"
  "Australia / Commonwealth climate-duty candidate"

pabaiGraph : Algebra.LegalGraph
pabaiGraph = Algebra.legal-graph (pabaiDutyRule ∷ []) (pabaiSource ∷ [])

pabaiFacts : Algebra.FactSet
pabaiFacts = Algebra.fact-set
  (pabaiForeseeability ∷ pabaiKnowledge ∷ pabaiControl ∷ pabaiCorePolicy ∷ [])

pabaiComputedCurrentlyUnreachable :
  Search.reachable 1 pabaiGraph pabaiFacts Negligence.dutyProposition ≡ false
pabaiComputedCurrentlyUnreachable = refl

pabaiNarrowedRule : Algebra.LegalRule
pabaiNarrowedRule = Algebra.legal-rule
  (Ontology.stableId "rule:Pabai:reformulated-duty-candidate")
  (pabaiForeseeability ∷ pabaiKnowledge ∷ pabaiControl ∷ [])
  Negligence.dutyProposition
  [] []
  pabaiSource Algebra.dashReconstructionRole
  "counterfactual search candidate only"
  "Australia / reformulated candidate"

pabaiReformulatedGraph : Algebra.LegalGraph
pabaiReformulatedGraph =
  Algebra.legal-graph (pabaiNarrowedRule ∷ []) (pabaiSource ∷ [])

pabaiReformulationCandidate :
  Search.ExecutableTransformationCandidate Negligence.dutyProposition
pabaiReformulationCandidate = Search.executable-transformation-candidate
  "reformulate the encoded duty route so the core-policy proposition is not a categorical defeater"
  pabaiReformulatedGraph
  pabaiFacts

pabaiTransformationSearch :
  Search.firstReopeningTransformation 1 Negligence.dutyProposition
    (pabaiReformulationCandidate ∷ [])
  ≡ Search.found pabaiReformulationCandidate
pabaiTransformationSearch = refl

pabaiLegacyCalibrationAgreesOnCurrentUnreachability :
  LegacyCut.reachableUnderCurrentAuthorities LegacyCut.pabaiNegativeCalibration ≡ false
pabaiLegacyCalibrationAgreesOnCurrentUnreachability = refl

------------------------------------------------------------------------
-- CULLEN: computed public-authority positive-act duty comparator.
------------------------------------------------------------------------

cullenDutyRule : Algebra.LegalRule
cullenDutyRule = Algebra.legal-rule
  (Ontology.stableId "rule:Cullen:positive-operational-duty")
  (Cullen.positiveOperationalAct ∷
   Cullen.foreseeablePhysicalInjuryRisk ∷
   Cullen.statutoryPoliceFunction ∷ [])
  Cullen.cullenDutyProposition
  [] []
  Cullen.cullenSource Algebra.bindingRatioRole
  "from 2026-06-17"
  "Australia / High Court / NSW police operational conduct"

cullenGraph : Algebra.LegalGraph
cullenGraph = Algebra.legal-graph (cullenDutyRule ∷ []) (Cullen.cullenSource ∷ [])

cullenFacts : Algebra.FactSet
cullenFacts = Algebra.fact-set
  (Cullen.positiveOperationalAct ∷
   Cullen.foreseeablePhysicalInjuryRisk ∷
   Cullen.statutoryPoliceFunction ∷
   Cullen.cullenBreachNotEstablished ∷ [])

cullenComputedDutyReachable :
  Search.reachable 1 cullenGraph cullenFacts Cullen.cullenDutyProposition ≡ true
cullenComputedDutyReachable = refl

cullenGenericBreachNotManufactured :
  Search.reachable 1 cullenGraph cullenFacts Negligence.breachProposition ≡ false
cullenGenericBreachNotManufactured = refl

cullenDutyRuleIsComputedMinimalCut :
  Search.searchMinimalCut 1 cullenGraph cullenFacts Cullen.cullenDutyProposition
  ≡ Search.found (Search.ruleKey cullenDutyRule ∷ [])
cullenDutyRuleIsComputedMinimalCut = refl

------------------------------------------------------------------------
-- Cullen vs climate candidate: executable feature mismatch only.
------------------------------------------------------------------------

climateComparatorCase : Precedent.CurrentCase
climateComparatorCase = Precedent.current-case
  (Ontology.stableId "case:climate-duty-comparator")
  Negligence.auCommonLawSystem
  "Australia"
  (Ontology.stableId "issue:negligence:duty-public-authority-positive-act")
  (pabaiForeseeability ∷ pabaiKnowledge ∷ pabaiControl ∷ pabaiCorePolicy ∷ [])

cullenClimateFeatureFitFails :
  Search.precedentFeatureFitCandidate Cullen.cullenDutyHolding climateComparatorCase
  ≡ false
cullenClimateFeatureFitFails = refl

cullenClimateFirstMissingFeature :
  Search.minimalDistinguishingCandidate Cullen.cullenDutyHolding climateComparatorCase
  ≡ Search.found Cullen.positiveOperationalAct
cullenClimateFirstMissingFeature = refl

------------------------------------------------------------------------
-- Regression firewalls.
------------------------------------------------------------------------

data ComputedPabaiCounterfactualIsCurrentLaw : Set where
data CullenFeatureMismatchProvesClimateNoDuty : Set where
data MaboExecutableGraphIsVerbatimJudgmentAlgorithm : Set where

pabaiCounterfactualDoesNotBecomeLaw : ComputedPabaiCounterfactualIsCurrentLaw → ⊥
pabaiCounterfactualDoesNotBecomeLaw ()

cullenMismatchDoesNotDecideClimateDuty : CullenFeatureMismatchProvesClimateNoDuty → ⊥
cullenMismatchDoesNotDecideClimateDuty ()

maboSearchGraphDoesNotClaimVerbatimAlgorithm :
  MaboExecutableGraphIsVerbatimJudgmentAlgorithm → ⊥
maboSearchGraphDoesNotClaimVerbatimAlgorithm ()
