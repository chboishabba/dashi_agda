module DASHI.Governance.BoloBoloPolycentricEvidenceSynthesisExact where

open import DASHI.Core.Prelude

import DASHI.Core.CriticalRelationalGrammarSourceRegistryExact as Registry
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- EMPIRICAL POLYCENTRIC-GOVERNANCE SYNTHESIS.
--
-- This is independent literature evidence about polycentric governance, not a
-- theorem about p.m.'s design and not an empirical bolo cost model.
------------------------------------------------------------------------

baldwinEtAl2024Source : Registry.SourceReference
baldwinEtAl2024Source = Registry.source-reference
  "Elizabeth Baldwin; Andreas Thiel; Michael McGinnis; Elke Kellner"
  "Empirical research on polycentric governance: Critical gaps and a framework for studying long-term change"
  "Policy Studies Journal 52(2):319-348"
  2024
  "10.1111/psj.12518"
  "systematic empirical-literature review"
  "review of empirical polycentric-governance research showing both positive and negative features in practice, substantial context dependence, weak concept/variable standardization and limited longitudinal evidence; not a bolo effect estimate"

record PolycentricEvidenceSynthesis : Set where
  constructor polycentricEvidenceSynthesis
  field
    initialEmpiricalPeerReviewedArticleCount : Nat
    coreFunctioningPerformanceArticleCount : Nat
    positiveFeaturesObservedInLiterature : Bool
    negativeFeaturesObservedInLiterature : Bool
    polycentricityIsEmpiricalPanacea : Bool
    sharedCrossStudyVariableLanguageAlreadyAdequate : Bool
    contextOftenUnderSpecified : Bool
    longTermChangeEvidenceLimited : Bool
    crossCaseTransportNeedsQualification : Bool
    directBoloCostBoundPaid : Bool

open PolycentricEvidenceSynthesis public

canonicalPolycentricEvidenceSynthesis : PolycentricEvidenceSynthesis
canonicalPolycentricEvidenceSynthesis =
  polycentricEvidenceSynthesis
    179 112 true true false false true true true false

canonicalPolycentricEvidenceSynthesisReceipt : GenericReceipt.GenericReceipt
canonicalPolycentricEvidenceSynthesisReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "empirical polycentric-governance evidence synthesis"
    "DASHI.Governance.BoloBoloPolycentricEvidenceSynthesisExact"
    "canonicalPolycentricEvidenceSynthesis"
    "records the Baldwin-Thiel-McGinnis-Kellner review's 179-paper empirical sample and 112-paper core functioning/performance subset together with its central finding that empirical polycentric governance exhibits both positive and negative features and remains difficult to compare across contexts because shared concepts, contextual specification and longitudinal evidence are limited"
    "this literature synthesis strengthens DASHI transfer/model-robustness obligations but does not make polycentricity a panacea, identify a bolo cost coefficient or turn independent empirical studies into evidence authored by p.m."
    "agda -i . DASHI/Governance/BoloBoloPolycentricEvidenceSynthesisRegression.agda"
