module DASHI.Law.HerzogColonialConcreteRefinementParetoRerunExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawLegalGraphRefinementReopeningExact as Refinement
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Law.HerzogColonialWrongTypeCrossSystemBridgeExact as Cross
import DASHI.Law.HerzogColonialWrongTypeElementRequirementExact as Element
import DASHI.Law.HerzogColonialWrongTypeGenericParetoFrontierBridgeExact as HerzogPareto

emptyHerzogAnalyticalGraph : Algebra.LegalGraph
emptyHerzogAnalyticalGraph = Algebra.legal-graph [] []

stage0Facts : Algebra.FactSet
stage0Facts = Algebra.fact-set []

stage1Facts : Algebra.FactSet
stage1Facts = Algebra.fact-set (Cross.modernAuthorityErasureObserved ∷ [])

stage2Facts : Algebra.FactSet
stage2Facts = Algebra.fact-set
  (Cross.authorityErasureOperationalPrerequisite ∷
   Cross.modernAuthorityErasureObserved ∷ [])

emptyGraphPreserved :
  Refinement.GraphRefinement emptyHerzogAnalyticalGraph emptyHerzogAnalyticalGraph
emptyGraphPreserved = Refinement.graph-refinement
  (λ { () })
  (λ { () })
  "no analytical rule added by translation-state refinement"
  "no municipal legal authority source added by translation-state refinement"

stage0To1FactRefinement : Refinement.FactRefinement stage0Facts stage1Facts
stage0To1FactRefinement = Refinement.fact-refinement
  (λ { () })
  "translation-state fact: modern authority-erasure meaning coordinate closed"

preserveStage1Fact :
  ∀ {p} →
  Algebra._∈_ p (Algebra.facts stage1Facts) →
  Algebra._∈_ p (Algebra.facts stage2Facts)
preserveStage1Fact Algebra.here = Algebra.there Algebra.here
preserveStage1Fact (Algebra.there ())

stage1To2FactRefinement : Refinement.FactRefinement stage1Facts stage2Facts
stage1To2FactRefinement = Refinement.fact-refinement
  preserveStage1Fact
  "translation-state fact: operational-power-prerequisite coordinate closed"

stage0To1Receipt :
  Refinement.LegalRefinementReceipt
    emptyHerzogAnalyticalGraph emptyHerzogAnalyticalGraph stage0Facts stage1Facts
stage0To1Receipt = Refinement.legal-refinement-receipt
  emptyGraphPreserved
  stage0To1FactRefinement
  Residual.missingRelationalFeature
  Residual.obtainFactualEvidence
  Refinement.factCarrier
  true refl
  true refl

stage1To2Receipt :
  Refinement.LegalRefinementReceipt
    emptyHerzogAnalyticalGraph emptyHerzogAnalyticalGraph stage1Facts stage2Facts
stage1To2Receipt = Refinement.legal-refinement-receipt
  emptyGraphPreserved
  stage1To2FactRefinement
  Residual.missingInstitutionalConstraint
  Residual.inspectJudicialReasons
  Refinement.factCarrier
  true refl
  true refl

authorityMeaningFactPresentAtStage1 :
  Algebra._∈_ Cross.modernAuthorityErasureObserved (Algebra.facts stage1Facts)
authorityMeaningFactPresentAtStage1 = Algebra.here

authorityMeaningFactPreservedAtStage2 :
  Algebra._∈_ Cross.modernAuthorityErasureObserved (Algebra.facts stage2Facts)
authorityMeaningFactPreservedAtStage2 = Algebra.there Algebra.here

powerPrerequisiteFactPresentAtStage2 :
  Algebra._∈_ Cross.authorityErasureOperationalPrerequisite (Algebra.facts stage2Facts)
powerPrerequisiteFactPresentAtStage2 = Algebra.here

stage0Frontier :
  Pareto.paretoFrontier HerzogPareto.currentPortfolio
  ≡ HerzogPareto.currentAuthorityCell ∷ []
stage0Frontier = HerzogPareto.currentParetoFrontierIsAuthorityOnly

stage1Frontier :
  Pareto.paretoFrontier HerzogPareto.afterAuthorityPortfolio
  ≡ HerzogPareto.afterAuthorityPowerCell ∷ []
stage1Frontier = HerzogPareto.afterAuthorityParetoFrontierIsPowerOnly

stage2Frontier :
  Pareto.paretoFrontier HerzogPareto.afterPowerPortfolio
  ≡ HerzogPareto.afterPowerIncidentCell ∷ []
stage2Frontier = HerzogPareto.afterPowerParetoFrontierIsIncidentOnly

authorityAndPowerRequirementsDiffer :
  Pareto.requirement HerzogPareto.currentAuthorityCell
  ≡ Pareto.requirement HerzogPareto.afterAuthorityPowerCell
  → ⊥
authorityAndPowerRequirementsDiffer ()

powerAndIncidentRequirementsDiffer :
  Pareto.requirement HerzogPareto.afterAuthorityPowerCell
  ≡ Pareto.requirement HerzogPareto.afterPowerIncidentCell
  → ⊥
powerAndIncidentRequirementsDiffer ()

record HerzogConcreteRerunChain : Set where
  constructor herzog-concrete-rerun-chain
  field
    firstRefinement :
      Refinement.LegalRefinementReceipt
        emptyHerzogAnalyticalGraph emptyHerzogAnalyticalGraph stage0Facts stage1Facts
    secondRefinement :
      Refinement.LegalRefinementReceipt
        emptyHerzogAnalyticalGraph emptyHerzogAnalyticalGraph stage1Facts stage2Facts
    firstFrontier :
      Pareto.paretoFrontier HerzogPareto.currentPortfolio
      ≡ HerzogPareto.currentAuthorityCell ∷ []
    secondFrontier :
      Pareto.paretoFrontier HerzogPareto.afterAuthorityPortfolio
      ≡ HerzogPareto.afterAuthorityPowerCell ∷ []
    thirdFrontier :
      Pareto.paretoFrontier HerzogPareto.afterPowerPortfolio
      ≡ HerzogPareto.afterPowerIncidentCell ∷ []
    firstCoordinateChanged :
      Pareto.requirement HerzogPareto.currentAuthorityCell
      ≡ Pareto.requirement HerzogPareto.afterAuthorityPowerCell
      → ⊥
    secondCoordinateChanged :
      Pareto.requirement HerzogPareto.afterAuthorityPowerCell
      ≡ Pareto.requirement HerzogPareto.afterPowerIncidentCell
      → ⊥

open HerzogConcreteRerunChain public

herzogConcreteRerunChain : HerzogConcreteRerunChain
herzogConcreteRerunChain = herzog-concrete-rerun-chain
  stage0To1Receipt
  stage1To2Receipt
  stage0Frontier
  stage1Frontier
  stage2Frontier
  authorityAndPowerRequirementsDiffer
  powerAndIncidentRequirementsDiffer

data TranslationStateFactCreatesHistoricalIdentity : Set where
data TranslationStateFactCreatesMunicipalLiability : Set where
data FrontierAdvanceProvesAnalyticalWrongTypeApplicable : Set where

translationStateDoesNotCreateHistoricalIdentity :
  TranslationStateFactCreatesHistoricalIdentity → ⊥
translationStateDoesNotCreateHistoricalIdentity ()

translationStateDoesNotCreateMunicipalLiability :
  TranslationStateFactCreatesMunicipalLiability → ⊥
translationStateDoesNotCreateMunicipalLiability ()

frontierAdvanceDoesNotAutoApplyWrongType :
  FrontierAdvanceProvesAnalyticalWrongTypeApplicable → ⊥
frontierAdvanceDoesNotAutoApplyWrongType ()
