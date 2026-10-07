module DASHI.Governance.BoloBoloModelClassRobustnessExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloCalibrationTransferExact as Transfer
import DASHI.Governance.BoloBoloPracticalSignificanceExact as Significance

------------------------------------------------------------------------
-- MODEL-CLASS ROBUSTNESS.
--
-- Even target-qualified, validated evidence may be fragile to the chosen cost
-- mapping.  This owner therefore makes model sensitivity explicit: an
-- admissible model family must be fixed before target outcomes, and a uniform
-- meaningful advantage means the meaningful-margin result holds for every
-- model in that declared family.
------------------------------------------------------------------------

record AdmissibleModelFamily : Set₁ where
  constructor admissibleModelFamily
  field
    Index : Set
    model : Index → Comparison.CounterfactualCoordinationCostModel
    targetEvidence :
      (i : Index) → Transfer.BoloTargetBoundEvidence (model i)

open AdmissibleModelFamily public

record UniformMeaningfulAdvantage
  (threshold : Nat)
  (family : AdmissibleModelFamily) : Set where
  constructor uniformMeaningfulAdvantage
  field
    everyAdmissibleModelWins :
      (i : Index family) →
      Significance.RobustMeaningfulWin
        threshold
        (Transfer.targetBounds (targetEvidence family i))

open UniformMeaningfulAdvantage public

record UniformMeaningfulDisadvantage
  (threshold : Nat)
  (family : AdmissibleModelFamily) : Set where
  constructor uniformMeaningfulDisadvantage
  field
    everyAdmissibleModelLoses :
      (i : Index family) →
      Significance.RobustMeaningfulLoss
        threshold
        (Transfer.targetBounds (targetEvidence family i))

open UniformMeaningfulDisadvantage public

uniformMeaningfulAdvantageImpliesPerModelMargin :
  ∀ {threshold family} →
  UniformMeaningfulAdvantage threshold family →
  (i : Index family) →
  Significance.MeaningfulOrderImprovement threshold (model family i)
uniformMeaningfulAdvantageImpliesPerModelMargin certificate i =
  Significance.robustMeaningfulWinImpliesMargin
    (Transfer.targetBounds (targetEvidence _ i))
    (everyAdmissibleModelWins certificate i)

uniformMeaningfulDisadvantageImpliesPerModelMargin :
  ∀ {threshold family} →
  UniformMeaningfulDisadvantage threshold family →
  (i : Index family) →
  Significance.MeaningfulOrderLoss threshold (model family i)
uniformMeaningfulDisadvantageImpliesPerModelMargin certificate i =
  Significance.robustMeaningfulLossImpliesMargin
    (Transfer.targetBounds (targetEvidence _ i))
    (everyAdmissibleModelLoses certificate i)

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record ModelClassRobustnessBoundary : Set where
  constructor modelClassRobustnessBoundary
  field
    admissibleModelFamilyMustBePredeclared : Bool
    singleFavouredModelEstablishesFamilyRobustness : Bool
    outcomeDependentModelFamilySelectionAllowed : Bool
    failureInOneAdmissibleModelBlocksUniformAdvantage : Bool
    uniformMeaningfulAdvantageCreatesUniversalPoliticalOptimality : Bool
    uniformMeaningfulDisadvantageRefutesEveryPossibleGovernanceModel : Bool

open ModelClassRobustnessBoundary public

canonicalModelClassRobustnessBoundary : ModelClassRobustnessBoundary
canonicalModelClassRobustnessBoundary =
  modelClassRobustnessBoundary true false false true false false

canonicalModelClassRobustnessReceipt : GenericReceipt.GenericReceipt
canonicalModelClassRobustnessReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo predeclared model-class robustness"
    "DASHI.Governance.BoloBoloModelClassRobustnessExact"
    "UniformMeaningfulAdvantage / UniformMeaningfulDisadvantage / canonicalModelClassRobustnessBoundary"
    "adds a model-sensitivity layer above target-qualified meaningful bounds: a predeclared admissible family carries its own target evidence for each cost model, and uniform advantage or disadvantage requires the meaningful-margin result for every model in that family"
    "one favoured cost mapping is not family robustness, the admissible family may not be chosen after observing outcomes, and even uniform coordination advantage across that family creates neither universal political optimality nor legitimacy"
    "agda -i . DASHI/Governance/BoloBoloModelClassRobustnessRegression.agda"
