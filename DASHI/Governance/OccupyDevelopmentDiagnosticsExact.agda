module DASHI.Governance.OccupyDevelopmentDiagnosticsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- DEVELOPMENT-ONLY DURATION DIAGNOSTICS.
--
-- Reproducibility script:
--   scripts/occupy_governance_development_diagnostics.py
--
-- The six rows are development records only. No protected holdout record is
-- inspected by this diagnostic. MAE values are stored in thousandths of a
-- minute, rounded from the script output.
------------------------------------------------------------------------

record DurationModelDiagnostic : Set where
  constructor durationModelDiagnostic
  field
    modelLabel : String
    looMAEThousandths : Nat

open DurationModelDiagnostic public

interceptBaseline : DurationModelDiagnostic
interceptBaseline = durationModelDiagnostic "intercept-only mean-duration baseline" 172667

wordCountModel : DurationModelDiagnostic
wordCountModel = durationModelDiagnostic "normalized word count: univariate OLS" 218451

consensusLexemeModel : DurationModelDiagnostic
consensusLexemeModel = durationModelDiagnostic "consensus-paragraph count: univariate OLS" 210837

blockLexemeModel : DurationModelDiagnostic
blockLexemeModel = durationModelDiagnostic "block-paragraph count: univariate OLS" 213011

proposalLexemeModel : DurationModelDiagnostic
proposalLexemeModel = durationModelDiagnostic "proposal-paragraph count: univariate OLS" 208141

anonymisationMarkerModel : DurationModelDiagnostic
anonymisationMarkerModel = durationModelDiagnostic "anonymisation-marker count: univariate OLS" 317659

canonicalDurationDiagnostics : List DurationModelDiagnostic
canonicalDurationDiagnostics =
  interceptBaseline
  ∷ wordCountModel
  ∷ consensusLexemeModel
  ∷ blockLexemeModel
  ∷ proposalLexemeModel
  ∷ anonymisationMarkerModel
  ∷ []

record DevelopmentDiagnosticBoundary : Set where
  constructor developmentDiagnosticBoundary
  field
    developmentDurationRowsUsed : Nat
    protectedHoldoutConsumedByDiagnostics : Bool
    primaryGateRequiresBeatingInterceptLOOMAE : Bool
    nontrivialDurationModelPassesDevelopmentGate : Bool
    multivariateModelPromotedFromSixRows : Bool
    durationPredictionEqualsCoordinationBurden : Bool
    lexicalCountsBecomeSemanticDecisionCounts : Bool
    negativeDevelopmentResultPreservesHoldout : Bool

open DevelopmentDiagnosticBoundary public

canonicalDevelopmentDiagnosticBoundary : DevelopmentDiagnosticBoundary
canonicalDevelopmentDiagnosticBoundary =
  developmentDiagnosticBoundary 6 false true false false false false true

canonicalOccupyDevelopmentDiagnosticReceipt : GenericReceipt.GenericReceipt
canonicalOccupyDevelopmentDiagnosticReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "development-only OWS duration-model diagnostic gate"
    "DASHI.Governance.OccupyDevelopmentDiagnosticsExact"
    "canonicalDevelopmentDiagnosticBoundary"
    "compares an intercept-only duration baseline against five predeclared one-predictor lexical ordinary-least-squares models using leave-one-out mean absolute error on the six source-explicit development duration rows; every nontrivial candidate performs worse than the intercept baseline"
    "the negative development result is not a burden or causal estimate; no multivariate model is promoted from six rows, no lexical count is reinterpreted semantically, and the protected prospective holdout remains unread"
    "python3 scripts/occupy_governance_development_diagnostics.py && agda -i . DASHI/Governance/OccupyDevelopmentDiagnosticsRegression.agda"
