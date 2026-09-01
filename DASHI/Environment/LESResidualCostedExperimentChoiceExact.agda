module DASHI.Environment.LESResidualCostedExperimentChoiceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.CostedResidualInformationChoiceExact as Costed
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis

------------------------------------------------------------------------
-- LES experiment bundles as costed residual-information moves.
-- Bundle cost is reused literally from DiscriminatorSynthesisExact; only the
-- certified residual gain remains application/experiment-design supplied.
------------------------------------------------------------------------

record LESResidualExperimentMove
    {mechanism : Basis.DomainMechanismSocket}
    (bundle : Synthesis.ExperimentBundle (Basis.State mechanism)) : Set₁ where
  constructor lesResidualExperimentMove
  field
    prior : Bidi.ResidualFibre (Basis.State mechanism)
    posterior : Bidi.ResidualFibre (Basis.State mechanism)
    refinement : Bidi.FibreRefines posterior prior
    certifiedGain : Nat
    gainCertificateReference : String
    residualInterpretationReference : String
    admissibilityReference : String

open LESResidualExperimentMove public

asCostedResidualMove :
  ∀ {mechanism}
    {bundle : Synthesis.ExperimentBundle (Basis.State mechanism)} →
  LESResidualExperimentMove bundle →
  Costed.ResidualInformationMove (Basis.State mechanism)
asCostedResidualMove {bundle = bundle} move = Costed.residualInformationMove
  (prior move)
  (posterior move)
  (refinement move)
  Costed.measurementResidualMove
  (Synthesis.cost bundle)
  (certifiedGain move)
  (Synthesis.bundleReference bundle)
  (gainCertificateReference move)
  (Synthesis.calibrationReference bundle)
  (admissibilityReference move)
  (residualInterpretationReference move)

record LESResidualCostedChoiceBoundary : Set where
  constructor lesResidualCostedChoiceBoundary
  field
    LESBundleCostIsReusedRatherThanReinvented : Bool
    LESBundleCostIsReusedRatherThanReinventedIsTrue :
      LESBundleCostIsReusedRatherThanReinvented ≡ true
    residualGainIsInferredFromCostAlone : Bool
    residualGainIsInferredFromCostAloneIsFalse :
      residualGainIsInferredFromCostAlone ≡ false
    partialExperimentProgressCanEnterCostedSelection : Bool
    partialExperimentProgressCanEnterCostedSelectionIsTrue :
      partialExperimentProgressCanEnterCostedSelection ≡ true

canonicalLESResidualCostedChoiceBoundary : LESResidualCostedChoiceBoundary
canonicalLESResidualCostedChoiceBoundary =
  lesResidualCostedChoiceBoundary true refl false refl true refl
