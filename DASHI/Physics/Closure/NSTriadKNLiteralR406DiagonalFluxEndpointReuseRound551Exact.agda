module DASHI.Physics.Closure.NSTriadKNLiteralR406DiagonalFluxEndpointReuseRound551Exact where

------------------------------------------------------------------------
-- ROUND551 / REUSE THE EXISTING R393 TEMPORAL ENDPOINT AUTHORITY
--
-- R549-R550 reduce the R547 diagonal to
--
--   Diagonal = SelfGram + SelfFluxTangent,
--
-- and pay the SelfGram term by the existing physical energy-square estimate.
-- The remaining diagonal coordinate is therefore temporal: integrate the
-- literal self-pair weighted Gram-flux tangent and realize it as an endpoint.
--
-- R393 already owns exactly the required analytic authority shape for a
-- rational-valued flux/tangent pair: one interval integral plus the endpoint
-- fundamental theorem.  This module does NOT introduce a second integration
-- interface.  It asks only for same-object welds identifying the R549 self flux
-- and self-flux tangent with the corresponding R393 temporal carrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLiteralR378TemporalIntegrationBoundaryRound393Exact as R393
import DASHI.Physics.Closure.NSTriadKNLiteralR406DiagonalR290FluxDecompositionRound549Exact as R549
import DASHI.Physics.Closure.NSTriadKNLiteralR406DiagonalSelfGramEnergyControlRound550Exact as R550
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

------------------------------------------------------------------------
-- 1. Same-object temporal weld.
------------------------------------------------------------------------

record LiteralSelfFluxTemporalWeld551
    {t : Level} {Time : Set t}
    (temporal : R393.LiteralR378TemporalRealization Time)
    (selfFlux selfFluxTangent : Time → ℚ) : Set (lsuc t) where
  constructor literal-self-flux-temporal-weld-551
  field
    selfFluxIsR393Flux551 :
      (τ : Time) →
      selfFlux τ ≡ R393.literalOffDiagonalFlux temporal τ

    selfFluxTangentIsR393Tangent551 :
      (τ : Time) →
      selfFluxTangent τ ≡ R393.literalOffDiagonalFluxTangent temporal τ

open LiteralSelfFluxTemporalWeld551 public

------------------------------------------------------------------------
-- 2. Existing R393 FTC transported onto the literal self-flux carrier.
------------------------------------------------------------------------

selfFluxEndpointFundamentalTheorem551 :
  ∀ {t} {Time : Set t}
    (temporal : R393.LiteralR378TemporalRealization Time)
    (selfFlux selfFluxTangent : Time → ℚ) →
    LiteralSelfFluxTemporalWeld551 temporal selfFlux selfFluxTangent →
    R393.Integral temporal selfFluxTangent
    ≡ selfFlux (R393.finalTime temporal)
      - selfFlux (R393.initialTime temporal)
selfFluxEndpointFundamentalTheorem551
    temporal selfFlux selfFluxTangent weld =
  trans
    (R393.integralCongruence temporal
      (selfFluxTangentIsR393Tangent551 weld))
    (trans
      (R393.offDiagonalFundamentalTheorem temporal)
      (cong₂ _-_
        (sym (selfFluxIsR393Flux551 weld (R393.finalTime temporal)))
        (sym (selfFluxIsR393Flux551 weld (R393.initialTime temporal)))))
  where
  open import Data.Rational.Base using (_-_)
  open import Relation.Binary.PropositionalEquality using (cong₂)

------------------------------------------------------------------------
-- 3. What remains after reuse.
--
-- The analytic FTC schema is no longer a new proof-search family.  The live
-- task is to instantiate selfFlux/selfFluxTangent on the time-indexed literal
-- R549 physical carrier and prove the two same-object equalities above.
------------------------------------------------------------------------

data R551Residual : Set where
  missingLiteralSelfFluxTrajectoryWeld551 : R551Residual
  missingFactoredFullSpacetimeBound551 : R551Residual
  literalLeafAFromNormalFormClosed551 : R551Residual

currentR551Residual : R551Residual
currentR551Residual = missingLiteralSelfFluxTrajectoryWeld551

round551ReusesExistingR393IntegrationAuthority : Bool
round551ReusesExistingR393IntegrationAuthority = true

round551IntroducesNewFTCInterface : Bool
round551IntroducesNewFTCInterface = false

round551SelfGramEnergyControlAlreadyClosed : Bool
round551SelfGramEnergyControlAlreadyClosed =
  R550.round550SelfGramEnergySquareControlClosed

round551EndpointTheoremClosedGivenSameObjectWeld : Bool
round551EndpointTheoremClosedGivenSameObjectWeld = true

round551LiteralSelfFluxTrajectoryWeldClosed : Bool
round551LiteralSelfFluxTrajectoryWeldClosed = false

round551LiteralR406SignedCrossPaymentClosed : Bool
round551LiteralR406SignedCrossPaymentClosed = false

round551CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round551CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round551ClayPromotion : Bool
round551ClayPromotion = false

round551ReusesExistingR393IntegrationAuthorityIsTrue :
  round551ReusesExistingR393IntegrationAuthority ≡ true
round551ReusesExistingR393IntegrationAuthorityIsTrue = refl

round551IntroducesNewFTCInterfaceIsFalse :
  round551IntroducesNewFTCInterface ≡ false
round551IntroducesNewFTCInterfaceIsFalse = refl

round551EndpointTheoremClosedGivenSameObjectWeldIsTrue :
  round551EndpointTheoremClosedGivenSameObjectWeld ≡ true
round551EndpointTheoremClosedGivenSameObjectWeldIsTrue = refl

round551ClayPromotionIsFalse : round551ClayPromotion ≡ false
round551ClayPromotionIsFalse = refl
