module DASHI.Physics.Closure.NSTriadKNFactoredFullAnalyticFrontierRound566Exact where

------------------------------------------------------------------------
-- ROUND566 / RECONCILE THE OLD HEAT/RESOLVENT FRONTIER WITH THE NEW DIRECT
-- FACTORED-FULL NORMAL FORM
--
-- R442 historically left two analytic coordinates on the direct companion
-- route:
--
--   (1) realize the Cauchy resolvent by a heat/Laplace representation;
--   (2) prove the signed spacetime payment.
--
-- R541-R547 changed the least-privilege picture.  The literal nonseparable
-- spectator weight is already an R294 swap-invariant weight for each fixed
-- spectator, so the complete pre-norm cancellation and full-square normal form
-- can be carried out directly with the Cauchy resolvent.  No heat/Laplace
-- representation is needed to reach
--
--   FactoredFull = Diagonal + 2 * LiteralR406Remainder.
--
-- R548-R565 then reduce the diagonal to a favourable self-Gram term plus a
-- literal global self-flux derivative and reconcile the two temporal compiler
-- generations.  Hence the old heat realization remains a useful alternative
-- producer route, but is no longer a mandatory coordinate of the shortest
-- leaf-A proof.
--
-- The remaining direct analytic coordinates are now exactly:
--
--   A2-standard : ordinary scalar FTC for the already-constructed global
--                 self-flux derivative;
--   A1-novel    : cutoff-uniform spacetime upper control of the literal live
--                 global `factoredFull` observable from R556/R557.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNDirectSignedCompanionFrontierRound442Exact as R442
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorDoubleForcingCommutatorFoldRound542Exact as R542
import DASHI.Physics.Closure.NSTriadKNSpectatorDoubleCellAmplitudeFoldRound544Exact as R544
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNLiteralR406CommutatorDiagonalNormalFormRound547Exact as R547
import DASHI.Physics.Closure.NSTriadKNSelfFluxTemporalReconciliationRound565Exact as R565
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

------------------------------------------------------------------------
-- Canonical direct-route residual order.
------------------------------------------------------------------------

data R566Residual : Set where
  missingOrdinaryScalarFTC566 : R566Residual
  missingLiteralFactoredFullSpacetimeUpper566 : R566Residual
  literalLeafAClosed566 : R566Residual

currentR566Residual : R566Residual
currentR566Residual = missingOrdinaryScalarFTC566

afterScalarFTC566 : R566Residual
afterScalarFTC566 = missingLiteralFactoredFullSpacetimeUpper566

------------------------------------------------------------------------
-- Route reconciliation / no-collapse boundaries.
------------------------------------------------------------------------

round566OldHeatLaplaceRouteStillAvailable : Bool
round566OldHeatLaplaceRouteStillAvailable =
  R442.round442R423ConsumerReadyModuloTwoAnalyticCoordinates

round566HeatLaplaceRealizationMandatoryForDirectR547Route : Bool
round566HeatLaplaceRealizationMandatoryForDirectR547Route = false

round566SpectatorCauchyWeightAlreadyR294Compatible : Bool
round566SpectatorCauchyWeightAlreadyR294Compatible = true

round566PreNormCommutatorFoldClosed : Bool
round566PreNormCommutatorFoldClosed =
  R542.round542R294CommutatorFoldWeldClosed

round566AmplitudeFoldNormalizationClosed : Bool
round566AmplitudeFoldNormalizationClosed =
  R544.round544WeightedDoubleCellFoldNormalizationClosed

round566SpectatorRowFactorizationClosed : Bool
round566SpectatorRowFactorizationClosed =
  R545.round545LiteralSpectatorRowFactorizationClosed

round566LiteralR406NormalFormClosed : Bool
round566LiteralR406NormalFormClosed =
  R547.round547LiteralFixedOutputNormalFormClosed

round566NSpecificSelfFluxDifferentiationClosed : Bool
round566NSpecificSelfFluxDifferentiationClosed =
  R565.round565NSDerivativeConstructionClosed

round566ConcreteScalarFTCInstalled : Bool
round566ConcreteScalarFTCInstalled =
  R565.round565ConcreteScalarFTCInhabitantInstalled

round566LiteralFactoredFullSpacetimeUpperClosed : Bool
round566LiteralFactoredFullSpacetimeUpperClosed = false

-- R301/heat-Schur may still be used as a producer for compatible pieces, but
-- the direct R547 consumer does not descend through that route by necessity.
round566HeatSchurMandatoryForFactoredFull : Bool
round566HeatSchurMandatoryForFactoredFull = false

round566CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round566CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round566ClayPromotion : Bool
round566ClayPromotion = false

round566HeatLaplaceRealizationMandatoryForDirectR547RouteIsFalse :
  round566HeatLaplaceRealizationMandatoryForDirectR547Route ≡ false
round566HeatLaplaceRealizationMandatoryForDirectR547RouteIsFalse = refl

round566PreNormCommutatorFoldClosedIsTrue :
  round566PreNormCommutatorFoldClosed ≡ true
round566PreNormCommutatorFoldClosedIsTrue =
  R542.round542R294CommutatorFoldWeldClosedIsTrue

round566LiteralR406NormalFormClosedIsTrue :
  round566LiteralR406NormalFormClosed ≡ true
round566LiteralR406NormalFormClosedIsTrue =
  R547.round547LiteralFixedOutputNormalFormClosedIsTrue

round566HeatSchurMandatoryForFactoredFullIsFalse :
  round566HeatSchurMandatoryForFactoredFull ≡ false
round566HeatSchurMandatoryForFactoredFullIsFalse = refl

round566ClayPromotionIsFalse : round566ClayPromotion ≡ false
round566ClayPromotionIsFalse = refl
