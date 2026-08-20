module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound55LiteralG1BetaBoxesValidation where

------------------------------------------------------------------------
-- ROUND 55 FOCUSED VALIDATION ROOT
--
-- This root advances only the shortest finite/source-specific fronts.
--
-- G1:
--   actual one-leg Frechet derivatives
--     D_X log(exp X exp Y)|_0 = J_+(Y)
--     D_X log(exp Y exp X)|_0 = J_-(Y)
--   + already-proved left/right dexp cancellation
--     -> literal printed equation-(0.11) J_+ Ad_exp centre derivative.
--
-- L3 finite one-loop denominator:
--   generated regular cell
--     -> at least one outer coordinate
--     -> one outer sine-half square floor
--     -> lower bound for the complete four-dimensional hat-momentum sum.
--
-- The repository already contains a constructive Bishop theorem giving the
-- coarse outer-angle gap
--
--   3/4 <= t <= 11/7
--     -> sin t >= 87/128
--     -> (2 sin t)^2 >= 7569/4096.
--
-- Hence the immediate physical bridge is now the exact normalized-momentum
-- conversion q -> t = pi |q| / 2 using 3 < pi < 22/7, followed by the literal
-- Wilson propagator identification.  No 240 independent denominator proofs are
-- required.
--
-- No continuum/OS layer is imported here.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound54FinitePhysicalProducersValidation as R54
import DASHI.Physics.YangMills.BalabanCMP109LiteralPrincipalLogFrechetReductionExact as G1
import DASHI.Physics.YangMills.BalabanCMP109FiniteMatrixLeftRightDexpCancellationExact as G1Cancel
import DASHI.Physics.YangMills.BalabanClayT4RegularGridOuterAxisExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4RegularHatMomentumDenominatorExact as Denominator
import DASHI.Physics.YangMills.BalabanClayT4RegularBoxDenominatorReductionExact as BoxDenominator
import DASHI.Physics.YangMills.BalabanBishopSineTwoBallCubicLowerExact as SineTwoBall
import DASHI.Physics.YangMills.BalabanBishopOuterBrillouinSineGapExact as OuterSine

literalOneLegFrechetReductionLevel =
  G1.cmp109LiteralOneLegFrechetReductionLevel
literalPrincipalLogFrechetAnalyticInputsLevel =
  G1.cmp109LiteralPrincipalLogFrechetAnalyticInputsLevel

leftRightDexpActionCancellationLevel =
  G1Cancel.cmp109FiniteMatrixLeftRightDexpCancellationLevel

regularOuterAxisGeometryLevel = Grid.regularOuterAxisGeometryLevel
regularDenominatorScalarFloorLevel =
  Denominator.regularDenominatorScalarFloorLevel
regularBoxDenominatorReductionLevel =
  BoxDenominator.regularBoxDenominatorReductionLevel
outerNormalizedSineSquareFloorLevel =
  BoxDenominator.outerNormalizedSineSquareFloorLevel

bishopSineTwoBallCubicLowerLevel =
  SineTwoBall.bishopSineTwoBallCubicLowerLevel
outerBrillouinCubicSineLowerLevel =
  OuterSine.outerBrillouinCubicSineLowerLevel
outerBrillouinHatMomentumGapLevel =
  OuterSine.outerBrillouinHatMomentumGapLevel
