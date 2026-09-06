module DASHI.Physics.Closure.NSTriadKNFixedOutputFluxToTemporalRealizationRound413Exact where

------------------------------------------------------------------------
-- ROUND413 / BIDI TEMPORAL COMPILER TARGET, UPDATED AFTER R425--R427
--
-- The intended same-object composition is:
--
--   R406 fixed-output instantaneous identity
--     + R422 finite derivative assembly
--     + R425--R427 actual literal mixed-cell derivative from R408
--     + ordinary real FTC/integration laws
--   -> R393 literal temporal realization.
--
-- R425--R427 remove the former NS-specific "actual cell derivative" ambiguity:
-- the tangent is now built from the literal R408 trajectory rather than chosen
-- by a caller.  What remains here is ordinary scalar calculus/FTC authority on
-- the already-fixed finite observable.  No replacement flux, replacement debt,
-- or new Navier--Stokes estimate is admitted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact as R422
import DASHI.Physics.Closure.NSTriadKNLiteralTrajectoryMixedCellDerivativeRound427Exact as R427
import DASHI.Physics.Closure.NSTriadKNLiteralR378TemporalIntegrationBoundaryRound393Exact as R393

round413UsesSameR406Flux : Bool
round413UsesSameR406Flux = true

round413UsesSameLiteralR378Debt : Bool
round413UsesSameLiteralR378Debt = true

round413FiniteDerivativeAssemblyClosed : Bool
round413FiniteDerivativeAssemblyClosed = R422.round422FinitePairSummationClosed

round413ActualLiteralMixedCellDerivativeConstructed : Bool
round413ActualLiteralMixedCellDerivativeConstructed =
  R427.round427ActualPlusMinusCellDifferentiationClosedModuloStandardCalculus

round413PhysicalDerivativeSelectionStillOpen : Bool
round413PhysicalDerivativeSelectionStillOpen = false

round413OnlyOrdinaryScalarCalculusFTCRemains : Bool
round413OnlyOrdinaryScalarCalculusFTCRemains = true

round413EndpointFTCStillAnalyticLeaf : Bool
round413EndpointFTCStillAnalyticLeaf =
  R393.round393EndpointFundamentalTheoremStillAnalyticLeaf

round413IntroducesNewNSCancellationEstimate : Bool
round413IntroducesNewNSCancellationEstimate = false

round413UsesSameR406FluxIsTrue : round413UsesSameR406Flux ≡ true
round413UsesSameR406FluxIsTrue = refl

round413FiniteDerivativeAssemblyClosedIsTrue :
  round413FiniteDerivativeAssemblyClosed ≡ true
round413FiniteDerivativeAssemblyClosedIsTrue = refl

round413ActualLiteralMixedCellDerivativeConstructedIsTrue :
  round413ActualLiteralMixedCellDerivativeConstructed ≡ true
round413ActualLiteralMixedCellDerivativeConstructedIsTrue = refl

round413PhysicalDerivativeSelectionStillOpenIsFalse :
  round413PhysicalDerivativeSelectionStillOpen ≡ false
round413PhysicalDerivativeSelectionStillOpenIsFalse = refl

round413OnlyOrdinaryScalarCalculusFTCRemainsIsTrue :
  round413OnlyOrdinaryScalarCalculusFTCRemains ≡ true
round413OnlyOrdinaryScalarCalculusFTCRemainsIsTrue = refl

round413IntroducesNewNSCancellationEstimateIsFalse :
  round413IntroducesNewNSCancellationEstimate ≡ false
round413IntroducesNewNSCancellationEstimateIsFalse = refl
