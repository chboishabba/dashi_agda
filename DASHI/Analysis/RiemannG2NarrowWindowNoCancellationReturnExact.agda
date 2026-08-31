module DASHI.Analysis.RiemannG2NarrowWindowNoCancellationReturnExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LEAN RETURN: NARROW-WINDOW NO-CANCELLATION REGIME
--
-- The corresponding Lean theorem is reported machine-checked in
-- Zeta23Bridge/Zeta23Bridge/NearCoreNarrowWindowNoCancellation.lean.
-- This Agda owner records the theorem surface and its BIDI consequence only.
-- It does NOT transport the Lean proof term into Agda.
------------------------------------------------------------------------

data CrossProverAuthority : Set where
  checkedLeanReturn openAgdaObligation : CrossProverAuthority

data WindowRegime : Set where
  narrowQuarterPeriod
  oscillatoryBeyondQuarterPeriod
  : WindowRegime

data ScalarRouteDisposition : Set where
  directEstimateBlocked
  explicitFormulaWindowBlocked
  oscillatoryRouteLive
  : ScalarRouteDisposition

record NarrowWindowNoCancellationReturn : Set where
  constructor narrow-window-no-cancellation-return
  field
    theoremOwner : String
    authority : CrossProverAuthority
    machineCheckedInLean : Bool
    transportedIntoAgda : Bool

    supportRadiusName : String
    cutoffName : String
    narrowRegimeCondition : String

    cosineNonnegativeOnNarrowRegime : Bool
    cosineNonnegativeOnNarrowRegimeIsTrue :
      cosineNonnegativeOnNarrowRegime ≡ true

    phaseSumPinnedByNearMass : Bool
    phaseSumPinnedByNearMassIsTrue :
      phaseSumPinnedByNearMass ≡ true

    scalarIntegralPinnedPositive : Bool
    scalarIntegralPinnedPositiveIsTrue :
      scalarIntegralPinnedPositive ≡ true

    scalarConsumerHypothesisCanBecomeUnsatisfiable : Bool
    scalarConsumerHypothesisCanBecomeUnsatisfiableIsTrue :
      scalarConsumerHypothesisCanBecomeUnsatisfiable ≡ true

    directAndExplicitFormulaBranchesShareSamePinnedQuantity : Bool
    directAndExplicitFormulaBranchesShareSamePinnedQuantityIsTrue :
      directAndExplicitFormulaBranchesShareSamePinnedQuantity ≡ true

    survivingRouteRequiresQuarterPeriodCrossing : Bool
    survivingRouteRequiresQuarterPeriodCrossingIsTrue :
      survivingRouteRequiresQuarterPeriodCrossing ≡ true

    quarterPeriodCrossingReading : String
    exactLowerBoundReading : String
    exactUpperBoundReading : String
    boundedReading : String

open NarrowWindowNoCancellationReturn public

canonicalNarrowWindowNoCancellationReturn : NarrowWindowNoCancellationReturn
canonicalNarrowWindowNoCancellationReturn =
  narrow-window-no-cancellation-return
    "Zeta23Bridge.NearCoreNarrowWindowNoCancellation"
    (checkedLeanReturn)
    true
    false
    "Lambda"
    "J"
    "J * Lambda <= pi/2"
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "A surviving cancellation route requires pi/2 < J*Lambda; at high ordinate this forces the cutoff to grow on the inverse taper-width scale rather than remaining fixed."
    "nearMass * cos(J*Lambda) <= S(t,J;u), hence integral q*S is bounded below by a positive multiple of nearMass and taper mass in the stated regime."
    "S(t,J;u) <= nearMass * cosh(Lambda/2) in the stated regime."
    "In the narrow quarter-period regime the finite near scalar is positively pinned. There is no signed phase cancellation to extract there. The direct scalar route and any target-centred explicit-formula route computing the same scalar fail together once the pinned lower bound reaches the consumer threshold. This is checked-Lean provenance, not an Agda proof and not RH."

currentRegimeIfQuarterPeriodNotCrossed : WindowRegime
currentRegimeIfQuarterPeriodNotCrossed = narrowQuarterPeriod

narrowDirectDisposition : ScalarRouteDisposition
narrowDirectDisposition = directEstimateBlocked

narrowExplicitFormulaDisposition : ScalarRouteDisposition
narrowExplicitFormulaDisposition = explicitFormulaWindowBlocked

wideOscillatoryDisposition : ScalarRouteDisposition
wideOscillatoryDisposition = oscillatoryRouteLive

record NarrowWindowRouteBoundary : Set where
  constructor narrow-window-route-boundary
  field
    sharperEstimateAtFixedNarrowCutoffCanCreateCancellation : Bool
    sharperEstimateAtFixedNarrowCutoffCanCreateCancellationIsFalse :
      sharperEstimateAtFixedNarrowCutoffCanCreateCancellation ≡ false

    directAndExplicitFormulaAreIndependentInNarrowRegime : Bool
    directAndExplicitFormulaAreIndependentInNarrowRegimeIsFalse :
      directAndExplicitFormulaAreIndependentInNarrowRegime ≡ false

    fixedNarrowCutoffIsHighestAlpha : Bool
    fixedNarrowCutoffIsHighestAlphaIsFalse :
      fixedNarrowCutoffIsHighestAlpha ≡ false

    quarterPeriodCrossingIsNecessaryForOscillatoryCancellation : Bool
    quarterPeriodCrossingIsNecessaryForOscillatoryCancellationIsTrue :
      quarterPeriodCrossingIsNecessaryForOscillatoryCancellation ≡ true

    leanProofTransportedIntoAgda : Bool
    leanProofTransportedIntoAgdaIsFalse : leanProofTransportedIntoAgda ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalNarrowWindowRouteBoundary : NarrowWindowRouteBoundary
canonicalNarrowWindowRouteBoundary =
  narrow-window-route-boundary
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    "The narrow-window scalar-cancellation leaf is closed negatively in Lean: if J*Lambda <= pi/2, the target-centred phase sum is nonnegative and the scalar is positively pinned. Do not sharpen the same fixed-cutoff estimate and do not treat direct versus explicit-formula evaluation as separate escape routes. The live analytic search begins only after proving pi/2 < J*Lambda on the literal taper/cutoff pair."
