module DASHI.Analysis.HyperrealThresholdProcessBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Hyperreals supply infinitesimal resolution and hyperfinite processing time.
-- They do not supply the hierarchical address carried by Z_3.

record HyperrealFieldLane : Set₁ where
  field
    Real Hyperreal : Set
    embed : Real → Hyperreal
    zeroH oneH : Hyperreal
    addH multiplyH subtractH : Hyperreal → Hyperreal → Hyperreal
    _<H_ : Hyperreal → Hyperreal → Set
    infinitesimal : Hyperreal → Set
    finite : Hyperreal → Set
    epsilon : Hyperreal
    epsilonPositive : zeroH <H epsilon
    epsilonInfinitesimal : infinitesimal epsilon
    standardPart : (x : Hyperreal) → finite x → Real
    standardPartLaw : Set
    transferPrincipleFragment : Set

record HyperfiniteTimeLane (H : HyperrealFieldLane) : Set₁ where
  open HyperrealFieldLane H
  field
    State Context : Set
    hyperfiniteSteps : Nat
    step : State → Context → State
    initial : State
    context : Context
    iterate : Nat → State
    iterationLaw : Set
    finiteObservation : Set
    standardPartTrajectory : Set

------------------------------------------------------------------------
-- A threshold halo distinguishes approach/depart direction internally even
-- when all points have the same standard part.

data HaloPosition : Set where
  wellBelowHalo : HaloPosition
  approachesFromBelow : HaloPosition
  atHalo : HaloPosition
  departsAbove : HaloPosition
  wellAboveHalo : HaloPosition

data HaloAction : Set where
  retainAction inspectAction refineAction branchAction : HaloAction

haloPolicy : HaloPosition → HaloAction
haloPolicy wellBelowHalo = retainAction
haloPolicy approachesFromBelow = inspectAction
haloPolicy atHalo = refineAction
haloPolicy departsAbove = refineAction
haloPolicy wellAboveHalo = branchAction

record ThresholdHalo (H : HyperrealFieldLane) : Set₁ where
  open HyperrealFieldLane H
  field
    threshold : Hyperreal
    tolerance : Hyperreal
    toleranceInfinitesimalOrDeclared : Set
    classify : Hyperreal → HaloPosition
    belowWitness : Hyperreal
    exactWitness : Hyperreal
    aboveWitness : Hyperreal
    sharedStandardPart : Set
    directionRetainedInternally : Set

------------------------------------------------------------------------
-- Standard part is a projection which may forget an infinitesimal residual.

record StandardPartDarkMirror (H : HyperrealFieldLane) : Set₁ where
  open HyperrealFieldLane H
  field
    hidden : Hyperreal
    hiddenFinite : finite hidden
    observed : Real
    observedChecks : observed ≡ standardPart hidden hiddenFinite
    infinitesimalResidual : Hyperreal
    residualChecks : infinitesimalResidual ≡ subtractH hidden (embed observed)
    residualIsInfinitesimal : infinitesimal infinitesimalResidual

record HyperrealLogisticLane (H : HyperrealFieldLane) : Set₁ where
  open HyperrealFieldLane H
  field
    parameterThree : Hyperreal
    justBeforeThree : Hyperreal
    justAfterThree : Hyperreal
    accumulationParameter : Hyperreal
    justBeforeAccumulation : Hyperreal
    justAfterAccumulation : Hyperreal
    beforeAfterDifferInfinitesimally : Set
    logisticStep : Hyperreal → Hyperreal → Hyperreal
    hyperfiniteOrbit : Set
    standardPartOrbit : Set
    bifurcationComparison : Set

record HyperrealPadicSeparationBoundary : Set where
  constructor hyperrealPadicSeparationBoundary
  field
    hyperrealSuppliesInfinitesimalResolution : Bool
    padicSuppliesHierarchicalAddress : Bool
    hyperrealAndPadicIdentifiedAsOneField : Bool
    hyperrealAndPadicIdentifiedAsOneFieldIsFalse :
      hyperrealAndPadicIdentifiedAsOneField ≡ false
    standardPartIsPadicInverseLimit : Bool
    standardPartIsPadicInverseLimitIsFalse :
      standardPartIsPadicInverseLimit ≡ false
    concreteHyperrealConstructionPromoted : Bool
    concreteHyperrealConstructionPromotedIsFalse :
      concreteHyperrealConstructionPromoted ≡ false
    universalTransferPromoted : Bool
    universalTransferPromotedIsFalse : universalTransferPromoted ≡ false
    interpretation : String

canonicalHyperrealPadicSeparationBoundary :
  HyperrealPadicSeparationBoundary
canonicalHyperrealPadicSeparationBoundary =
  hyperrealPadicSeparationBoundary
    true
    true
    false refl
    false refl
    false refl
    false refl
    "hyperreals provide infinitesimal threshold and hyperfinite-time sockets, while triadic quotients provide hierarchical address; any product or bridge is explicit"
