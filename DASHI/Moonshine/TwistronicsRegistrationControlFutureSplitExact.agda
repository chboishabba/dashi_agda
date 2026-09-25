module DASHI.Moonshine.TwistronicsRegistrationControlFutureSplitExact where

------------------------------------------------------------------------
-- TWISTRONICS REGISTRATION-CONTROL DYNAMICS
--
-- PRIMARY EXTERNAL SOURCE
--
-- Cheng Hu et al.,
-- "In-situ twistable bilayer graphene",
-- Scientific Reports 12, 204 (2022).
-- DOI: 10.1038/s41598-021-04030-z.
--
-- The experiment constructs a tBLG device whose relative twist angle can be
-- changed in situ by AFM manipulation of an hBN gear.  AFM/SNOM/Raman
-- measurements verify twist changes and twist-dependent moire/optical response.
--
-- DASHI contribution:
--   * a proof-bearing generic action system for a registration-control map;
--   * a terminalisation/future-split theorem conditional on an explicit
--     control-sensitive witness;
--   * a two-class residual-capacity consequence.
--
-- The external source establishes controllability and twist-dependent measured
-- observables.  It does NOT itself prove the generic DASHI factorisation or
-- FutureEquivalent theorem, nor do we fabricate an exact equal-before /
-- unequal-after experimental pair not reported by the source.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Moonshine.TwistronicsRelativeRegistrationComparatorExact as Twist
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationalRefinement as Future
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.FutureSafeCoarseFibreCapacityExact as Capacity
import DASHI.Core.GeneralResidualFibreCardinalityExact as Cardinality

------------------------------------------------------------------------
-- 1. External control source receipt.
------------------------------------------------------------------------

huEtAl2022InSituTwist : Attribution.AttributedSource
huEtAl2022InSituTwist =
  Attribution.mkDOISource
    "Cheng Hu, Tongyao Wu, Xinyue Huang, Yulong Dong, Jiajun Chen, Zhichun Zhang, Bosai Lyu, Saiqun Ma, Kenji Watanabe, Takashi Taniguchi, Guibai Xie, Xiaojun Li, Qi Liang, Zhiwen Shi"
    "In-situ twistable bilayer graphene"
    "Scientific Reports 12, 204"
    "2022"
    "10.1038/s41598-021-04030-z"
    "https://doi.org/10.1038/s41598-021-04030-z"
    Attribution.academicArticleSource
    "primary source for AFM-driven in-situ relative-twist control in one bilayer graphene device and twist-dependent AFM/SNOM/Raman characterization; not a source for DASHI future-equivalence, codec, J/369 or nongin claims"
    Attribution.publicAttribution

twistControlSourceAtlas : Attribution.AttributedSourceAtlas
twistControlSourceAtlas =
  Attribution.mkSourceAtlas
    "Twistronics in-situ registration-control source atlas"
    "DASHI.Moonshine.TwistronicsRegistrationControlFutureSplitExact"
    (huEtAl2022InSituTwist ∷ [])
    "external source owns the physical control/measurement facts; DASHI owns the generic action-system and future-safety reconstruction"

record ExternalTwistControlReceipt : Set where
  constructor external-twist-control-receipt
  field
    source : Attribution.AttributedSourceAtlas
    sameDeviceTwistCanBeControlledInSitu : Bool
    afmManipulationControlsRelativeRotation : Bool
    snomTracksMoireChange : Bool
    ramanResponseDependsOnTwist : Bool
    sourceReportsContinuousLargeRangeControl : Bool
    sourceReportsFineTwistControl : Bool
    sourceProvesDASHIFutureEquivalentTheorem : Bool
    sourceProvesDASHIFutureEquivalentTheoremIsFalse :
      sourceProvesDASHIFutureEquivalentTheorem ≡ false

canonicalExternalTwistControlReceipt : ExternalTwistControlReceipt
canonicalExternalTwistControlReceipt =
  external-twist-control-receipt
    twistControlSourceAtlas
    true true true true true true
    false refl

------------------------------------------------------------------------
-- 2. Generic physically meaningful registration-control action.
------------------------------------------------------------------------

record RegistrationControl (Registration : Set) : Set₁ where
  constructor registration-control
  field
    updateRegistration : Registration -> Registration
    controlLabel : String
    sourceReading : String

open RegistrationControl public

data ControlAction : Set where
  applyRegistrationControl : ControlAction

Postcondition :
  ∀ {Microscopic Registration : Set} ->
  RegistrationControl Registration ->
  Twist.OverlayState Microscopic Registration ->
  ControlAction ->
  Twist.OverlayState Microscopic Registration ->
  Set
Postcondition control before applyRegistrationControl after =
  after ≡
    Twist.changeRegistration
      before
      (updateRegistration control (Twist.relativeRegistration before))

registrationControlActionSystem :
  ∀ {Microscopic Registration : Set} ->
  RegistrationControl Registration ->
  Dependency.DependentActionSystem
    (Twist.OverlayState Microscopic Registration)
    ControlAction
registrationControlActionSystem control =
  record
    { Precondition = λ before action -> ⊤
    ; Postcondition = Postcondition control
    ; actionLabel =
        λ { applyRegistrationControl -> controlLabel control }
    }

controlledState :
  ∀ {Microscopic Registration : Set} ->
  RegistrationControl Registration ->
  Twist.OverlayState Microscopic Registration ->
  Twist.OverlayState Microscopic Registration
controlledState control state =
  Twist.changeRegistration
    state
    (updateRegistration control (Twist.relativeRegistration state))

controlPreservesLeftMicroscopic :
  ∀ {Microscopic Registration : Set}
    (control : RegistrationControl Registration)
    (state : Twist.OverlayState Microscopic Registration) ->
  Twist.leftMicroscopic (controlledState control state)
  ≡ Twist.leftMicroscopic state
controlPreservesLeftMicroscopic control state = refl

controlPreservesRightMicroscopic :
  ∀ {Microscopic Registration : Set}
    (control : RegistrationControl Registration)
    (state : Twist.OverlayState Microscopic Registration) ->
  Twist.rightMicroscopic (controlledState control state)
  ≡ Twist.rightMicroscopic state
controlPreservesRightMicroscopic control state = refl

------------------------------------------------------------------------
-- 3. A control-sensitive witness is exactly the experimental/theory input
--    needed for a dynamic split.  No equal-before pair is manufactured.
------------------------------------------------------------------------

record RegistrationControlSplitWitness
    {Microscopic Registration Effective : Set}
    (system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective)
    (control : RegistrationControl Registration) : Set where
  constructor registration-control-split-witness
  field
    microscopic : Microscopic
    firstRegistration secondRegistration : Registration

    sameBefore :
      Twist.observeEffective system
        (Twist.overlay microscopic microscopic firstRegistration)
      ≡
      Twist.observeEffective system
        (Twist.overlay microscopic microscopic secondRegistration)

    differentAfter :
      Twist.observeEffective system
        (controlledState control
          (Twist.overlay microscopic microscopic firstRegistration))
      ≡
      Twist.observeEffective system
        (controlledState control
          (Twist.overlay microscopic microscopic secondRegistration))
      ->
      ⊥

open RegistrationControlSplitWitness public

leftBefore :
  ∀ {Microscopic Registration Effective}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration} ->
  RegistrationControlSplitWitness system control ->
  Twist.OverlayState Microscopic Registration
leftBefore witness =
  Twist.overlay
    (microscopic witness)
    (microscopic witness)
    (firstRegistration witness)

rightBefore :
  ∀ {Microscopic Registration Effective}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration} ->
  RegistrationControlSplitWitness system control ->
  Twist.OverlayState Microscopic Registration
rightBefore witness =
  Twist.overlay
    (microscopic witness)
    (microscopic witness)
    (secondRegistration witness)

leftAfter :
  ∀ {Microscopic Registration Effective}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration} ->
  RegistrationControlSplitWitness system control ->
  Twist.OverlayState Microscopic Registration
leftAfter {control = control} witness =
  controlledState control (leftBefore witness)

rightAfter :
  ∀ {Microscopic Registration Effective}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration} ->
  RegistrationControlSplitWitness system control ->
  Twist.OverlayState Microscopic Registration
rightAfter {control = control} witness =
  controlledState control (rightBefore witness)

leftControlAction :
  ∀ {Microscopic Registration Effective}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration}
    (witness : RegistrationControlSplitWitness system control) ->
  Dependency.AdmissibleAction
    (registrationControlActionSystem control)
    (leftBefore witness)
    applyRegistrationControl
leftControlAction {control = control} witness =
  record
    { precondition = tt
    ; after = leftAfter witness
    ; postcondition = refl
    ; dependencyReceipt =
        "apply the declared sourced registration-control map while preserving both microscopic layer slots"
    }

rightControlAction :
  ∀ {Microscopic Registration Effective}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration}
    (witness : RegistrationControlSplitWitness system control) ->
  Dependency.AdmissibleAction
    (registrationControlActionSystem control)
    (rightBefore witness)
    applyRegistrationControl
rightControlAction {control = control} witness =
  record
    { precondition = tt
    ; after = rightAfter witness
    ; postcondition = refl
    ; dependencyReceipt =
        "apply the declared sourced registration-control map while preserving both microscopic layer slots"
    }

leftControlExecution :
  ∀ {Microscopic Registration Effective}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration}
    (witness : RegistrationControlSplitWitness system control) ->
  Reachability.Executes
    (registrationControlActionSystem control)
    (applyRegistrationControl ∷ [])
    (leftBefore witness)
    (leftAfter witness)
leftControlExecution witness =
  Reachability.executesCons
    (leftControlAction witness)
    Reachability.executesNil

rightControlExecution :
  ∀ {Microscopic Registration Effective}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration}
    (witness : RegistrationControlSplitWitness system control) ->
  Reachability.Executes
    (registrationControlActionSystem control)
    (applyRegistrationControl ∷ [])
    (rightBefore witness)
    (rightAfter witness)
rightControlExecution witness =
  Reachability.executesCons
    (rightControlAction witness)
    Reachability.executesNil

------------------------------------------------------------------------
-- 4. Dynamic consequence: common physical control can expose a hidden
--    registration distinction for the declared effective observer.
------------------------------------------------------------------------

registrationControlTerminalisationDefect :
  ∀ {Microscopic Registration Effective}
    (system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective)
    (control : RegistrationControl Registration)
    (witness : RegistrationControlSplitWitness system control) ->
  Dynamic.TerminalisationDefect
    (registrationControlActionSystem control)
    (Twist.observeEffective system)
registrationControlTerminalisationDefect system control witness =
  Dynamic.terminalisationDefect
    (applyRegistrationControl ∷ [])
    (leftBefore witness)
    (rightBefore witness)
    (leftAfter witness)
    (rightAfter witness)
    (sameBefore witness)
    (leftControlExecution witness)
    (rightControlExecution witness)
    (differentAfter witness)

controlSplitRefutesFutureEquivalent :
  ∀ {Microscopic Registration Effective}
    (system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective)
    (control : RegistrationControl Registration)
    (witness : RegistrationControlSplitWitness system control) ->
  Future.FutureEquivalent
    (registrationControlActionSystem control)
    (Twist.observeEffective system)
    (leftBefore witness)
    (rightBefore witness)
  ->
  ⊥
controlSplitRefutesFutureEquivalent system control witness future =
  differentAfter witness
    (future
      (leftControlExecution witness)
      (rightControlExecution witness))

controlSplitRefutesReverseFutureEquivalent :
  ∀ {Microscopic Registration Effective}
    (system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective)
    (control : RegistrationControl Registration)
    (witness : RegistrationControlSplitWitness system control) ->
  Future.FutureEquivalent
    (registrationControlActionSystem control)
    (Twist.observeEffective system)
    (rightBefore witness)
    (leftBefore witness)
  ->
  ⊥
controlSplitRefutesReverseFutureEquivalent system control witness future =
  differentAfter witness
    (sym
      (future
        (rightControlExecution witness)
        (leftControlExecution witness)))

------------------------------------------------------------------------
-- 5. Conditional two-class capacity theorem.
------------------------------------------------------------------------

twoControlRepresentative :
  ∀ {Microscopic Registration Effective}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration} ->
  RegistrationControlSplitWitness system control ->
  Fin 2 ->
  Twist.OverlayState Microscopic Registration
twoControlRepresentative witness zero = leftBefore witness
twoControlRepresentative witness (suc zero) = rightBefore witness

twoControlFutureEquivalentIndicesEqual :
  ∀ {Microscopic Registration Effective}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration}
    (witness : RegistrationControlSplitWitness system control)
    {left right : Fin 2} ->
  Future.FutureEquivalent
    (registrationControlActionSystem control)
    (Twist.observeEffective system)
    (twoControlRepresentative witness left)
    (twoControlRepresentative witness right) ->
  left ≡ right
twoControlFutureEquivalentIndicesEqual systemWitness {zero} {zero} future = refl
twoControlFutureEquivalentIndicesEqual
  {system = system} {control = control}
  witness {zero} {suc zero} future =
  ⊥-elim (controlSplitRefutesFutureEquivalent system control witness future)
twoControlFutureEquivalentIndicesEqual
  {system = system} {control = control}
  witness {suc zero} {zero} future =
  ⊥-elim
    (controlSplitRefutesReverseFutureEquivalent system control witness future)
twoControlFutureEquivalentIndicesEqual systemWitness {suc zero} {suc zero} future = refl

canonicalControlFutureDistinctFibre :
  ∀ {Microscopic Registration Effective}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration}
    (witness : RegistrationControlSplitWitness system control) ->
  Capacity.CanonicalFiniteFutureDistinctFibre
    2
    (registrationControlActionSystem control)
    (Twist.observeEffective system)
canonicalControlFutureDistinctFibre
  {system = system} {control = control} witness =
  Cardinality.finiteFutureDistinctFibre
    (twoControlRepresentative witness)
    (Twist.observeEffective system (leftBefore witness))
    (λ { zero -> refl ; (suc zero) -> sym (sameBefore witness) })
    (twoControlFutureEquivalentIndicesEqual witness)

controlSplitForcesResidualInjection :
  ∀ {Microscopic Registration Effective Residual}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration}
    (witness : RegistrationControlSplitWitness system control)
    {residual : Twist.OverlayState Microscopic Registration -> Residual} ->
  Capacity.FutureSafeResidual
    (registrationControlActionSystem control)
    (Twist.observeEffective system)
    residual ->
  Cardinality.Injective
    (λ index -> residual (twoControlRepresentative witness index))
controlSplitForcesResidualInjection witness safe =
  Capacity.futureSafeResidualInjectsCanonicalFutureClasses
    safe
    (canonicalControlFutureDistinctFibre witness)

controlSplitForcesBitCapacity :
  ∀ {Microscopic Registration Effective bits}
    {system : Twist.RelativeRegistrationSystem
      Microscopic Registration Effective}
    {control : RegistrationControl Registration}
    (witness : RegistrationControlSplitWitness system control)
    {residual :
      Twist.OverlayState Microscopic Registration ->
      Cardinality.BitWords bits} ->
  Capacity.FutureSafeResidual
    (registrationControlActionSystem control)
    (Twist.observeEffective system)
    residual ->
  2 ≤ Cardinality.pow2 bits
controlSplitForcesBitCapacity witness safe =
  Capacity.futureSafeBitResidualCapacityBound
    safe
    (canonicalControlFutureDistinctFibre witness)

------------------------------------------------------------------------
-- 6. Physical / formal boundary.
------------------------------------------------------------------------

record TwistronicsRegistrationControlBoundary : Set where
  constructor twistronics-registration-control-boundary
  field
    primaryInSituTwistControlAttributed : Bool
    proofBearingRegistrationControlSystemConstructed : Bool
    controlPreservesMicroscopicLayerSlots : Bool
    dynamicFutureSplitAvailableFromExplicitWitness : Bool
    twoClassCapacityAvailableFromExplicitWitness : Bool
    exactEqualBeforeUnequalAfterExperimentalPairHardCoded : Bool
    exactEqualBeforeUnequalAfterExperimentalPairHardCodedIsFalse :
      exactEqualBeforeUnequalAfterExperimentalPairHardCoded ≡ false
    staticParameterDependenceCalledTimeEvolution : Bool
    staticParameterDependenceCalledTimeEvolutionIsFalse :
      staticParameterDependenceCalledTimeEvolution ≡ false
    twistronicsControlProvesNonginMechanism : Bool
    twistronicsControlProvesNonginMechanismIsFalse :
      twistronicsControlProvesNonginMechanism ≡ false

canonicalTwistronicsRegistrationControlBoundary :
  TwistronicsRegistrationControlBoundary
canonicalTwistronicsRegistrationControlBoundary =
  twistronics-registration-control-boundary
    true true true true true
    false refl
    false refl
    false refl
