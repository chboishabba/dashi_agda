module DASHI.Biology.AnaestheticObservationErrorProductRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.AnaestheticErrorBoundMechanismFibreMonotonicityExact as Error
import DASHI.Biology.CrossKingdomAnaestheticMechanismFibreRefinementExact as Fibre

------------------------------------------------------------------------
-- PRODUCT REFINEMENT: OBSERVATIONS × VALIDATED ERROR BOUNDS
--
-- The previous two owners establish two independent reverse-inference facts:
--
--   additional observations        shrink the residual mechanism fibre;
--   tighter validated error bounds shrink the admissible mechanism fibre.
--
-- This owner combines them into one order and proves that the two operations
-- commute at the level of admissible candidates.  The construction is generic
-- repository mathematics.  It does not identify any synthetic mechanism with
-- an empirical anaesthetic target.
------------------------------------------------------------------------

record ObservationCompatibility (Candidate : Set) : Set₁ where
  constructor observationCompatibility
  field
    ObservationSpec : Set
    satisfiesObservation : Candidate → ObservationSpec → Set

open ObservationCompatibility public

record ObservationRefinement
    {Candidate : Set}
    (model : ObservationCompatibility Candidate) : Set₁ where
  constructor observationRefinement
  field
    coarse fine : ObservationSpec model
    fineImpliesCoarse :
      (candidate : Candidate) →
      satisfiesObservation model candidate fine →
      satisfiesObservation model candidate coarse

open ObservationRefinement public

------------------------------------------------------------------------
-- Product state and admissible fibre.
------------------------------------------------------------------------

record ProductRefinementState
    {Candidate : Set}
    (observations : ObservationCompatibility Candidate)
    (errors : Error.OrderedErrorCompatibility) : Set where
  constructor productRefinementState
  field
    observation : ObservationSpec observations
    measurement : Error.Measurement errors
    errorBound : Error.ErrorBound errors

open ProductRefinementState public

ProductAdmissible :
  {Candidate : Set} →
  (observations : ObservationCompatibility Candidate) →
  (errors : Error.OrderedErrorCompatibility) →
  (candidateToErrorCandidate : Candidate → Error.Candidate errors) →
  ProductRefinementState observations errors →
  Candidate → Set
ProductAdmissible observations errors lift state candidate =
  satisfiesObservation observations candidate (observation state)
  × Error.compatible errors
      (lift candidate)
      (measurement state)
      (errorBound state)

ProductFibre :
  {Candidate : Set} →
  (observations : ObservationCompatibility Candidate) →
  (errors : Error.OrderedErrorCompatibility) →
  (candidateToErrorCandidate : Candidate → Error.Candidate errors) →
  ProductRefinementState observations errors →
  Set
ProductFibre {Candidate} observations errors lift state =
  Σ Candidate (ProductAdmissible observations errors lift state)

------------------------------------------------------------------------
-- Product order: target has at least the information of source when its
-- observation is finer and its validated error bound is tighter.
------------------------------------------------------------------------

record ProductRefines
    {Candidate : Set}
    {observations : ObservationCompatibility Candidate}
    {errors : Error.OrderedErrorCompatibility}
    (source target : ProductRefinementState observations errors) : Set₁ where
  constructor productRefines
  field
    targetObservationImpliesSource :
      (candidate : Candidate) →
      satisfiesObservation observations candidate (observation target) →
      satisfiesObservation observations candidate (observation source)

    sameMeasurement : measurement source ≡ measurement target

    targetErrorNoLooserThanSource :
      Error._≼_ errors (errorBound target) (errorBound source)

open ProductRefines public

productRefinementShrinksFibre :
  {Candidate : Set}
  {observations : ObservationCompatibility Candidate}
  {errors : Error.OrderedErrorCompatibility}
  {lift : Candidate → Error.Candidate errors}
  {source target : ProductRefinementState observations errors} →
  ProductRefines source target →
  ProductFibre observations errors lift target →
  ProductFibre observations errors lift source
productRefinementShrinksFibre {errors = errors} {source = source} {target = target}
    refinement point =
  candidate ,
  targetObservationImpliesSource refinement candidate fineObservation ,
  Error.compatibilityMonotone errors
    (lift candidate)
    (measurement source)
    (targetErrorNoLooserThanSource refinement)
    errorAtTarget
  where
    candidate = proj₁ point
    fineObservation = proj₁ (proj₂ point)
    errorAtTargetRaw = proj₂ (proj₂ point)

    errorAtTarget :
      Error.compatible errors
        (lift candidate)
        (measurement source)
        (errorBound target)
    errorAtTarget rewrite sameMeasurement refinement = errorAtTargetRaw

------------------------------------------------------------------------
-- Two primitive refinement moves.
------------------------------------------------------------------------

addObservation :
  {Candidate : Set}
  {observations : ObservationCompatibility Candidate}
  {errors : Error.OrderedErrorCompatibility} →
  (state : ProductRefinementState observations errors) →
  (fine : ObservationSpec observations) →
  ((candidate : Candidate) →
    satisfiesObservation observations candidate fine →
    satisfiesObservation observations candidate (observation state)) →
  ProductRefinementState observations errors
addObservation state fine fineImpliesCoarse =
  productRefinementState fine (measurement state) (errorBound state)

tightenError :
  {Candidate : Set}
  {observations : ObservationCompatibility Candidate}
  {errors : Error.OrderedErrorCompatibility} →
  (state : ProductRefinementState observations errors) →
  (tight : Error.ErrorBound errors) →
  Error._≼_ errors tight (errorBound state) →
  ProductRefinementState observations errors
tightenError state tight tightNoLooser =
  productRefinementState (observation state) (measurement state) tight

------------------------------------------------------------------------
-- Commutation square.
--
-- Both paths produce definitionally the same final product state:
--
--   add observation ; tighten error
--   tighten error   ; add observation
------------------------------------------------------------------------

observationErrorCommute :
  {Candidate : Set}
  {observations : ObservationCompatibility Candidate}
  {errors : Error.OrderedErrorCompatibility}
  (state : ProductRefinementState observations errors)
  (fine : ObservationSpec observations)
  (fineImpliesCoarse :
    (candidate : Candidate) →
    satisfiesObservation observations candidate fine →
    satisfiesObservation observations candidate (observation state))
  (tight : Error.ErrorBound errors)
  (tightNoLooser : Error._≼_ errors tight (errorBound state)) →
  tightenError
    (addObservation state fine fineImpliesCoarse)
    tight tightNoLooser
  ≡
  addObservation
    (tightenError state tight tightNoLooser)
    fine fineImpliesCoarse
observationErrorCommute state fine fineImpliesCoarse tight tightNoLooser = refl

------------------------------------------------------------------------
-- Therefore the admissible fibre is path-independent as well.
------------------------------------------------------------------------

commutingRefinementGivesSameCandidatePredicate :
  {Candidate : Set}
  {observations : ObservationCompatibility Candidate}
  {errors : Error.OrderedErrorCompatibility}
  (lift : Candidate → Error.Candidate errors)
  (state : ProductRefinementState observations errors)
  (fine : ObservationSpec observations)
  (fineImpliesCoarse :
    (candidate : Candidate) →
    satisfiesObservation observations candidate fine →
    satisfiesObservation observations candidate (observation state))
  (tight : Error.ErrorBound errors)
  (tightNoLooser : Error._≼_ errors tight (errorBound state))
  (candidate : Candidate) →
  ProductAdmissible observations errors lift
    (tightenError
      (addObservation state fine fineImpliesCoarse)
      tight tightNoLooser)
    candidate
  ≡
  ProductAdmissible observations errors lift
    (addObservation
      (tightenError state tight tightNoLooser)
      fine fineImpliesCoarse)
    candidate
commutingRefinementGivesSameCandidatePredicate
  lift state fine fineImpliesCoarse tight tightNoLooser candidate = refl

------------------------------------------------------------------------
-- Finite synthetic instantiation using the existing anaesthetic candidate set.
------------------------------------------------------------------------

data ObservationSpecSynthetic : Set where
  behaviourOnly
  behaviourPlusVoltage
  behaviourPlusVoltageCurrent
  : ObservationSpecSynthetic

data SyntheticObservationCompatible :
    Fibre.MechanismCandidate → ObservationSpecSynthetic → Set where
  channelBehaviour :
    SyntheticObservationCompatible Fibre.channelCandidate behaviourOnly
  membraneBehaviour :
    SyntheticObservationCompatible Fibre.membraneCandidate behaviourOnly
  pumpBehaviour :
    SyntheticObservationCompatible Fibre.pumpCandidate behaviourOnly

  channelVoltage :
    SyntheticObservationCompatible Fibre.channelCandidate behaviourPlusVoltage
  membraneVoltage :
    SyntheticObservationCompatible Fibre.membraneCandidate behaviourPlusVoltage

  channelCurrent :
    SyntheticObservationCompatible Fibre.channelCandidate behaviourPlusVoltageCurrent

syntheticObservationModel : ObservationCompatibility Fibre.MechanismCandidate
syntheticObservationModel =
  observationCompatibility
    ObservationSpecSynthetic
    SyntheticObservationCompatible

voltageRefinesBehaviour :
  (candidate : Fibre.MechanismCandidate) →
  SyntheticObservationCompatible candidate behaviourPlusVoltage →
  SyntheticObservationCompatible candidate behaviourOnly
voltageRefinesBehaviour Fibre.channelCandidate channelVoltage = channelBehaviour
voltageRefinesBehaviour Fibre.membraneCandidate membraneVoltage = membraneBehaviour
voltageRefinesBehaviour Fibre.pumpCandidate ()

currentRefinesVoltage :
  (candidate : Fibre.MechanismCandidate) →
  SyntheticObservationCompatible candidate behaviourPlusVoltageCurrent →
  SyntheticObservationCompatible candidate behaviourPlusVoltage
currentRefinesVoltage Fibre.channelCandidate channelCurrent = channelVoltage
currentRefinesVoltage Fibre.membraneCandidate ()
currentRefinesVoltage Fibre.pumpCandidate ()

------------------------------------------------------------------------
-- Bridge the anaesthetic candidate set into the existing synthetic error model.
------------------------------------------------------------------------

candidateToSyntheticErrorCandidate :
  Fibre.MechanismCandidate → Error.SyntheticCandidate
candidateToSyntheticErrorCandidate Fibre.channelCandidate = Error.robustCandidate
candidateToSyntheticErrorCandidate Fibre.membraneCandidate = Error.marginalCandidate
candidateToSyntheticErrorCandidate Fibre.pumpCandidate = Error.marginalCandidate

syntheticProductBase :
  ProductRefinementState syntheticObservationModel Error.syntheticOrderedErrorModel
syntheticProductBase =
  productRefinementState
    behaviourOnly
    Error.measuredSuppressedTrace
    Error.looseBound

syntheticVoltageTightFinalA :
  ProductRefinementState syntheticObservationModel Error.syntheticOrderedErrorModel
syntheticVoltageTightFinalA =
  tightenError
    (addObservation syntheticProductBase behaviourPlusVoltage voltageRefinesBehaviour)
    Error.tightBound
    Error.tightLoose

syntheticVoltageTightFinalB :
  ProductRefinementState syntheticObservationModel Error.syntheticOrderedErrorModel
syntheticVoltageTightFinalB =
  addObservation
    (tightenError syntheticProductBase Error.tightBound Error.tightLoose)
    behaviourPlusVoltage
    voltageRefinesBehaviour

syntheticRefinementSquareCommutes :
  syntheticVoltageTightFinalA ≡ syntheticVoltageTightFinalB
syntheticRefinementSquareCommutes = refl

------------------------------------------------------------------------
-- Boundary and weld.
------------------------------------------------------------------------

record ObservationErrorProductBoundary : Set where
  constructor observationErrorProductBoundary
  field
    moreObservationsAndTighterErrorCompose : Bool
    moreObservationsAndTighterErrorComposeIsTrue :
      moreObservationsAndTighterErrorCompose ≡ true

    observationThenErrorEqualsErrorThenObservation : Bool
    observationThenErrorEqualsErrorThenObservationIsTrue :
      observationThenErrorEqualsErrorThenObservation ≡ true

    productRefinementAutomaticallyIdentifiesUniqueMechanism : Bool
    productRefinementAutomaticallyIdentifiesUniqueMechanismIsFalse :
      productRefinementAutomaticallyIdentifiesUniqueMechanism ≡ false

    errorValidationAuthorityStillRequired : Bool
    errorValidationAuthorityStillRequiredIsTrue :
      errorValidationAuthorityStillRequired ≡ true

    syntheticProductWitnessIsEmpiricalTargetIdentification : Bool
    syntheticProductWitnessIsEmpiricalTargetIdentificationIsFalse :
      syntheticProductWitnessIsEmpiricalTargetIdentification ≡ false

canonicalObservationErrorProductBoundary : ObservationErrorProductBoundary
canonicalObservationErrorProductBoundary =
  observationErrorProductBoundary
    true refl
    true refl
    false refl
    true refl
    false refl

record AnaestheticObservationErrorProductWeld : Set₁ where
  constructor anaestheticObservationErrorProductWeld
  field
    mechanismRefinementBoundary : Fibre.MechanismFibreRefinementBoundary
    errorRefinementBoundary : Error.ErrorBoundMechanismFibreBoundary
    productBoundary : ObservationErrorProductBoundary
    productBoundaryIsCanonical :
      productBoundary ≡ canonicalObservationErrorProductBoundary
    sourceAttributionReference : String
    calibrationAuthorityReference : String

open AnaestheticObservationErrorProductWeld public
