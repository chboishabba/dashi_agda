module DASHI.Reasoning.Trialectic369MultiplicityProjectionPositionIndependenceExact where

------------------------------------------------------------------------
-- MULTIPLICITY DESCENT: ELIMINATE REDUNDANT ACTION CHOICE
--
-- DASHI CONTRIBUTION
--
-- The existing multiplicity projection descent contract carries both:
--
--   multiplicityAct : Inertia -> Fin 90 -> Fin 90
--   multiplicityProjectionIntertwines : forall position, ...
--
-- That action is not independent data.  Fix the canonical zero X6 origin;
-- descent is equivalent to equality of multiplicity output at every X6
-- position with its output at this origin.  We reconstruct the action
-- canonically, prove the required intertwining, and prove uniqueness.
--
-- This is an exact compiler theorem, NOT evidence that the actual Monster
-- inertia action has position-independent multiplicity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Data.Empty using (⊥)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

open import DASHI.Algebra.Trit using (zer)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action
import DASHI.Reasoning.Trialectic369MultiplicityProjectionDescentCompilerExact as Descent
import DASHI.Moonshine.Monster3BFiniteSchrodingerDeltaOrbitTransitivityExact as Reach

zeroPosition : H.X6
zeroPosition = H.x6 zer zer zer zer zer zer

multiplicityOutput :
  (source : Action.ActualMonster3BActionRecognition) →
  Descent.ActualInertia source →
  H.X6 →
  Fin 90 →
  Fin 90
multiplicityOutput source inertia position multiplicity =
  proj₂
    (Descent.transportedActualProductAct
      source inertia (position , multiplicity))

record MultiplicityPositionIndependence
    (source : Action.ActualMonster3BActionRecognition) : Set₁ where
  field
    independentOfPosition :
      (inertia : Descent.ActualInertia source) →
      (position : H.X6) →
      (multiplicity : Fin 90) →
      multiplicityOutput source inertia position multiplicity
      ≡ multiplicityOutput source inertia zeroPosition multiplicity

open MultiplicityPositionIndependence public

canonicalMultiplicityAct :
  (source : Action.ActualMonster3BActionRecognition) →
  Descent.ActualInertia source →
  Fin 90 →
  Fin 90
canonicalMultiplicityAct source inertia multiplicity =
  multiplicityOutput source inertia zeroPosition multiplicity

descentFromPositionIndependence :
  (source : Action.ActualMonster3BActionRecognition) →
  MultiplicityPositionIndependence source →
  Descent.MultiplicityProjectionDescent source
descentFromPositionIndependence source witness =
  record
    { multiplicityAct = canonicalMultiplicityAct source
    ; multiplicityProjectionIntertwines =
        independentOfPosition witness
    }

positionIndependenceFromDescent :
  (source : Action.ActualMonster3BActionRecognition) →
  Descent.MultiplicityProjectionDescent source →
  MultiplicityPositionIndependence source
positionIndependenceFromDescent source descent =
  record
    { independentOfPosition = λ inertia position multiplicity →
        trans
          (Descent.multiplicityProjectionIntertwines
            descent inertia position multiplicity)
          (sym
            (Descent.multiplicityProjectionIntertwines
              descent inertia zeroPosition multiplicity))
    }

multiplicityActIsUniquelyDetermined :
  (source : Action.ActualMonster3BActionRecognition) →
  (descent : Descent.MultiplicityProjectionDescent source) →
  (inertia : Descent.ActualInertia source) →
  (multiplicity : Fin 90) →
  Descent.multiplicityAct descent inertia multiplicity
  ≡ canonicalMultiplicityAct source inertia multiplicity
multiplicityActIsUniquelyDetermined source descent inertia multiplicity =
  sym (Descent.multiplicityProjectionIntertwines
    descent inertia zeroPosition multiplicity)

independenceReconstructedFromDescent :
  (source : Action.ActualMonster3BActionRecognition) →
  (descent : Descent.MultiplicityProjectionDescent source) →
  (inertia : Descent.ActualInertia source) →
  (position : H.X6) →
  (multiplicity : Fin 90) →
  independentOfPosition
    (positionIndependenceFromDescent source descent)
    inertia position multiplicity
  ≡
  trans
    (Descent.multiplicityProjectionIntertwines
      descent inertia position multiplicity)
    (sym (Descent.multiplicityProjectionIntertwines
      descent inertia zeroPosition multiplicity))
independenceReconstructedFromDescent source descent inertia position multiplicity =
  refl

------------------------------------------------------------------------
-- A single witnessed departure from zero-position output rejects descent.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Six generator equations suffice by the existing transitive X6 orbit.
------------------------------------------------------------------------

record MultiplicityGeneratorInvariant
    (source : Action.ActualMonster3BActionRecognition) : Set₁ where
  field
    unitTranslationPreservesMultiplicityOutput :
      (inertia : Descent.ActualInertia source) →
      (axis : H.Axis6) →
      (position : H.X6) →
      (multiplicity : Fin 90) →
      multiplicityOutput source inertia (H.translate axis position) multiplicity
      ≡ multiplicityOutput source inertia position multiplicity

open MultiplicityGeneratorInvariant public

generatorInvarianceAlongReachability :
  (source : Action.ActualMonster3BActionRecognition) →
  (witness : MultiplicityGeneratorInvariant source) →
  (inertia : Descent.ActualInertia source) →
  (multiplicity : Fin 90) →
  ∀ {x y} →
  Reach.TranslationReachable x y →
  multiplicityOutput source inertia x multiplicity
  ≡ multiplicityOutput source inertia y multiplicity
generatorInvarianceAlongReachability source witness inertia multiplicity
  Reach.reachableRefl = refl
generatorInvarianceAlongReachability source witness inertia multiplicity
  (Reach.reachableStep {x = x} axis rest) =
  trans
    (sym
      (unitTranslationPreservesMultiplicityOutput
        witness inertia axis x multiplicity))
    (generatorInvarianceAlongReachability
      source witness inertia multiplicity rest)

positionIndependenceFromGenerators :
  (source : Action.ActualMonster3BActionRecognition) →
  MultiplicityGeneratorInvariant source →
  MultiplicityPositionIndependence source
positionIndependenceFromGenerators source witness =
  record
    { independentOfPosition = λ inertia position multiplicity →
        generatorInvarianceAlongReachability
          source witness inertia multiplicity
          (Reach.toZero position)
    }

generatorInvarianceFromPositionIndependence :
  (source : Action.ActualMonster3BActionRecognition) →
  MultiplicityPositionIndependence source →
  MultiplicityGeneratorInvariant source
generatorInvarianceFromPositionIndependence source witness =
  record
    { unitTranslationPreservesMultiplicityOutput =
        λ inertia axis position multiplicity →
          trans
            (independentOfPosition witness
              inertia (H.translate axis position) multiplicity)
            (sym (independentOfPosition witness
              inertia position multiplicity))
    }

descentFromGeneratorInvariance :
  (source : Action.ActualMonster3BActionRecognition) →
  MultiplicityGeneratorInvariant source →
  Descent.MultiplicityProjectionDescent source
descentFromGeneratorInvariance source witness =
  descentFromPositionIndependence source
    (positionIndependenceFromGenerators source witness)

generatorInvarianceFromDescent :
  (source : Action.ActualMonster3BActionRecognition) →
  Descent.MultiplicityProjectionDescent source →
  MultiplicityGeneratorInvariant source
generatorInvarianceFromDescent source descent =
  generatorInvarianceFromPositionIndependence source
    (positionIndependenceFromDescent source descent)

record ZeroPositionCrossDependence
    (source : Action.ActualMonster3BActionRecognition) : Set where
  field
    inertia : Descent.ActualInertia source
    position : H.X6
    multiplicity : Fin 90
    outputDiffersFromOrigin :
      multiplicityOutput source inertia position multiplicity
      ≢ multiplicityOutput source inertia zeroPosition multiplicity

open ZeroPositionCrossDependence public

zeroPositionCrossDependenceRejectsIndependence :
  (source : Action.ActualMonster3BActionRecognition) →
  ZeroPositionCrossDependence source →
  MultiplicityPositionIndependence source →
  ⊥
zeroPositionCrossDependenceRejectsIndependence source witness independent =
  outputDiffersFromOrigin witness
    (independentOfPosition independent
      (inertia witness) (position witness) (multiplicity witness))

zeroPositionCrossDependenceRejectsDescent :
  (source : Action.ActualMonster3BActionRecognition) →
  ZeroPositionCrossDependence source →
  Descent.MultiplicityProjectionDescent source →
  ⊥
zeroPositionCrossDependenceRejectsDescent source witness descent =
  zeroPositionCrossDependenceRejectsIndependence
    source witness (positionIndependenceFromDescent source descent)

zeroPositionWitnessAsExistingCrossDependence :
  (source : Action.ActualMonster3BActionRecognition) →
  ZeroPositionCrossDependence source →
  Descent.MultiplicityCrossDependenceWitness source
zeroPositionWitnessAsExistingCrossDependence source witness =
  record
    { inertia = inertia witness
    ; multiplicity = multiplicity witness
    ; leftPosition = position witness
    ; rightPosition = zeroPosition
    ; outputsDiffer = outputDiffersFromOrigin witness
    }

record Trialectic369MultiplicityPositionIndependenceBoundary : Set where
  constructor trialectic-369-multiplicity-position-independence-boundary
  field
    zeroPositionCanonical : Bool
    actionRecoveredByZeroPositionEvaluation : Bool
    positionIndependenceSufficesForDescent : Bool
    descentImpliesPositionIndependence : Bool
    multiplicityActionPointwiseUnique : Bool
    oneZeroReferenceCounterexampleRejectsDescent : Bool
    sixUnitGeneratorEquationsSuffice : Bool
    descentImpliesAllGeneratorEquations : Bool
    existingX6TranslationReachabilityReused : Bool
    actualMonsterPositionIndependenceEstablishedHere : Bool
    canonicalLinearRepresentationReplacedByFiniteAction : Bool

canonicalTrialectic369MultiplicityPositionIndependenceBoundary :
  Trialectic369MultiplicityPositionIndependenceBoundary
canonicalTrialectic369MultiplicityPositionIndependenceBoundary =
  trialectic-369-multiplicity-position-independence-boundary
    true true true true true true true true true false false
