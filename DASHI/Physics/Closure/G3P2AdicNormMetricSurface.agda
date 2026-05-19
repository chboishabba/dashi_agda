module DASHI.Physics.Closure.G3P2AdicNormMetricSurface where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Ultrametric as UMetric
import DASHI.Physics.Closure.G3ConcreteOperators as G3Concrete
import DASHI.Physics.Closure.G3WaveFunctionOperatorAlgebra as G3Wave

------------------------------------------------------------------------
-- Selected p2-adic norm/metric surface.
--
-- This is the smallest honest metric/norm primitive currently available
-- for the selected G3 lane.  It does not fabricate a real-valued norm or a
-- convergence theorem.  Instead it binds the selected p2-filtration degree
-- relation already proved in G3WaveFunctionOperatorAlgebra to the concrete
-- selected operators P/H/K/mass, and records the exact state p2 exponent
-- increment law.  The downstream missing primitive is the genuine
-- convergence-to-zero law for rescaled boosts.

data G3SelectedP2AdicNormMetricStatus : Set where
  selectedP2AdicNormIndexOnlyNoLimitPromotion :
    G3SelectedP2AdicNormMetricStatus

data G3SelectedP2OperatorDistanceBlocker : Set where
  missingSelectedOperatorNormIndexFunction :
    G3SelectedP2OperatorDistanceBlocker

  missingSelectedOperatorDifferenceNormIndex :
    G3SelectedP2OperatorDistanceBlocker

  missingSelectedOperatorNormIdentityZero :
    G3SelectedP2OperatorDistanceBlocker

  missingSelectedOperatorDifferenceNormSymmetry :
    G3SelectedP2OperatorDistanceBlocker

  missingSelectedOperatorDifferenceNormUltrametric :
    G3SelectedP2OperatorDistanceBlocker

  missingSelectedOperatorRescalingDistanceBound :
    G3SelectedP2OperatorDistanceBlocker

SelectedOperator :
  Set
SelectedOperator =
  G3Wave.WaveFunctionOperator

selectedZeroOperator :
  SelectedOperator
selectedZeroOperator ψ =
  G3Wave.zeroψ

record G3SelectedP2OperatorDistancePrimitive : Setω where
  field
    operatorDistance :
      SelectedOperator →
      SelectedOperator →
      Nat

    operatorDistanceIdentityZero :
      (A : SelectedOperator) →
      operatorDistance A A ≡ zero

    operatorDistanceSymmetric :
      (A B : SelectedOperator) →
      operatorDistance A B ≡ operatorDistance B A

    operatorDistanceUltrametric :
      (A B C : SelectedOperator) →
      operatorDistance A C
      ≤
      UMetric.max (operatorDistance A B) (operatorDistance B C)

    distanceTiedToSelectedNormIndex :
      List String

selectedP2OperatorUltrametricFromDistancePrimitive :
  G3SelectedP2OperatorDistancePrimitive →
  UMetric.Ultrametric SelectedOperator
selectedP2OperatorUltrametricFromDistancePrimitive distance =
  record
    { d =
        G3SelectedP2OperatorDistancePrimitive.operatorDistance distance
    ; id-zero =
        G3SelectedP2OperatorDistancePrimitive.operatorDistanceIdentityZero
          distance
    ; symmetric =
        G3SelectedP2OperatorDistancePrimitive.operatorDistanceSymmetric
          distance
    ; ultratriangle =
        G3SelectedP2OperatorDistancePrimitive.operatorDistanceUltrametric
          distance
    }

record G3SelectedP2OperatorDistanceConstructionAttempt : Setω where
  field
    candidateDistanceShape :
      String

    existingNormIndexEvidence :
      List String

    exactDistanceBlockers :
      List G3SelectedP2OperatorDistanceBlocker

    exactDistanceBlockerNames :
      List String

canonicalSelectedP2OperatorDistanceConstructionAttempt :
  G3SelectedP2OperatorDistanceConstructionAttempt
canonicalSelectedP2OperatorDistanceConstructionAttempt =
  record
    { candidateDistanceShape =
        "operatorDistance A B should be the selected p2 norm-index of waveFunctionOperatorSubtraction A B"
    ; existingNormIndexEvidence =
        "G3Wave.waveFunctionOperatorSubtraction defines the selected operator difference A - B"
        ∷ "G3Wave.SelectedOperatorP2Degree is available as an indexed proof relation WaveFunctionOperator -> Nat -> Set"
        ∷ "G3Wave.selectedPψDegreeZero, selectedHψDegreeOne, selectedKψDegreeOne, and selectedIdentityDegreeZero inhabit generator norm indices"
        ∷ "G3Wave.selectedCommutatorDegree transports selected p2-degree evidence across commutators by addition"
        ∷ []
    ; exactDistanceBlockers =
        missingSelectedOperatorNormIndexFunction
        ∷ missingSelectedOperatorDifferenceNormIndex
        ∷ missingSelectedOperatorNormIdentityZero
        ∷ missingSelectedOperatorDifferenceNormSymmetry
        ∷ missingSelectedOperatorDifferenceNormUltrametric
        ∷ missingSelectedOperatorRescalingDistanceBound
        ∷ []
    ; exactDistanceBlockerNames =
        "selectedOperatorNormIndex : WaveFunctionOperator -> Nat, with SelectedOperatorP2Degree A (selectedOperatorNormIndex A)"
        ∷ "selectedOperatorDifferenceNormIndex : (A B : WaveFunctionOperator) -> Nat, tied to SelectedOperatorP2Degree (waveFunctionOperatorSubtraction A B)"
        ∷ "selectedOperatorNormIdentityZero : (A B : WaveFunctionOperator) -> selectedOperatorDifferenceNormIndex A B ≡ zero iff A ≡ B"
        ∷ "selectedOperatorDifferenceNormSymmetry : (A B : WaveFunctionOperator) -> selectedOperatorDifferenceNormIndex A B ≡ selectedOperatorDifferenceNormIndex B A"
        ∷ "selectedOperatorDifferenceNormUltrametric : (A B C : WaveFunctionOperator) -> selectedOperatorDifferenceNormIndex A C ≤ max (selectedOperatorDifferenceNormIndex A B) (selectedOperatorDifferenceNormIndex B C)"
        ∷ "selectedOperatorRescalingDistanceBound : p2-level rescaling lowers selected K distance to selectedZeroOperator strongly enough to produce the Cauchy/zero-limit witness"
        ∷ []
    }

record G3SelectedP2OperatorRescalingPrimitive
  (distance : G3SelectedP2OperatorDistancePrimitive) : Setω where
  field
    rescaleAtP2Level :
      Nat →
      SelectedOperator →
      SelectedOperator

    rescaledBoostSequence :
      G3Concrete.G3SpatialDirection →
      Nat →
      SelectedOperator

    rescaledBoostSequenceIsSelectedKRescaled :
      (d : G3Concrete.G3SpatialDirection) →
      (n : Nat) →
      rescaledBoostSequence d n
      ≡
      rescaleAtP2Level n (G3Wave.selectedKψ d)

    zeroLimitOperator :
      SelectedOperator

    zeroLimitOperatorIsSelectedZero :
      zeroLimitOperator ≡ selectedZeroOperator

    exactRescalingSemantics :
      List String

record G3SelectedP2AdicNormMetricSurface : Setω where
  field
    status :
      G3SelectedP2AdicNormMetricStatus

    stateCarrier :
      Set

    stateCarrierIsSelected :
      stateCarrier ≡ G3Wave.SelectedG3State

    operatorCarrier :
      Set

    operatorCarrierIsSelected :
      operatorCarrier ≡ G3Wave.WaveFunctionOperator

    p2Exponent :
      G3Wave.SelectedG3State →
      Nat

    p2ExponentIsSelectedFiltration :
      p2Exponent ≡ G3Concrete.selectedP2Filtration

    p2BumpIncrementsExponent :
      (v : G3Wave.SelectedG3State) →
      p2Exponent (G3Concrete.selectedH v) ≡ suc (p2Exponent v)

    normEvidence :
      G3Wave.WaveFunctionOperator →
      Nat →
      Set

    normEvidenceIsSelectedDegree :
      normEvidence ≡ G3Wave.SelectedOperatorP2Degree

    generator :
      Set

    generatorIsSelected :
      generator ≡ G3Wave.G3SelectedAssociatedGradedGenerator

    generatorOperator :
      G3Wave.G3SelectedAssociatedGradedGenerator →
      G3Wave.WaveFunctionOperator

    generatorOperatorIsSelected :
      generatorOperator ≡ G3Wave.selectedGeneratorOperator

    generatorNormIndex :
      G3Wave.G3SelectedAssociatedGradedGenerator →
      Nat

    generatorNormIndexIsSelectedDegree :
      generatorNormIndex ≡ G3Wave.selectedGeneratorDegree

    generatorNormEvidence :
      (g : G3Wave.G3SelectedAssociatedGradedGenerator) →
      normEvidence (generatorOperator g) (generatorNormIndex g)

    spatialMomentumNormZero :
      (d : G3Concrete.G3SpatialDirection) →
      normEvidence (G3Wave.selectedPψ d) zero

    hamiltonianNormOne :
      normEvidence G3Wave.selectedHψ (suc zero)

    boostNormOne :
      (d : G3Concrete.G3SpatialDirection) →
      normEvidence (G3Wave.selectedKψ d) (suc zero)

    massCentralSlotNormZero :
      normEvidence (λ ψ → ψ) zero

    selectedZeroOperatorCarrier :
      G3Wave.WaveFunctionOperator

    selectedZeroOperatorIsCanonical :
      selectedZeroOperatorCarrier ≡ selectedZeroOperator

    requiredOperatorDistancePrimitiveName :
      String

    operatorDistanceConstructionAttempt :
      G3SelectedP2OperatorDistanceConstructionAttempt

    exactOperatorDistanceBlockers :
      List G3SelectedP2OperatorDistanceBlocker

    requiredOperatorRescalingPrimitiveName :
      String

    contractionParameter :
      Nat →
      Nat

    contractionParameterIsSuccessor :
      (n : Nat) →
      contractionParameter n ≡ suc n

    exactRemainingLimitPrimitive :
      List String

canonicalG3SelectedP2AdicNormMetricSurface :
  G3SelectedP2AdicNormMetricSurface
canonicalG3SelectedP2AdicNormMetricSurface =
  record
    { status =
        selectedP2AdicNormIndexOnlyNoLimitPromotion
    ; stateCarrier =
        G3Wave.SelectedG3State
    ; stateCarrierIsSelected =
        refl
    ; operatorCarrier =
        G3Wave.WaveFunctionOperator
    ; operatorCarrierIsSelected =
        refl
    ; p2Exponent =
        G3Concrete.selectedP2Filtration
    ; p2ExponentIsSelectedFiltration =
        refl
    ; p2BumpIncrementsExponent =
        G3Concrete.selectedHFiltrationStep
    ; normEvidence =
        G3Wave.SelectedOperatorP2Degree
    ; normEvidenceIsSelectedDegree =
        refl
    ; generator =
        G3Wave.G3SelectedAssociatedGradedGenerator
    ; generatorIsSelected =
        refl
    ; generatorOperator =
        G3Wave.selectedGeneratorOperator
    ; generatorOperatorIsSelected =
        refl
    ; generatorNormIndex =
        G3Wave.selectedGeneratorDegree
    ; generatorNormIndexIsSelectedDegree =
        refl
    ; generatorNormEvidence =
        G3Wave.selectedGeneratorHasDegree
    ; spatialMomentumNormZero =
        G3Wave.selectedPψDegreeZero
    ; hamiltonianNormOne =
        G3Wave.selectedHψDegreeOne
    ; boostNormOne =
        G3Wave.selectedKψDegreeOne
    ; massCentralSlotNormZero =
        G3Wave.selectedIdentityDegreeZero
    ; selectedZeroOperatorCarrier =
        selectedZeroOperator
    ; selectedZeroOperatorIsCanonical =
        refl
    ; requiredOperatorDistancePrimitiveName =
        "G3SelectedP2OperatorDistancePrimitive: Nat-valued distance on selected wave-function operators with identity/symmetry/ultrametric laws tied to SelectedOperatorP2Degree"
    ; operatorDistanceConstructionAttempt =
        canonicalSelectedP2OperatorDistanceConstructionAttempt
    ; exactOperatorDistanceBlockers =
        G3SelectedP2OperatorDistanceConstructionAttempt.exactDistanceBlockers
          canonicalSelectedP2OperatorDistanceConstructionAttempt
    ; requiredOperatorRescalingPrimitiveName =
        "G3SelectedP2OperatorRescalingPrimitive: p2-level rescaling operation whose selected K sequence is Cauchy and limits to selectedZeroOperator"
    ; contractionParameter =
        suc
    ; contractionParameterIsSuccessor =
        λ _ → refl
    ; exactRemainingLimitPrimitive =
        "Need selectedOperatorNormIndex : WaveFunctionOperator -> Nat with evidence tying it to SelectedOperatorP2Degree"
        ∷ "Need selectedOperatorDifferenceNormIndex for waveFunctionOperatorSubtraction A B"
        ∷ "Need selectedOperatorNormIdentityZero for the difference norm"
        ∷ "Need selectedOperatorDifferenceNormSymmetry for the difference norm"
        ∷ "Need selectedOperatorDifferenceNormUltrametric for the difference norm"
        ∷ "Need G3SelectedP2OperatorDistancePrimitive once those norm/difference laws are accepted"
        ∷ "Need G3SelectedP2OperatorRescalingPrimitive; no p2-level scalar/rescale action on WaveFunctionOperator is currently accepted"
        ∷ "Need selectedOperatorRescalingDistanceBound proving rescaled selected K approaches selectedZeroOperator in the accepted distance"
        ∷ "Need a selected p2-adic convergence-to-zero law for rescaled boosts once distance and rescaling primitives exist"
        ∷ "Need a limit predicate compatible with the Schrodinger SES contraction carrier"
        ∷ "Need quotient/associated-graded carrier compatibility before final G3 promotion"
        ∷ []
    }
