module DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the Round-28 dependent selector on the actual reconstruction
-- carrier used by the finite Fourier lane. Positive-orbit coefficients carry
-- transversality proofs; negative coefficients are reconstructed by complex
-- conjugation and proved transverse; zero modes are excluded dependently.
-- Since all constraints are intrinsic to the state type, the three selectors
-- are literal identities. The still-open theorem is that the full physical
-- Galerkin vector field maps this state type to itself.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNCommutingPhysicalCarrierSelectorRound28Exact as Selector

record ReconstructedPhysicalState
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set r where
  constructor reconstructed-physical-state
  field
    positiveOrbitCoefficients :
      List (Phase.TransverseModeCoefficient F E)
    positiveModesNonzero :
      ∀ coefficient →
      coefficient Cube.∈ positiveOrbitCoefficients →
      Z3.NonZeroMode (Phase.coefficientMode coefficient)

open ReconstructedPhysicalState public

negateNonzeroMode :
  (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  Z3.NonZeroMode (Z3.negateMode mode)
negateNonzeroMode mode nonzero = record
  { notZero = λ negatedIsZero →
      Z3.notZero nonzero
        (trans
          (sym (Symmetry.negateModeInvolutive mode))
          (trans
            (cong Z3.negateMode negatedIsZero)
            refl))
  }

reconstructedNegativeModeNonzero :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (state : ReconstructedPhysicalState F E)
    (coefficient : Phase.TransverseModeCoefficient F E) →
  coefficient Cube.∈ positiveOrbitCoefficients state →
  Z3.NonZeroMode (Phase.reconstructedNegativeMode coefficient)
reconstructedNegativeModeNonzero state coefficient member =
  negateNonzeroMode
    (Phase.coefficientMode coefficient)
    (positiveModesNonzero state coefficient member)

reconstructedNegativeCoefficientTransverse :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (coefficient : Phase.TransverseModeCoefficient F E) →
  C3.bilinearDot3
    (C3.modeVector E (Phase.reconstructedNegativeMode coefficient))
    (Phase.reconstructedNegativeValue coefficient)
  ≡ C3.complexZero F
reconstructedNegativeCoefficientTransverse =
  Phase.canonicalReconstructedNegativeIsTransverse

reconstructedPhysicalSelectors :
  ∀ {r} (F : C3.RealField r) (E : C3.IntegerEmbedding F) →
  Selector.CommutingPhysicalSelectors (ReconstructedPhysicalState F E)
reconstructedPhysicalSelectors F E = record
  { leray = λ state → state
  ; reality = λ state → state
  ; center = λ state → state
  ; lerayIdempotent = λ state → refl
  ; realityIdempotent = λ state → refl
  ; centerIdempotent = λ state → refl
  ; lerayRealityCommute = λ state → refl
  ; lerayCenterCommute = λ state → refl
  ; realityCenterCommute = λ state → refl
  }

reconstructedPhysicalCarrier :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  ReconstructedPhysicalState F E →
  Selector.PhysicalCarrier (reconstructedPhysicalSelectors F E)
reconstructedPhysicalCarrier state =
  Selector.physical-carrier state refl refl refl

reconstructedPhysicalSelectorFixesState :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (state : ReconstructedPhysicalState F E) →
  Selector.physicalSelector (reconstructedPhysicalSelectors F E) state
  ≡ state
reconstructedPhysicalSelectorFixesState state = refl

reconstructedPhysicalStateSelectorInstantiated : Bool
reconstructedPhysicalStateSelectorInstantiated = true

fullGalerkinVectorFieldMapsReconstructedState : Bool
fullGalerkinVectorFieldMapsReconstructedState = false

reconstructedPhysicalStateSelectorInstantiatedIsTrue :
  reconstructedPhysicalStateSelectorInstantiated ≡ true
reconstructedPhysicalStateSelectorInstantiatedIsTrue = refl

fullGalerkinVectorFieldMapsReconstructedStateIsFalse :
  fullGalerkinVectorFieldMapsReconstructedState ≡ false
fullGalerkinVectorFieldMapsReconstructedStateIsFalse = refl
