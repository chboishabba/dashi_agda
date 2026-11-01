module DASHI.Physics.Closure.NSTriadKNReconstructedOrbitCoordinateGrowthNoGoRound62Exact where

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
-- ROUND 62 FINITE-FLOW REPRESENTATION AUDIT
--
-- `ReconstructedPhysicalState` stores one list called
-- `positiveOrbitCoefficients`.  The same-object Fourier system expands each
-- stored representative into the two retained modes k,-k.  The generic exact
-- Galerkin RHS builder then maps one output coefficient over EVERY retained
-- mode and stores that entire output list back as `positiveOrbitCoefficients`.
--
-- Pure list arithmetic therefore gives
--
--   n stored representatives
--     -> 2n retained modes
--     -> 2n stored RHS coefficients
--     -> 4n reconstructed RHS modes.
--
-- This is a representation theorem, not a PDE estimate.  It does not challenge
-- the literal RHS formula: every generated coefficient is still the exact
-- viscous-plus-exhaustive-quadratic coefficient.  It shows that the unrestricted
-- list carrier is not yet the fixed-dimensional one-representative-per-reality-
-- orbit coordinate space required by Picard--Lindelof.
--
-- The needed repair is precise: for each fixed cutoff choose one canonical
-- representative of every nonzero orbit k ~ -k; evolve only those coordinates;
-- reconstruct the opposite sheet by conjugation.  The already-proved summed
-- nonlinear and viscous Fourier-reality theorems determine the omitted RHS
-- coordinates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Coefficient
import DASHI.Physics.Closure.NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact as Concrete
import DASHI.Physics.Closure.NSTriadKNSameCarrierSameObjectRound31Exact as Same

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

twice : Nat → Nat
twice zero = zero
twice (suc n) = suc (suc (twice n))

fourTimes : Nat → Nat
fourTimes n = twice (twice n)

------------------------------------------------------------------------
-- Exact list used by the same-object state reconstruction.
------------------------------------------------------------------------

reconstructedModesOf :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  List (Phase.TransverseModeCoefficient F E) → List Z3.FourierMode
reconstructedModesOf [] = []
reconstructedModesOf (coefficient ∷ rest) =
  Phase.coefficientMode coefficient
  ∷ Phase.reconstructedNegativeMode coefficient
  ∷ reconstructedModesOf rest

reconstructedModesOfCount :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (coefficients : List (Phase.TransverseModeCoefficient F E)) →
  length (reconstructedModesOf coefficients)
  ≡ twice (length coefficients)
reconstructedModesOfCount [] = refl
reconstructedModesOfCount (_ ∷ rest) =
  cong suc (cong suc (reconstructedModesOfCount rest))

sameObjectReconstructedModesMeaning :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (state : State.ReconstructedPhysicalState F E) →
  Same.reconstructedStateModes state
  ≡ reconstructedModesOf (State.positiveOrbitCoefficients state)
sameObjectReconstructedModesMeaning state = refl

reconstructedStateModesCount :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (state : State.ReconstructedPhysicalState F E) →
  length (Same.reconstructedStateModes state)
  ≡ twice (length (State.positiveOrbitCoefficients state))
reconstructedStateModesCount state =
  trans
    (cong length (sameObjectReconstructedModesMeaning state))
    (reconstructedModesOfCount (State.positiveOrbitCoefficients state))

------------------------------------------------------------------------
-- The concrete RHS map returns exactly one stored coefficient for each source
-- retained mode.
------------------------------------------------------------------------

mapConcreteCoefficientsCount :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : Concrete.StateIndexedPhysicalGalerkinSystem F E)
    (state : State.ReconstructedPhysicalState F E)
    (source : List Z3.FourierMode)
    (sourceIncluded : ∀ mode →
      mode Cube.∈ source →
      mode Cube.∈ Audit.modes
        (Coefficient.finiteSystem
          (Concrete.physicalSystemAt builder state))) →
  length (Concrete.mapConcreteCoefficients
    builder state source sourceIncluded)
  ≡ length source
mapConcreteCoefficientsCount builder state [] sourceIncluded = refl
mapConcreteCoefficientsCount builder state (_ ∷ rest) sourceIncluded =
  cong suc
    (mapConcreteCoefficientsCount builder state rest
      (λ selected selectedMember →
        sourceIncluded selected (Cube.there selectedMember)))

concreteOutputCoefficientsCount :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : Concrete.StateIndexedPhysicalGalerkinSystem F E)
    (state : State.ReconstructedPhysicalState F E) →
  length (Concrete.concreteOutputCoefficients builder state)
  ≡ length
      (Audit.modes
        (Coefficient.finiteSystem
          (Concrete.physicalSystemAt builder state)))
concreteOutputCoefficientsCount builder state =
  mapConcreteCoefficientsCount builder state
    (Audit.modes
      (Coefficient.finiteSystem
        (Concrete.physicalSystemAt builder state)))
    (λ mode member → member)

------------------------------------------------------------------------
-- Same-object builder: retained modes are exactly the +/- reconstruction of the
-- input state.  Hence the concrete RHS stores twice as many representatives as
-- the input state stores.
------------------------------------------------------------------------

sameObjectConcreteOutputPositiveCount :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : Same.SameCarrierSameObjectGalerkinBuilder F E)
    (state : State.ReconstructedPhysicalState F E) →
  length
    (State.positiveOrbitCoefficients
      (Same.sameObjectPhysicalGalerkinVectorField builder state))
  ≡ twice (length (State.positiveOrbitCoefficients state))
sameObjectConcreteOutputPositiveCount builder state =
  trans
    (concreteOutputCoefficientsCount
      (Same.forgetSameCarrierSameObject builder) state)
    (trans
      (cong length (Same.retainedModesExact builder state))
      (reconstructedStateModesCount state))

sameObjectConcreteOutputReconstructedCount :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : Same.SameCarrierSameObjectGalerkinBuilder F E)
    (state : State.ReconstructedPhysicalState F E) →
  length
    (Same.reconstructedStateModes
      (Same.sameObjectPhysicalGalerkinVectorField builder state))
  ≡ fourTimes (length (State.positiveOrbitCoefficients state))
sameObjectConcreteOutputReconstructedCount builder state =
  trans
    (reconstructedStateModesCount
      (Same.sameObjectPhysicalGalerkinVectorField builder state))
    (cong twice (sameObjectConcreteOutputPositiveCount builder state))

rawReconstructedListIsNotYetFixedCoordinateCarrier : Bool
rawReconstructedListIsNotYetFixedCoordinateCarrier = true

canonicalOrbitRepresentativeCarrierRequiredForPicard : Bool
canonicalOrbitRepresentativeCarrierRequiredForPicard = true

rawReconstructedListIsNotYetFixedCoordinateCarrierIsTrue :
  rawReconstructedListIsNotYetFixedCoordinateCarrier ≡ true
rawReconstructedListIsNotYetFixedCoordinateCarrierIsTrue = refl

canonicalOrbitRepresentativeCarrierRequiredForPicardIsTrue :
  canonicalOrbitRepresentativeCarrierRequiredForPicard ≡ true
canonicalOrbitRepresentativeCarrierRequiredForPicardIsTrue = refl
