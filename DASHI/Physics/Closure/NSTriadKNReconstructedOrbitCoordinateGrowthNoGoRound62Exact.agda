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
-- The reconstructed physical state stores ONE list called
-- `positiveOrbitCoefficients`; its retained Fourier modes are then expanded as
--
--   k_1,-k_1,k_2,-k_2,... .
--
-- The mature concrete Galerkin producer is exact coefficient-wise, but its
-- generic construction maps the RHS over the ENTIRE retained-mode list and
-- stores every resulting coefficient back into `positiveOrbitCoefficients`.
-- Therefore the generic composition does not preserve the intended
-- one-representative-per-reality-orbit coordinate count:
--
--   input positive representatives       : n
--   input reconstructed retained modes   : 2 n
--   output stored "positive" coefficients: 2 n
--   output reconstructed retained modes  : 4 n.
--
-- This file proves those list-count identities definitionally, independently
-- of any PDE estimate.  It does NOT say the Fourier RHS is mathematically
-- wrong: every generated coefficient is still the exact literal RHS.  It says
-- this unrestricted LIST representation is not yet the fixed-dimensional ODE
-- coordinate carrier needed by Picard--Lindelof.
--
-- The repair is precise: fix a cutoff-dependent canonical representative of
-- each nonzero orbit k ~ -k, store/evolve only those coordinates, and
-- reconstruct the opposite sheet by conjugation.  The already-proved Fourier
-- reality theorem then determines the discarded derivative coordinates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
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
-- Any reconstructed physical state has exactly two retained modes per stored
-- representative.
------------------------------------------------------------------------

reconstructedStateModesCount :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (state : State.ReconstructedPhysicalState F E) →
  length (Same.reconstructedStateModes state)
  ≡ twice (length (State.positiveOrbitCoefficients state))
reconstructedStateModesCount {F = F} {E = E} state =
  go (State.positiveOrbitCoefficients state)
  where
  go :
    (coefficients : List (Phase.TransverseModeCoefficient F E)) →
    length (Same.reconstructedStateModes
      (State.reconstructed-physical-state coefficients
        (λ coefficient member →
          State.positiveModesNonzero state coefficient
            (transportMember coefficients member))))
    ≡ twice (length coefficients)
  go [] = refl
  go (coefficient ∷ rest) = cong suc (cong suc (go rest))

  transportMember :
    (coefficients : List (Phase.TransverseModeCoefficient F E)) →
    ∀ coefficient → coefficient State.∈ coefficients →
    coefficient State.∈ State.positiveOrbitCoefficients state
  transportMember coefficients coefficient member =
    transportByPrefix coefficients member

  transportByPrefix :
    (coefficients : List (Phase.TransverseModeCoefficient F E)) →
    ∀ {coefficient} → coefficient State.∈ coefficients →
    coefficient State.∈ State.positiveOrbitCoefficients state
  transportByPrefix coefficients member = member

------------------------------------------------------------------------
-- The concrete map produces exactly one output coefficient for every source
-- retained mode.
------------------------------------------------------------------------

mapConcreteCoefficientsCount :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : Concrete.StateIndexedPhysicalGalerkinSystem F E)
    (state : State.ReconstructedPhysicalState F E)
    (source : List DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode)
    (sourceIncluded : ∀ mode →
      DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier._∈_
        mode source →
      DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier._∈_
        mode
        (DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.modes
          (DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact.finiteSystem
            (Concrete.physicalSystemAt builder state)))) →
  length (Concrete.mapConcreteCoefficients
    builder state source sourceIncluded)
  ≡ length source
mapConcreteCoefficientsCount builder state [] sourceIncluded = refl
mapConcreteCoefficientsCount builder state (_ ∷ rest) sourceIncluded =
  cong suc
    (mapConcreteCoefficientsCount builder state rest
      (λ selected selectedMember →
        sourceIncluded selected
          (DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier.there
            selectedMember)))

------------------------------------------------------------------------
-- For a same-object builder, the concrete output stored-representative count is
-- exactly the input reconstructed-mode count, hence twice the input positive
-- count.
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
    (mapConcreteCoefficientsCount
      (Same.forgetSameCarrierSameObject builder)
      state
      (DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.modes
        (DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact.finiteSystem
          (Same.physicalSystemAt builder state)))
      (λ mode member → member))
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
