module DASHI.Physics.Closure.NSTriadKNCanonicalRealityOrbitLookupRound63Exact where

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
-- ROUND 63 A0 LOOKUP CLOSURE
--
-- A canonical fixed-cutoff state stores one transverse coefficient for each
-- mode in the Round63 one-sheet reality-orbit list, in exactly that list order.
-- From that single structural fact this module DERIVES the two compatibility
-- laws required by the mature Round33 executable velocity lookup:
--
--   * equal stored modes have equal stored values, because the canonical mode
--     list is duplicate-free;
--   * no positive stored mode can coincide with the reconstructed negative of
--     another stored mode, because the one-sheet carrier never contains both
--     k and -k.
--
-- Thus `SameObjectCompatibleState` is not another certificate assumption for
-- canonical states; it is a theorem of the fixed orbit carrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (map)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNSameObjectLookupConsistencyRound33Exact as Lookup
import DASHI.Physics.Closure.NSTriadKNCanonicalRealityOrbitCarrierRound63Exact as Orbit

record CanonicalOrbitPhysicalState
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (cutoff : Nat) : Set r where
  constructor canonical-orbit-physical-state
  field
    reconstructedState : State.ReconstructedPhysicalState F E
    positiveModesExact :
      map Phase.coefficientMode
        (State.positiveOrbitCoefficients reconstructedState)
      ≡ Orbit.canonicalRealityOrbitModes cutoff

open CanonicalOrbitPhysicalState public

modeMemberFromCoefficientMember :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {coefficients : List (Phase.TransverseModeCoefficient F E)}
    {coefficient} →
  coefficient State.∈ coefficients →
  Phase.coefficientMode coefficient
    Cube.∈ map Phase.coefficientMode coefficients
modeMemberFromCoefficientMember {coefficients = []} ()
modeMemberFromCoefficientMember {coefficients = head ∷ tail}
    (State.here refl) = Cube.here refl
modeMemberFromCoefficientMember {coefficients = head ∷ tail}
    (State.there member) =
  Cube.there (modeMemberFromCoefficientMember member)

canonicalModeMemberFromCoefficientMember :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {cutoff}
    (state : CanonicalOrbitPhysicalState F E cutoff)
    {coefficient} →
  coefficient State.∈
    State.positiveOrbitCoefficients (reconstructedState state) →
  Phase.coefficientMode coefficient
    Cube.∈ Orbit.canonicalRealityOrbitModes cutoff
canonicalModeMemberFromCoefficientMember state member =
  subst
    (λ modes → Phase.coefficientMode _ Cube.∈ modes)
    (positiveModesExact state)
    (modeMemberFromCoefficientMember member)

modeNoDuplicatesFromCanonicalState :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {cutoff}
    (state : CanonicalOrbitPhysicalState F E cutoff) →
  Cube.NoDuplicates
    (map Phase.coefficientMode
      (State.positiveOrbitCoefficients (reconstructedState state)))
modeNoDuplicatesFromCanonicalState {cutoff = cutoff} state =
  subst Cube.NoDuplicates
    (sym (positiveModesExact state))
    (Orbit.canonicalRealityOrbitModesNoDuplicates cutoff)

positiveFunctionalFromModeNoDuplicates :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {coefficients : List (Phase.TransverseModeCoefficient F E)} →
  Cube.NoDuplicates (map Phase.coefficientMode coefficients) →
  Lookup.PositiveModeFunctional coefficients
positiveFunctionalFromModeNoDuplicates Cube.unique[] left right () rightMember sameMode
positiveFunctionalFromModeNoDuplicates
    (Cube.unique∷ {x = headMode} {xs = tailModes} headFresh tailUnique)
    left right (State.here refl) (State.here refl) sameMode = refl
positiveFunctionalFromModeNoDuplicates
    (Cube.unique∷ {x = headMode} {xs = tailModes} headFresh tailUnique)
    left right (State.here refl) (State.there rightMember) sameMode =
  ⊥-elim
    (headFresh
      (subst
        (λ selected → selected Cube.∈ tailModes)
        (sym sameMode)
        (modeMemberFromCoefficientMember rightMember)))
positiveFunctionalFromModeNoDuplicates
    (Cube.unique∷ {x = headMode} {xs = tailModes} headFresh tailUnique)
    left right (State.there leftMember) (State.here refl) sameMode =
  ⊥-elim
    (headFresh
      (subst
        (λ selected → selected Cube.∈ tailModes)
        sameMode
        (modeMemberFromCoefficientMember leftMember)))
positiveFunctionalFromModeNoDuplicates
    (Cube.unique∷ {x = headMode} {xs = tailModes} headFresh tailUnique)
    left right (State.there leftMember) (State.there rightMember) sameMode =
  positiveFunctionalFromModeNoDuplicates tailUnique
    left right leftMember rightMember sameMode

canonicalPositiveFunctional :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {cutoff}
    (state : CanonicalOrbitPhysicalState F E cutoff) →
  Lookup.PositiveModeFunctional
    (State.positiveOrbitCoefficients (reconstructedState state))
canonicalPositiveFunctional state =
  positiveFunctionalFromModeNoDuplicates
    (modeNoDuplicatesFromCanonicalState state)

canonicalPositiveNegativeCompatibility :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {cutoff}
    (state : CanonicalOrbitPhysicalState F E cutoff) →
  Lookup.PositiveNegativeCompatible
    (State.positiveOrbitCoefficients (reconstructedState state))
canonicalPositiveNegativeCompatibility state
    positive source positiveMember sourceMember samePhysicalMode =
  ⊥-elim
    (Orbit.canonicalAndNegativeCannotBothOccur
      (canonicalModeMemberFromCoefficientMember state sourceMember)
      (subst
        (λ selected → selected Cube.∈ Orbit.canonicalRealityOrbitModes _)
        samePhysicalMode
        (canonicalModeMemberFromCoefficientMember state positiveMember)))

canonicalOrbitStateCompatible :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {cutoff}
    (state : CanonicalOrbitPhysicalState F E cutoff) →
  Lookup.SameObjectCompatibleState F E (reconstructedState state)
canonicalOrbitStateCompatible state =
  Lookup.same-object-compatible-state
    (canonicalPositiveFunctional state)
    (canonicalPositiveNegativeCompatibility state)

canonicalOrbitLookupCompatibilityClosed : Bool
canonicalOrbitLookupCompatibilityClosed = true

canonicalOrbitLookupCompatibilityClosedIsTrue :
  canonicalOrbitLookupCompatibilityClosed ≡ true
canonicalOrbitLookupCompatibilityClosedIsTrue = refl
