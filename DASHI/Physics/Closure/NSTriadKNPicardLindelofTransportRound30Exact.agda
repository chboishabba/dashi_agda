module DASHI.Physics.Closure.NSTriadKNPicardLindelofTransportRound30Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Émile Picard.
-- Title: "Traité d'analyse" (successive-approximation method).
-- DOI: not applicable to the cited historical book.
--
-- Author: Ernst Lindelöf.
-- Title: "Sur l'application de la méthode des approximations successives aux
-- équations différentielles ordinaires du premier ordre".
-- DOI: not applicable to the 1894 historical article.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact analytic library interface needed by the finite Galerkin
-- lane and prove that a local coordinate flow transports through the Round-30
-- physical-coordinate equivalence.  The derivative equation, initial value
-- and coordinatewise uniqueness are preserved.  The external real
-- Picard--Lindelöf implementation must provide the authority record; all
-- DASHI-specific transport is machine-checked and uses no function
-- extensionality axiom.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial
import DASHI.Physics.Closure.NSTriadKNFinitePhysicalCoordinateEquivalenceRound30Exact as Coordinates

record CoordinateTrajectory
    {timeLevel : Level}
    (Time : Set timeLevel) : Set (lsuc timeLevel) where
  field
    stateAt : Time → Polynomial.Assignment
    derivativeAt : Time → Polynomial.Assignment
open CoordinateTrajectory public

record CoordinateODESolution
    {timeLevel : Level}
    {Time : Set timeLevel}
    (vectorField : Polynomial.Assignment → Polynomial.Assignment)
    (trajectory : CoordinateTrajectory Time) : Set timeLevel where
  field
    derivativeEquation : ∀ time variable →
      derivativeAt trajectory time variable
      ≡ vectorField (stateAt trajectory time) variable
open CoordinateODESolution public

record CoordinatePicardLindelofAuthority
    {timeLevel : Level}
    (Time : Set timeLevel) : Set (lsuc timeLevel) where
  field
    InitialTime : Set timeLevel
    initialTimeValue : InitialTime → Time

    LocallyLipschitz :
      (Polynomial.Assignment → Polynomial.Assignment) → Set

    localTrajectory :
      (vectorField : Polynomial.Assignment → Polynomial.Assignment) →
      LocallyLipschitz vectorField →
      Polynomial.Assignment → CoordinateTrajectory Time

    localTrajectorySolves :
      (vectorField : Polynomial.Assignment → Polynomial.Assignment) →
      (lipschitz : LocallyLipschitz vectorField) →
      (initial : Polynomial.Assignment) →
      CoordinateODESolution vectorField
        (localTrajectory vectorField lipschitz initial)

    localTrajectoryInitial :
      (vectorField : Polynomial.Assignment → Polynomial.Assignment) →
      (lipschitz : LocallyLipschitz vectorField) →
      (initial : Polynomial.Assignment) →
      (time : InitialTime) →
      stateAt (localTrajectory vectorField lipschitz initial)
        (initialTimeValue time)
      ≡ initial

    localUniqueness :
      (vectorField : Polynomial.Assignment → Polynomial.Assignment) →
      LocallyLipschitz vectorField →
      (initial : Polynomial.Assignment) →
      (left right : CoordinateTrajectory Time) →
      CoordinateODESolution vectorField left →
      CoordinateODESolution vectorField right →
      (time : InitialTime) →
      stateAt left (initialTimeValue time) ≡ initial →
      stateAt right (initialTimeValue time) ≡ initial →
      ∀ localTime variable →
      stateAt left localTime variable ≡ stateAt right localTime variable
open CoordinatePicardLindelofAuthority public

record PhysicalTrajectory
    {timeLevel stateLevel : Level}
    (Time : Set timeLevel)
    (PhysicalState : Set stateLevel) :
    Set (lsuc (timeLevel ⊔ stateLevel)) where
  field
    stateAt : Time → PhysicalState
    derivativeCoordinatesAt : Time → Polynomial.Assignment
open PhysicalTrajectory public

transportCoordinateTrajectory :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {PhysicalState : Set stateLevel} →
  Coordinates.FinitePhysicalCoordinateEquivalence PhysicalState →
  CoordinateTrajectory Time →
  PhysicalTrajectory Time PhysicalState
transportCoordinateTrajectory equivalence trajectory = record
  { PhysicalTrajectory.stateAt = λ time →
      Coordinates.decode equivalence
        (CoordinateTrajectory.stateAt trajectory time)
  ; PhysicalTrajectory.derivativeCoordinatesAt =
      CoordinateTrajectory.derivativeAt trajectory
  }

coordinateVectorFieldFromPhysical :
  ∀ {stateLevel}
    {PhysicalState : Set stateLevel} →
  Coordinates.FinitePhysicalCoordinateEquivalence PhysicalState →
  (PhysicalState → PhysicalState) →
  Polynomial.Assignment → Polynomial.Assignment
coordinateVectorFieldFromPhysical equivalence physicalVectorField coordinates =
  Coordinates.encode equivalence
    (physicalVectorField (Coordinates.decode equivalence coordinates))

record PhysicalCoordinateODESolution
    {timeLevel stateLevel}
    {Time : Set timeLevel}
    {PhysicalState : Set stateLevel}
    (equivalence : Coordinates.FinitePhysicalCoordinateEquivalence PhysicalState)
    (physicalVectorField : PhysicalState → PhysicalState)
    (trajectory : PhysicalTrajectory Time PhysicalState) :
    Set (timeLevel ⊔ stateLevel) where
  field
    derivativeEquation : ∀ time variable →
      derivativeCoordinatesAt trajectory time variable
      ≡ Coordinates.encode equivalence
          (physicalVectorField (PhysicalTrajectory.stateAt trajectory time))
          variable
open PhysicalCoordinateODESolution public

transportedTrajectorySolvesPhysicalODE :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {PhysicalState : Set stateLevel}
    (equivalence : Coordinates.FinitePhysicalCoordinateEquivalence PhysicalState)
    (physicalVectorField : PhysicalState → PhysicalState)
    (trajectory : CoordinateTrajectory Time) →
  CoordinateODESolution
    (coordinateVectorFieldFromPhysical equivalence physicalVectorField)
    trajectory →
  PhysicalCoordinateODESolution equivalence physicalVectorField
    (transportCoordinateTrajectory equivalence trajectory)
transportedTrajectorySolvesPhysicalODE
    equivalence physicalVectorField trajectory solution = record
  { PhysicalCoordinateODESolution.derivativeEquation =
      CoordinateODESolution.derivativeEquation solution
  }

physicalLocalTrajectory :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {PhysicalState : Set stateLevel}
    (authority : CoordinatePicardLindelofAuthority Time)
    (equivalence : Coordinates.FinitePhysicalCoordinateEquivalence PhysicalState)
    (physicalVectorField : PhysicalState → PhysicalState) →
  LocallyLipschitz authority
    (coordinateVectorFieldFromPhysical equivalence physicalVectorField) →
  PhysicalState → PhysicalTrajectory Time PhysicalState
physicalLocalTrajectory authority equivalence physicalVectorField lipschitz initial =
  transportCoordinateTrajectory equivalence
    (localTrajectory authority
      (coordinateVectorFieldFromPhysical equivalence physicalVectorField)
      lipschitz (Coordinates.encode equivalence initial))

physicalLocalTrajectorySolves :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {PhysicalState : Set stateLevel}
    (authority : CoordinatePicardLindelofAuthority Time)
    (equivalence : Coordinates.FinitePhysicalCoordinateEquivalence PhysicalState)
    (physicalVectorField : PhysicalState → PhysicalState)
    (lipschitz : LocallyLipschitz authority
      (coordinateVectorFieldFromPhysical equivalence physicalVectorField))
    (initial : PhysicalState) →
  PhysicalCoordinateODESolution equivalence physicalVectorField
    (physicalLocalTrajectory authority equivalence physicalVectorField
      lipschitz initial)
physicalLocalTrajectorySolves authority equivalence physicalVectorField
    lipschitz initial =
  transportedTrajectorySolvesPhysicalODE
    equivalence physicalVectorField
    (localTrajectory authority
      (coordinateVectorFieldFromPhysical equivalence physicalVectorField)
      lipschitz (Coordinates.encode equivalence initial))
    (localTrajectorySolves authority
      (coordinateVectorFieldFromPhysical equivalence physicalVectorField)
      lipschitz (Coordinates.encode equivalence initial))

physicalLocalTrajectoryInitial :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {PhysicalState : Set stateLevel}
    (authority : CoordinatePicardLindelofAuthority Time)
    (equivalence : Coordinates.FinitePhysicalCoordinateEquivalence PhysicalState)
    (physicalVectorField : PhysicalState → PhysicalState)
    (lipschitz : LocallyLipschitz authority
      (coordinateVectorFieldFromPhysical equivalence physicalVectorField))
    (initial : PhysicalState)
    (time : InitialTime authority) →
  PhysicalTrajectory.stateAt
    (physicalLocalTrajectory authority equivalence physicalVectorField
      lipschitz initial)
    (initialTimeValue authority time)
  ≡ initial
physicalLocalTrajectoryInitial
    authority equivalence physicalVectorField lipschitz initial time =
  trans
    (cong (Coordinates.decode equivalence)
      (localTrajectoryInitial authority
        (coordinateVectorFieldFromPhysical equivalence physicalVectorField)
        lipschitz (Coordinates.encode equivalence initial) time))
    (Coordinates.decodeEncode equivalence initial)

physicalLocalTrajectoryUniqueCoordinatewise :
  ∀ {timeLevel stateLevel}
    {Time : Set timeLevel}
    {PhysicalState : Set stateLevel}
    (authority : CoordinatePicardLindelofAuthority Time)
    (equivalence : Coordinates.FinitePhysicalCoordinateEquivalence PhysicalState)
    (physicalVectorField : PhysicalState → PhysicalState)
    (lipschitz : LocallyLipschitz authority
      (coordinateVectorFieldFromPhysical equivalence physicalVectorField))
    (initial : PhysicalState)
    (left right : CoordinateTrajectory Time) →
  CoordinateODESolution
    (coordinateVectorFieldFromPhysical equivalence physicalVectorField) left →
  CoordinateODESolution
    (coordinateVectorFieldFromPhysical equivalence physicalVectorField) right →
  (time : InitialTime authority) →
  CoordinateTrajectory.stateAt left (initialTimeValue authority time)
    ≡ Coordinates.encode equivalence initial →
  CoordinateTrajectory.stateAt right (initialTimeValue authority time)
    ≡ Coordinates.encode equivalence initial →
  ∀ localTime variable →
  Coordinates.encode equivalence
    (PhysicalTrajectory.stateAt
      (transportCoordinateTrajectory equivalence left) localTime) variable
  ≡ Coordinates.encode equivalence
      (PhysicalTrajectory.stateAt
        (transportCoordinateTrajectory equivalence right) localTime) variable
physicalLocalTrajectoryUniqueCoordinatewise
    authority equivalence physicalVectorField lipschitz initial
    left right leftSolves rightSolves time leftInitial rightInitial
    localTime variable =
  trans
    (Coordinates.encodeDecode equivalence
      (CoordinateTrajectory.stateAt left localTime) variable)
    (trans
      (localUniqueness authority
        (coordinateVectorFieldFromPhysical equivalence physicalVectorField)
        lipschitz (Coordinates.encode equivalence initial)
        left right leftSolves rightSolves time leftInitial rightInitial
        localTime variable)
      (sym
        (Coordinates.encodeDecode equivalence
          (CoordinateTrajectory.stateAt right localTime) variable)))

picardLindelofTransportClosed : Bool
picardLindelofTransportClosed = true

repositoryRealPicardLindelofAuthoritySupplied : Bool
repositoryRealPicardLindelofAuthoritySupplied = false

picardLindelofTransportClosedIsTrue :
  picardLindelofTransportClosed ≡ true
picardLindelofTransportClosedIsTrue = refl

repositoryRealPicardLindelofAuthoritySuppliedIsFalse :
  repositoryRealPicardLindelofAuthoritySupplied ≡ false
repositoryRealPicardLindelofAuthoritySuppliedIsFalse = refl
