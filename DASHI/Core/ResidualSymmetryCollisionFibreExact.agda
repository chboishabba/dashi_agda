module DASHI.Core.ResidualSymmetryCollisionFibreExact where

------------------------------------------------------------------------
-- RESIDUAL SYMMETRY ON COLLISION / MULTIPLICITY FIBRES
--
-- Top-down rule:
--
--   observe -> locate collision fibre -> inspect symmetry acting inside it.
--
-- If an invertible symmetry preserves an observer, it acts internally on every
-- observation fibre.  A residual sector label may then strictly refine the
-- coarse observer without changing its public value.  This is the set-level
-- theorem shape instantiated more richly by deck/character decompositions in
-- the marked-Hecke lane.
--
-- SOURCE / METHOD CALIBRATION
--
-- Jean-Pierre Serre, "Linear Representations of Finite Groups",
-- Graduate Texts in Mathematics 42, Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Double-centralizer / commutant theory motivates the representation-level
-- version, but this generic core deliberately proves only what its hypotheses
-- support.  Equality A''=A and a full tensor decomposition require additional
-- semisimplicity/representation hypotheses and are NOT asserted here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer

record InvertibleSymmetryAction (State Symmetry : Set) : Set₁ where
  constructor invertibleSymmetryAction
  field
    identity : Symmetry
    combine : Symmetry → Symmetry → Symmetry
    inverse : Symmetry → Symmetry
    act : Symmetry → State → State

    identityActs : (x : State) → act identity x ≡ x
    combineActs :
      (g h : Symmetry) (x : State) →
      act (combine g h) x ≡ act g (act h x)
    inverseLeftActs :
      (g : Symmetry) (x : State) →
      act (inverse g) (act g x) ≡ x
    inverseRightActs :
      (g : Symmetry) (x : State) →
      act g (act (inverse g) x) ≡ x

open InvertibleSymmetryAction public

record ObserverPreservingSymmetry
    {State Symmetry Observation : Set}
    (action : InvertibleSymmetryAction State Symmetry)
    (observe : State → Observation) : Set₁ where
  constructor observerPreservingSymmetry
  field
    observationInvariant :
      (g : Symmetry) (x : State) →
      observe (act action g x) ≡ observe x

open ObserverPreservingSymmetry public

CollisionFibre :
  ∀ {State Observation : Set} →
  (State → Observation) → Observation → Set
CollisionFibre = Observer.ObservationFibre

actOnCollisionFibre :
  ∀ {State Symmetry Observation : Set}
    {action : InvertibleSymmetryAction State Symmetry}
    {observe : State → Observation} →
  ObserverPreservingSymmetry action observe →
  (g : Symmetry) →
  (value : Observation) →
  CollisionFibre observe value →
  CollisionFibre observe value
actOnCollisionFibre {action = action} preserving g value (x , sameValue) =
  act action g x ,
  trans (observationInvariant preserving g x) sameValue

fibreActionStaysInSamePublicValue :
  ∀ {State Symmetry Observation : Set}
    {action : InvertibleSymmetryAction State Symmetry}
    {observe : State → Observation}
    (preserving : ObserverPreservingSymmetry action observe)
    (g : Symmetry)
    (value : Observation)
    (point : CollisionFibre observe value) →
  observe (proj₁ (actOnCollisionFibre preserving g value point)) ≡ value
fibreActionStaysInSamePublicValue preserving g value point =
  proj₂ (actOnCollisionFibre preserving g value point)

fibreActionIdentityOnCarrier :
  ∀ {State Symmetry Observation : Set}
    {action : InvertibleSymmetryAction State Symmetry}
    {observe : State → Observation}
    (preserving : ObserverPreservingSymmetry action observe)
    (value : Observation)
    (point : CollisionFibre observe value) →
  proj₁
    (actOnCollisionFibre preserving (identity action) value point)
  ≡ proj₁ point
fibreActionIdentityOnCarrier {action = action} preserving value point =
  identityActs action (proj₁ point)

fibreActionCompositionOnCarrier :
  ∀ {State Symmetry Observation : Set}
    {action : InvertibleSymmetryAction State Symmetry}
    {observe : State → Observation}
    (preserving : ObserverPreservingSymmetry action observe)
    (g h : Symmetry)
    (value : Observation)
    (point : CollisionFibre observe value) →
  proj₁
    (actOnCollisionFibre preserving (combine action g h) value point)
  ≡ proj₁
      (actOnCollisionFibre preserving g value
        (actOnCollisionFibre preserving h value point))
fibreActionCompositionOnCarrier {action = action} preserving g h value point =
  combineActs action g h (proj₁ point)

------------------------------------------------------------------------
-- Residual sector labels refine a coarse collision fibre.
------------------------------------------------------------------------

record ResidualSectorWitness
    {State Observation Sector : Set}
    (observe : State → Observation)
    (sector : State → Sector) : Set where
  constructor residualSectorWitness
  field
    left right : State
    sameCoarseObservation : observe left ≡ observe right
    differentSector : sector left ≡ sector right → ⊥

open ResidualSectorWitness public

sectorPairStrictlyRefinesCoarse :
  ∀ {State Observation Sector : Set}
    (observe : State → Observation)
    (sector : State → Sector) →
  ResidualSectorWitness observe sector →
  Observer.StrictRefinement observe (Observer.pairObserver observe sector)
sectorPairStrictlyRefinesCoarse observe sector witness =
  Observer.strictPairRefinement
    observe sector
    (left witness)
    (right witness)
    (sameCoarseObservation witness)
    (differentSector witness)

------------------------------------------------------------------------
-- Commutant-shaped obligation.
--
-- Merely saying a symmetry commutes with an operator family does not by itself
-- construct a spectral label in this untyped set-level core.  Linear instances
-- must additionally prove that their declared joint spectral observer is
-- preserved.  This keeps the double-centralizer hypothesis boundary explicit.
------------------------------------------------------------------------

Endomorphism : Set → Set
Endomorphism State = State → State

CommutingWithFamily :
  ∀ {State Symmetry Index : Set} →
  InvertibleSymmetryAction State Symmetry →
  (Index → Endomorphism State) → Set
CommutingWithFamily action operators =
  ∀ g index x →
  operators index (act action g x)
  ≡ act action g (operators index x)

record ResidualSymmetryCollisionFibreBoundary : Set where
  constructor residualSymmetryCollisionFibreBoundary
  field
    observerPreservingSymmetryActsInsideEveryFibre : Bool
    residualSectorCanStrictlyRefineCollision : Bool
    commutingOperatorFamilyAutomaticallyBuildsSpectralLabels : Bool
    doubleCentralizerEqualityProvedWithoutSemisimplicity : Bool
    sectorSeparationMeansWorldCompleteness : Bool

canonicalResidualSymmetryCollisionFibreBoundary :
  ResidualSymmetryCollisionFibreBoundary
canonicalResidualSymmetryCollisionFibreBoundary =
  residualSymmetryCollisionFibreBoundary true true false false false
