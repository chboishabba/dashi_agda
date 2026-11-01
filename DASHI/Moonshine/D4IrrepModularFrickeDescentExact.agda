module DASHI.Moonshine.D4IrrepModularFrickeDescentExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7, pp. 1-8.
-- MR 417184; no DOI assigned.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230-239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Weld the exact C2-equivariant D4-sector / finite-Fricke chart to the
-- repository's existing abstract modular-curve Fricke interface.
--
-- No modular point is fabricated.  Instead, this module proves the strongest
-- theorem available without doing so: ANY lift of the ten finite sectors into
-- an actual ModularJFrickeSystem that intertwines finite complement with the
-- analytic Fricke involution descends each D4 irrep species to one
-- Fricke-invariant quotient coordinate.  Positive and negative orientation
-- lifts therefore have the same Hauptmodul coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Biology.D4IrrepFiniteFrickeEquivariantExact as D4Finite
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Finite
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as D4
import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular

record FiniteToModularFrickeLift
  (system : Modular.ModularJFrickeSystem) : Set where
  field
    lift :
      Finite.DecimalCompletionState →
      Modular.FinePoint system
    complementIntertwines :
      (state : Finite.DecimalCompletionState) →
      lift (Finite.complementState state)
      ≡ Modular.fricke system (lift state)

open FiniteToModularFrickeLift public

liftD4Sector :
  (system : Modular.ModularJFrickeSystem) →
  FiniteToModularFrickeLift system →
  D4Finite.D4OrientedSector →
  Modular.FinePoint system
liftD4Sector system bridge sector =
  lift bridge (D4Finite.sectorToCompletedFine sector)

liftD4FlipIsFricke :
  (system : Modular.ModularJFrickeSystem) →
  (bridge : FiniteToModularFrickeLift system) →
  (sector : D4Finite.D4OrientedSector) →
  liftD4Sector system bridge (D4Finite.flipSector sector)
  ≡ Modular.fricke system (liftD4Sector system bridge sector)
liftD4FlipIsFricke system bridge sector =
  trans
    (cong (lift bridge) (D4Finite.sectorComplementEquivariant sector))
    (complementIntertwines bridge
      (D4Finite.sectorToCompletedFine sector))

sourceJOfFlippedSector :
  (system : Modular.ModularJFrickeSystem) →
  (bridge : FiniteToModularFrickeLift system) →
  (sector : D4Finite.D4OrientedSector) →
  Modular.sourceJ system
    (liftD4Sector system bridge (D4Finite.flipSector sector))
  ≡
  Modular.targetJ system
    (liftD4Sector system bridge sector)
sourceJOfFlippedSector system bridge sector =
  trans
    (cong (Modular.sourceJ system)
      (liftD4FlipIsFricke system bridge sector))
    (Modular.sourceJAfterFricke system
      (liftD4Sector system bridge sector))

targetJOfFlippedSector :
  (system : Modular.ModularJFrickeSystem) →
  (bridge : FiniteToModularFrickeLift system) →
  (sector : D4Finite.D4OrientedSector) →
  Modular.targetJ system
    (liftD4Sector system bridge (D4Finite.flipSector sector))
  ≡
  Modular.sourceJ system
    (liftD4Sector system bridge sector)
targetJOfFlippedSector system bridge sector =
  trans
    (cong (Modular.targetJ system)
      (liftD4FlipIsFricke system bridge sector))
    (Modular.targetJAfterFricke system
      (liftD4Sector system bridge sector))

hauptmodulIgnoresD4Orientation :
  (system : Modular.ModularJFrickeSystem) →
  (bridge : FiniteToModularFrickeLift system) →
  (quotient : Modular.GenusZeroQuotientCoordinate system) →
  (sector : D4Finite.D4OrientedSector) →
  Modular.hauptmodul quotient
    (liftD4Sector system bridge (D4Finite.flipSector sector))
  ≡
  Modular.hauptmodul quotient
    (liftD4Sector system bridge sector)
hauptmodulIgnoresD4Orientation system bridge quotient sector =
  trans
    (cong (Modular.hauptmodul quotient)
      (liftD4FlipIsFricke system bridge sector))
    (Modular.hauptmodulFrickeInvariant quotient
      (liftD4Sector system bridge sector))

positiveSector :
  D4.D4IrrepKind → D4Finite.D4OrientedSector
positiveSector kind = kind , D4.positiveOrientation

negativeSector :
  D4.D4IrrepKind → D4Finite.D4OrientedSector
negativeSector kind = kind , D4.negativeOrientation

negativeIsFlipOfPositive :
  (kind : D4.D4IrrepKind) →
  negativeSector kind ≡ D4Finite.flipSector (positiveSector kind)
negativeIsFlipOfPositive D4.A1 = refl
negativeIsFlipOfPositive D4.A2 = refl
negativeIsFlipOfPositive D4.B1 = refl
negativeIsFlipOfPositive D4.B2 = refl
negativeIsFlipOfPositive D4.E2 = refl

irrepSpeciesDescendsToOneHauptmodulCoordinate :
  (system : Modular.ModularJFrickeSystem) →
  (bridge : FiniteToModularFrickeLift system) →
  (quotient : Modular.GenusZeroQuotientCoordinate system) →
  (kind : D4.D4IrrepKind) →
  Modular.hauptmodul quotient
    (liftD4Sector system bridge (negativeSector kind))
  ≡
  Modular.hauptmodul quotient
    (liftD4Sector system bridge (positiveSector kind))
irrepSpeciesDescendsToOneHauptmodulCoordinate
  system bridge quotient kind
  rewrite negativeIsFlipOfPositive kind =
  hauptmodulIgnoresD4Orientation
    system bridge quotient (positiveSector kind)

record D4IrrepModularFrickeBoundary : Set where
  field
    descentFromEquivariantLiftProved : Bool
    descentFromEquivariantLiftProvedIsTrue :
      descentFromEquivariantLiftProved ≡ true
    actualFiniteToModularLiftConstructedHere : Bool
    actualFiniteToModularLiftConstructedHereIsFalse :
      actualFiniteToModularLiftConstructedHere ≡ false
    finiteModeDeclaredLiteralHauptmodulValue : Bool
    finiteModeDeclaredLiteralHauptmodulValueIsFalse :
      finiteModeDeclaredLiteralHauptmodulValue ≡ false

canonicalD4IrrepModularFrickeBoundary :
  D4IrrepModularFrickeBoundary
canonicalD4IrrepModularFrickeBoundary =
  record
    { descentFromEquivariantLiftProved = true
    ; descentFromEquivariantLiftProvedIsTrue = refl
    ; actualFiniteToModularLiftConstructedHere = false
    ; actualFiniteToModularLiftConstructedHereIsFalse = refl
    ; finiteModeDeclaredLiteralHauptmodulValue = false
    ; finiteModeDeclaredLiteralHauptmodulValueIsFalse = refl
    }
