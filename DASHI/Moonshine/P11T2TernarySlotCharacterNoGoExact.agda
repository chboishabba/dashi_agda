module DASHI.Moonshine.P11T2TernarySlotCharacterNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Trees", Springer Monographs in Mathematics.
-- DOI: 10.1007/978-3-642-61856-7.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Cross-pollinate the Phase3/C3 character weld with the actual positive p=11
-- ell=2 neighbour system.  The local slot set Fin 3 is exactly a Phase3/C3
-- carrier and therefore has the expected cubic character table.  But the
-- obvious fixed-source C3 slot rotation is NOT a symmetry of the actual T2
-- geometry: on a B-sheet row, rotating the second slot into the third changes
-- the coarse target from j=0 to j=1728.
--
-- Hence the equality ell+1=3 supplies local harmonic coordinates but not an
-- automatic Bruhat--Tits/S3 action on the p=11 quotient.  Any genuine tree
-- action must move additional source/frame data, not merely relabel the three
-- outgoing slots at a fixed vertex.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)

import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.Phase3RootCharacterWeldExact as Root3
import DASHI.Moonshine.PrimeRegularHeckeLocalGeometryExact as Local
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo

------------------------------------------------------------------------
-- The actual p=11 T2 system is a prime-regular ell=2 local geometry.
------------------------------------------------------------------------

p11T2LocalGeometry : Local.PrimeRegularHeckeLocalGeometry Fine.P11Fine5 2
p11T2LocalGeometry = record
  { Local.neighbour = Fine.r2Neighbour
  }

p11T2LocalArityIsThree : Local.localArity p11T2LocalGeometry ≡ 3
p11T2LocalArityIsThree = refl

------------------------------------------------------------------------
-- Exact Fin3 <-> Phase3 chart and cubic character coordinates.
------------------------------------------------------------------------

slotToPhase : Fin 3 → Phase.Phase3
slotToPhase zero = Phase.phase0
slotToPhase (suc zero) = Phase.phase1
slotToPhase (suc (suc zero)) = Phase.phase2

phaseToSlot : Phase.Phase3 → Fin 3
phaseToSlot Phase.phase0 = zero
phaseToSlot Phase.phase1 = suc zero
phaseToSlot Phase.phase2 = suc (suc zero)

slotPhaseRoundTrip : (slot : Fin 3) → phaseToSlot (slotToPhase slot) ≡ slot
slotPhaseRoundTrip zero = refl
slotPhaseRoundTrip (suc zero) = refl
slotPhaseRoundTrip (suc (suc zero)) = refl

phaseSlotRoundTrip : (phase : Phase.Phase3) → slotToPhase (phaseToSlot phase) ≡ phase
phaseSlotRoundTrip Phase.phase0 = refl
phaseSlotRoundTrip Phase.phase1 = refl
phaseSlotRoundTrip Phase.phase2 = refl

rotateSlot : Fin 3 → Fin 3
rotateSlot zero = suc zero
rotateSlot (suc zero) = suc (suc zero)
rotateSlot (suc (suc zero)) = zero

slotRotationMatchesZeta :
  (slot : Fin 3) →
  slotToPhase (rotateSlot slot) ≡ Root3.zetaRotate (slotToPhase slot)
slotRotationMatchesZeta zero = refl
slotRotationMatchesZeta (suc zero) = refl
slotRotationMatchesZeta (suc (suc zero)) = refl

slotCharacter : Phase.Phase3 → Fin 3 → Phase.Phase3
slotCharacter k slot = Root3.character k (slotToPhase slot)

slotCharacterDiagonalizesRotation :
  (k : Phase.Phase3) → (slot : Fin 3) →
  slotCharacter k (rotateSlot slot)
  ≡ Root3.phaseMul k (slotCharacter k slot)
slotCharacterDiagonalizesRotation Phase.phase0 zero = refl
slotCharacterDiagonalizesRotation Phase.phase0 (suc zero) = refl
slotCharacterDiagonalizesRotation Phase.phase0 (suc (suc zero)) = refl
slotCharacterDiagonalizesRotation Phase.phase1 zero = refl
slotCharacterDiagonalizesRotation Phase.phase1 (suc zero) = refl
slotCharacterDiagonalizesRotation Phase.phase1 (suc (suc zero)) = refl
slotCharacterDiagonalizesRotation Phase.phase2 zero = refl
slotCharacterDiagonalizesRotation Phase.phase2 (suc zero) = refl
slotCharacterDiagonalizesRotation Phase.phase2 (suc (suc zero)) = refl

------------------------------------------------------------------------
-- Falsifier: local slot rotation is not fixed-source Brandt-target symmetry.
------------------------------------------------------------------------

b0SecondSlotCoarseTarget :
  Fine.projectFine5 (Fine.r2Neighbour Fine.b0 (suc zero)) ≡ Geo.jZeroSS
b0SecondSlotCoarseTarget = refl

b0RotatedSecondSlotCoarseTarget :
  Fine.projectFine5 (Fine.r2Neighbour Fine.b0 (rotateSlot (suc zero)))
  ≡ Geo.j1728SS
b0RotatedSecondSlotCoarseTarget = refl

fixedSourceSlotRotationCannotPreserveCoarseTargets :
  ((slot : Fin 3) →
    Fine.projectFine5 (Fine.r2Neighbour Fine.b0 (rotateSlot slot))
    ≡ Fine.projectFine5 (Fine.r2Neighbour Fine.b0 slot)) →
  ⊥
fixedSourceSlotRotationCannotPreserveCoarseTargets preserves =
  Geo.jZeroNotJ1728 (sym (preserves (suc zero)))

record P11T2TernarySlotBoundary : Set where
  field
    actualT2HasTernaryLocalValency : Bool
    actualT2HasTernaryLocalValencyIsTrue :
      actualT2HasTernaryLocalValency ≡ true

    exactC3CharacterCoordinatesOnSlots : Bool
    exactC3CharacterCoordinatesOnSlotsIsTrue :
      exactC3CharacterCoordinatesOnSlots ≡ true

    naiveFixedSourceC3RotationIsGraphSymmetry : Bool
    naiveFixedSourceC3RotationIsGraphSymmetryIsFalse :
      naiveFixedSourceC3RotationIsGraphSymmetry ≡ false

    ternaryTreePromotedToBruhatTitsAction : Bool
    ternaryTreePromotedToBruhatTitsActionIsFalse :
      ternaryTreePromotedToBruhatTitsAction ≡ false

canonicalP11T2TernarySlotBoundary : P11T2TernarySlotBoundary
canonicalP11T2TernarySlotBoundary = record
  { actualT2HasTernaryLocalValency = true
  ; actualT2HasTernaryLocalValencyIsTrue = refl
  ; exactC3CharacterCoordinatesOnSlots = true
  ; exactC3CharacterCoordinatesOnSlotsIsTrue = refl
  ; naiveFixedSourceC3RotationIsGraphSymmetry = false
  ; naiveFixedSourceC3RotationIsGraphSymmetryIsFalse = refl
  ; ternaryTreePromotedToBruhatTitsAction = false
  ; ternaryTreePromotedToBruhatTitsActionIsFalse = refl
  }
