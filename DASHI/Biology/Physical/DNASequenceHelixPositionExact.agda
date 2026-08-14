module DASHI.Biology.Physical.DNASequenceHelixPositionExact where

------------------------------------------------------------------------
-- DNA-specific position -> phase -> helix-site bridge.
--
-- The finite phase period is an exact algebraic regression only; it is not a
-- claim that real B-DNA has four bases per turn.  Physical pitch/twist require
-- calibrated structural parameters.  The theorem here is the reusable
-- position/phase commutation surface requested by the attachment.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.DNAChemistryCarrier as DNA
import DASHI.Biology.Physical.DNAHelixDihedralExact as Helix

data Position4 : Set where
  n0 n1 n2 n3 : Position4

nextPosition : Position4 → Position4
nextPosition n0 = n1
nextPosition n1 = n2
nextPosition n2 = n3
nextPosition n3 = n0

phaseAt : Position4 → Helix.Phase4
phaseAt n0 = Helix.p0
phaseAt n1 = Helix.p1
phaseAt n2 = Helix.p2
phaseAt n3 = Helix.p3

positionAdvanceCommutesWithPhaseRotation :
  (n : Position4) → phaseAt (nextPosition n) ≡ Helix.rotate (phaseAt n)
positionAdvanceCommutesWithPhaseRotation n0 = refl
positionAdvanceCommutesWithPhaseRotation n1 = refl
positionAdvanceCommutesWithPhaseRotation n2 = refl
positionAdvanceCommutesWithPhaseRotation n3 = refl

record PositionedBase : Set where
  constructor positionedBase
  field
    base : DNA.DNABase
    cyclicPosition : Position4
    axialHistory : Nat

open PositionedBase public

embedPrimary : PositionedBase → Helix.HelixSite
embedPrimary (positionedBase b n z) =
  Helix.helixSite b (phaseAt n) z Helix.primary

advancePositioned : PositionedBase → PositionedBase
advancePositioned (positionedBase b n z) =
  positionedBase b (nextPosition n) (suc z)

embeddingCommutesWithAdvance :
  (x : PositionedBase) →
  embedPrimary (advancePositioned x) ≡ Helix.advance (embedPrimary x)
embeddingCommutesWithAdvance (positionedBase b n0 z) = refl
embeddingCommutesWithAdvance (positionedBase b n1 z) = refl
embeddingCommutesWithAdvance (positionedBase b n2 z) = refl
embeddingCommutesWithAdvance (positionedBase b n3 z) = refl

pairedPositionedSite : PositionedBase → Helix.HelixSite
pairedPositionedSite x = Helix.pairedSite (embedPrimary x)

pairedBaseIsWatsonCrickComplement :
  (x : PositionedBase) →
  Helix.base (pairedPositionedSite x) ≡ DNA.complement (base x)
pairedBaseIsWatsonCrickComplement (positionedBase b n z) = refl

pairedPhaseIsHalfTurnOffset :
  (x : PositionedBase) →
  Helix.phase (pairedPositionedSite x) ≡ Helix.halfTurn (phaseAt (cyclicPosition x))
pairedPhaseIsHalfTurnOffset (positionedBase b n z) = refl

-- Axial history is retained separately from cyclic phase, matching the general
-- PNF distinction between quotient phase and reopening/provenance coordinate.
