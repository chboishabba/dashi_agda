module DASHI.Physics.Motors.Resonate369CommonRefinementExact where

------------------------------------------------------------------------
-- A common *nominal* phase grid for:
-- - Holmstrom/Resonate369 C07 (8 station claim)
-- - Holmstrom/Resonate369 Dodecatron (12 station claim)
-- - historical Infinity SAV MG10 (250 station claim)
--
-- The 3000-grid embeds all three ideal station lattices exactly.
-- No measured physical offset, winding pitch, phase relation or
-- historical design equivalence is inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

commonSectorCount : Nat
commonSectorCount = 3000

commonSectorMilliDegrees : Nat
commonSectorMilliDegrees = 120

commonGridCloses :
  commonSectorCount * commonSectorMilliDegrees ≡ 360000
commonGridCloses = refl

c07RefinementFactor : Nat
c07RefinementFactor = 375

dodecatronRefinementFactor : Nat
dodecatronRefinementFactor = 250

historicalMG10RefinementFactor : Nat
historicalMG10RefinementFactor = 12

c07RefinementCloses :
  8 * c07RefinementFactor ≡ commonSectorCount
c07RefinementCloses = refl

dodecatronRefinementCloses :
  12 * dodecatronRefinementFactor ≡ commonSectorCount
dodecatronRefinementCloses = refl

historicalMG10RefinementCloses :
  250 * historicalMG10RefinementFactor ≡ commonSectorCount
historicalMG10RefinementCloses = refl

c07PitchMatchesCommonGrid :
  c07RefinementFactor * commonSectorMilliDegrees ≡ 45000
c07PitchMatchesCommonGrid = refl

dodecatronPitchMatchesCommonGrid :
  dodecatronRefinementFactor * commonSectorMilliDegrees ≡ 30000
dodecatronPitchMatchesCommonGrid = refl

historicalMG10PitchMatchesCommonGrid :
  historicalMG10RefinementFactor * commonSectorMilliDegrees ≡ 1440
historicalMG10PitchMatchesCommonGrid = refl

-- Exact integer-sector nominal positions, before quotient by one turn.
c07SectorIndex : Nat → Nat
c07SectorIndex k = k * c07RefinementFactor

dodecatronSectorIndex : Nat → Nat
dodecatronSectorIndex k = k * dodecatronRefinementFactor

historicalMG10SectorIndex : Nat → Nat
historicalMG10SectorIndex k = k * historicalMG10RefinementFactor

-- These are selected anchor positions (zero phase, then first station).
-- Phase-zero alignment is a mathematical convention, not CAD evidence.
c07FirstTwo : c07SectorIndex 0 ≡ 0
c07FirstTwo = refl

c07FirstStation : c07SectorIndex 1 ≡ 375
c07FirstStation = refl

dodecatronFirstStation : dodecatronSectorIndex 1 ≡ 250
dodecatronFirstStation = refl

historicalMG10FirstStation :
  historicalMG10SectorIndex 1 ≡ 12
historicalMG10FirstStation = refl

-- All three nominal embeddings return the full 3000 sector count
-- after their respective claimed number of steps.
c07TurnCloses : c07SectorIndex 8 ≡ commonSectorCount
c07TurnCloses = refl

dodecatronTurnCloses :
  dodecatronSectorIndex 12 ≡ commonSectorCount
dodecatronTurnCloses = refl

historicalMG10TurnCloses :
  historicalMG10SectorIndex 250 ≡ commonSectorCount
historicalMG10TurnCloses = refl
