module DASHI.Physics.Plasma.HelicityElsasserBinaryAxesExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- TWO DISTINCT BINARY AXES IN HELICAL MHD
--
-- Helicity sign s = +/- labels curl eigenmodes.
-- Elsasser orientation alpha = +/- labels z^+ / z^- propagation variables.
-- They are independent coordinates and must not be collapsed into one bit.
------------------------------------------------------------------------

data HelicitySign : Set where
  helicityPlus helicityMinus : HelicitySign

data ElsasserOrientation : Set where
  elsasserPlus elsasserMinus : ElsasserOrientation

record HelicalElsasserSector : Set where
  constructor helical-elsasser-sector
  field
    helicity : HelicitySign
    elsasser : ElsasserOrientation

open HelicalElsasserSector public

sectorPP sectorPM sectorMP sectorMM : HelicalElsasserSector
sectorPP = helical-elsasser-sector helicityPlus elsasserPlus
sectorPM = helical-elsasser-sector helicityPlus elsasserMinus
sectorMP = helical-elsasser-sector helicityMinus elsasserPlus
sectorMM = helical-elsasser-sector helicityMinus elsasserMinus

record BinaryAxesBoundary : Set where
  constructor binary-axes-boundary
  field
    helicitySignDeterminesElsasserOrientation : Bool
    helicitySignDeterminesElsasserOrientationIsFalse :
      helicitySignDeterminesElsasserOrientation ≡ false

    elsasserOrientationDeterminesHelicitySign : Bool
    elsasserOrientationDeterminesHelicitySignIsFalse :
      elsasserOrientationDeterminesHelicitySign ≡ false

    fourCombinedSectorsRequired : Bool
    fourCombinedSectorsRequiredIsTrue :
      fourCombinedSectorsRequired ≡ true

canonicalBinaryAxesBoundary : BinaryAxesBoundary
canonicalBinaryAxesBoundary =
  binary-axes-boundary false refl false refl true refl
