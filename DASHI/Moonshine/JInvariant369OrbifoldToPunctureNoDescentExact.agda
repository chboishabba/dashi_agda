module DASHI.Moonshine.JInvariant369OrbifoldToPunctureNoDescentExact where

-- Genuine no-descent theorem, reusing literal pre-existing Moonshine
-- Z/2 twisted-sector labels and literal punctured SSP/Monster T9 carrier.
-- The recorded B3 pure braid is identity in the coarse Z/2 module,
-- but fixed-point-free on the nonzero F3^2 fibre. Therefore NO
-- equivariant map from ALL coarse sectors to fine punctured states exists.
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Empty using (⊥)

import DASHI.Biology.MoonshineOrbifoldModularSectorActionExact as Orb
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Puncture
import DASHI.Moonshine.JInvariant369BraidOrbifoldSectorKernelExact as Coarse
import DASHI.Moonshine.JInvariant369PuncturedSheetModularBraidActionExact as Fine

record CoarseSectorToFinePuncture : Set where
  field
    decode : Orb.OrbifoldSector → Puncture.PuncturedNineSheet
    respectsRecordedPureBraid :
      (s : Orb.OrbifoldSector) →
      decode (Coarse.recordedPureBraidSectorAction s)
      ≡ Fine.modularMatrixOnPunctured (decode s)
open CoarseSectorToFinePuncture public

coarseDecodingForcesFixedFinePoint :
  (D : CoarseSectorToFinePuncture) →
  (s : Orb.OrbifoldSector) →
  Fine.modularMatrixOnPunctured (decode D s) ≡ decode D s
coarseDecodingForcesFixedFinePoint D s =
  trans
    (sym (respectsRecordedPureBraid D s))
    (cong (decode D)
      (Coarse.recordedPureBraidInvisibleToOrbifoldSector s))

noEquivariantCoarseToFinePuncture :
  CoarseSectorToFinePuncture → ⊥
noEquivariantCoarseToFinePuncture D =
  Fine.modularHasNoFixedPuncturedPoint
    (decode D Orb.vacuumSector)
    (coarseDecodingForcesFixedFinePoint D Orb.vacuumSector)

-- Narrow statement: no equivariant decoder from the four *labels*
-- into the nonzero eight-point fibre. It does not prohibit a larger
-- VOA Hilbert space, modular cover or explicit extension of the domain.
-- It is an exact instance of the existing
-- JInvariant369LevelNonDescentThroughJExact information-loss programme.
