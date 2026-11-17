module DASHI.Mathematics.Topology.AlexanderHornedC3ChronologicalClopenBridgeExact where

------------------------------------------------------------------------
-- THIN EXISTING-OWNER WELD: chronological Cantor cylinder from the
-- literal newest-first Hatcher/Horn address.
--
-- Reuses canonical owners, not a second Cantor measure library:
-- * AlexanderHornedC3FiniteStageExact: HornAddress, children, C3;
-- * AlexanderHornedBinaryPadicCylinderExact: chronological reversal;
-- * AlexanderHornedC3ClopenCylinderMassExact: bit-to-Bool conversion;
-- * CantorProjectiveCylinderMeasureExact: actual Cylinder constructor.
--
-- PARENT-CHILD DIRECTION IS REAL: the new geometric/stream child
-- appends a digit. The existing Cantor.leftChild PREPENDS and thus
-- its dyadic mass law alone does not establish chronological event
-- inclusion. The general same-stream counterexample and append
-- event refinement are owned by stacked PR #1254, not copied here.
--
-- NO wild R3 embedding, annular collar, pi1 or kernel receipt follows.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (_++_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Horn
import DASHI.Mathematics.Topology.AlexanderHornedBinaryPadicCylinderExact as Bin
import DASHI.Mathematics.Topology.AlexanderHornedC3ClopenCylinderMassExact as EndMass
import DASHI.Foundations.CantorProjectiveCylinderMeasureExact as Cantor

chronologicalCylinder : Horn.HornAddress → Cantor.Cylinder
chronologicalCylinder (Horn.address c reverseSuffix) =
  Cantor.cylinder
    (EndMass.prefixBitsToBools (Bin.chronological reverseSuffix))

-- The single-digit append conversion is proved on the original
-- source implementation's recursive word-to-Bool function.
booleansAppendOne : (xs : List Horn.Bit) (b : Horn.Bit) →
  EndMass.prefixBitsToBools (xs ++ (b ∷ [])) ≡
  EndMass.prefixBitsToBools xs ++ (EndMass.bitToBool b ∷ [])
booleansAppendOne [] b = refl
booleansAppendOne (x ∷ xs) b =
  cong (EndMass.bitToBool x ∷_) (booleansAppendOne xs b)

leftChildAppendsChronologicalBit :
  (c : Horn.HornAddress) →
  Cantor.prefix (chronologicalCylinder (Horn.leftChild c)) ≡
    Cantor.prefix (chronologicalCylinder c) ++ (false ∷ [])
leftChildAppendsChronologicalBit (Horn.address sector reverseSuffix) =
  booleansAppendOne (Bin.chronological reverseSuffix) Horn.left

rightChildAppendsChronologicalBit :
  (c : Horn.HornAddress) →
  Cantor.prefix (chronologicalCylinder (Horn.rightChild c)) ≡
    Cantor.prefix (chronologicalCylinder c) ++ (true ∷ [])
rightChildAppendsChronologicalBit (Horn.address sector reverseSuffix) =
  booleansAppendOne (Bin.chronological reverseSuffix) Horn.right

-- C3 permutes external sectors. It never rewrites a bit stream.
rotationPreservesChronologicalCylinder : (c : Horn.HornAddress) →
  chronologicalCylinder (Horn.rotateAddress c) ≡ chronologicalCylinder c
rotationPreservesChronologicalCylinder (Horn.address sector reverseSuffix) = refl

-- Scope: a genuine orientation-preserving symbolic commuting square;
-- no claim that any of these cylinders is clopen in the CONNECTED
-- ambient exterior, or that it captures linking in Hatcher X_n.
