module DASHI.Physics.YangMills.CompactSimpleClassification where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Cartan--Killing classification tags.  Classical-family constructors encode
-- the minimum simple rank in their index, so invalid low-rank aliases cannot be
-- formed through this surface.
------------------------------------------------------------------------

data SimpleLieType : Set where
  A : Nat → SimpleLieType       -- A_(n+1), n >= 0
  B : Nat → SimpleLieType       -- B_(n+2), n >= 0
  C : Nat → SimpleLieType       -- C_(n+2), n >= 0
  D : Nat → SimpleLieType       -- D_(n+4), n >= 0
  E6 E7 E8 F4 G2 : SimpleLieType

rank : SimpleLieType → Nat
rank (A n) = suc n
rank (B n) = suc (suc n)
rank (C n) = suc (suc n)
rank (D n) = suc (suc (suc (suc n)))
rank E6 = 6
rank E7 = 7
rank E8 = 8
rank F4 = 4
rank G2 = 2

-- Subtraction-free forms of the standard dimension formulas.
dimension : SimpleLieType → Nat
dimension (A n) = (n + 1) * (n + 3)
dimension (B n) = (n + 2) * (2 * n + 5)
dimension (C n) = (n + 2) * (2 * n + 5)
dimension (D n) = (n + 4) * (2 * n + 7)
dimension E6 = 78
dimension E7 = 133
dimension E8 = 248
dimension F4 = 52
dimension G2 = 14

-- Dual Coxeter numbers in the same predecessor-coded convention.
dualCoxeter : SimpleLieType → Nat
dualCoxeter (A n) = n + 2
dualCoxeter (B n) = 2 * n + 3
dualCoxeter (C n) = n + 3
dualCoxeter (D n) = 2 * n + 6
dualCoxeter E6 = 12
dualCoxeter E7 = 18
dualCoxeter E8 = 30
dualCoxeter F4 = 9
dualCoxeter G2 = 4

-- Canonical A1/SU(2) invariants are fully computational.
su2Type : SimpleLieType
su2Type = A zero

su2Rank : rank su2Type ≡ 1
su2Rank = refl

su2Dimension : dimension su2Type ≡ 3
su2Dimension = refl

su2DualCoxeter : dualCoxeter su2Type ≡ 2
su2DualCoxeter = refl

classificationFormulaLevel : ProofLevel
classificationFormulaLevel = machineChecked

classificationCompletenessLevel : ProofLevel
classificationCompletenessLevel = standardImported
