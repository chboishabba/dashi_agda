module DASHI.ComputerScience.TekumSourceAnchorCenterExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base as ℤ using (+_)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT

------------------------------------------------------------------------
-- HUNHOLD DEFINITION 7: THE ANCHOR MIDPOINT WORD
--
-- The paper subtracts the alternating balanced-ternary code
--
--     1T ... 1T
--
-- at even source widths.  Repository Vec words are least-significant-trit
-- first, so the same word is stored
--
--     T 1 T 1 ... .
--
-- Earlier Tekum source code accidentally used 11...1 here, i.e. the maximum
-- positive balanced integer.  This owner keeps the actual source word explicit
-- so the arithmetic backend cannot silently conflate the two constants again.
------------------------------------------------------------------------

sourceAnchorCenterWord : (n : Nat) → Vec Trit.Trit n
sourceAnchorCenterWord zero = []
sourceAnchorCenterWord (suc zero) = Trit.neg ∷ []
sourceAnchorCenterWord (suc (suc n)) =
  Trit.neg ∷ Trit.pos ∷ sourceAnchorCenterWord n

sourceAnchorCenterWidth2 :
  sourceAnchorCenterWord 2
  ≡ Trit.neg ∷ Trit.pos ∷ []
sourceAnchorCenterWidth2 = refl

sourceAnchorCenterWidth4 :
  sourceAnchorCenterWord 4
  ≡ Trit.neg ∷ Trit.pos ∷ Trit.neg ∷ Trit.pos ∷ []
sourceAnchorCenterWidth4 = refl

sourceAnchorCenterInteger2 :
  BT.toInteger (BT.eval (sourceAnchorCenterWord 2)) ≡ + 2
sourceAnchorCenterInteger2 = refl

sourceAnchorCenterInteger4 :
  BT.toInteger (BT.eval (sourceAnchorCenterWord 4)) ≡ + 20
sourceAnchorCenterInteger4 = refl
