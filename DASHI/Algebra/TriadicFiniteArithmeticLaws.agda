module DASHI.Algebra.TriadicFiniteArithmeticLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (Trit; neg; zer; pos; []; _∷_)

import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Algebra.TriadicFiniteIrrep as Irrep

------------------------------------------------------------------------
-- Generated finite carry-balance relation.

data CarryBalance : Trit → Trit → Trit → Trit → Set where
  bal-mmmm : CarryBalance neg neg neg neg
  bal-mzmz : CarryBalance neg zer neg zer
  bal-mzzm : CarryBalance neg zer zer neg
  bal-mpmp : CarryBalance neg pos neg pos
  bal-mpzz : CarryBalance neg pos zer zer
  bal-mppm : CarryBalance neg pos pos neg
  bal-zmmz : CarryBalance zer neg neg zer
  bal-zmzm : CarryBalance zer neg zer neg
  bal-zzmp : CarryBalance zer zer neg pos
  bal-zzzz : CarryBalance zer zer zer zer
  bal-zzpm : CarryBalance zer zer pos neg
  bal-zpzp : CarryBalance zer pos zer pos
  bal-zppz : CarryBalance zer pos pos zer
  bal-pmmp : CarryBalance pos neg neg pos
  bal-pmzz : CarryBalance pos neg zer zer
  bal-pmpm : CarryBalance pos neg pos neg
  bal-pzzp : CarryBalance pos zer zer pos
  bal-pzpz : CarryBalance pos zer pos zer
  bal-pppp : CarryBalance pos pos pos pos

------------------------------------------------------------------------
-- Commutativity for every incoming carry and every depth.

commuteWithCarry :
  ∀ {n : Nat} →
  (carry : Trit) →
  (x y : Q.Residue3Pow n) →
  Arithmetic.addWithCarry carry x y
  ≡ Arithmetic.addWithCarry carry y x
commuteWithCarry carry [] [] = refl
commuteWithCarry neg (neg ∷ xs) (neg ∷ ys)
  rewrite commuteWithCarry neg xs ys = refl
commuteWithCarry neg (neg ∷ xs) (zer ∷ ys)
  rewrite commuteWithCarry neg xs ys = refl
commuteWithCarry neg (neg ∷ xs) (pos ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry neg (zer ∷ xs) (neg ∷ ys)
  rewrite commuteWithCarry neg xs ys = refl
commuteWithCarry neg (zer ∷ xs) (zer ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry neg (zer ∷ xs) (pos ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry neg (pos ∷ xs) (neg ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry neg (pos ∷ xs) (zer ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry neg (pos ∷ xs) (pos ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry zer (neg ∷ xs) (neg ∷ ys)
  rewrite commuteWithCarry neg xs ys = refl
commuteWithCarry zer (neg ∷ xs) (zer ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry zer (neg ∷ xs) (pos ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry zer (zer ∷ xs) (neg ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry zer (zer ∷ xs) (zer ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry zer (zer ∷ xs) (pos ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry zer (pos ∷ xs) (neg ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry zer (pos ∷ xs) (zer ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry zer (pos ∷ xs) (pos ∷ ys)
  rewrite commuteWithCarry pos xs ys = refl
commuteWithCarry pos (neg ∷ xs) (neg ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry pos (neg ∷ xs) (zer ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry pos (neg ∷ xs) (pos ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry pos (zer ∷ xs) (neg ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry pos (zer ∷ xs) (zer ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry pos (zer ∷ xs) (pos ∷ ys)
  rewrite commuteWithCarry pos xs ys = refl
commuteWithCarry pos (pos ∷ xs) (neg ∷ ys)
  rewrite commuteWithCarry zer xs ys = refl
commuteWithCarry pos (pos ∷ xs) (zer ∷ ys)
  rewrite commuteWithCarry pos xs ys = refl
commuteWithCarry pos (pos ∷ xs) (pos ∷ ys)
  rewrite commuteWithCarry pos xs ys = refl

------------------------------------------------------------------------
-- General carry-balanced associativity.

associateWithCarries :
  ∀ {n : Nat} {a b c d : Trit} →
  CarryBalance a b c d →
  (x y z : Q.Residue3Pow n) →
  Arithmetic.addWithCarry a (Arithmetic.addWithCarry b x y) z
  ≡ Arithmetic.addWithCarry c x (Arithmetic.addWithCarry d y z)
associateWithCarries balance [] [] [] = refl
associateWithCarries bal-mmmm (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mmmm xs ys zs = refl
associateWithCarries bal-mmmm (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-mmmm (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-mmmm (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-mmmm (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-mmmm (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-mmmm (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mmmm (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mmmm (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mmmm (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-mmmm (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-mmmm (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-mmmm (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mmmm (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mmmm (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mmmm (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mmmm (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mmmm (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mmmm (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mmmm (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mmmm (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mmmm (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mmmm (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mmmm (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mmmm (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mmmm (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mmmm (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-mzmz (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-mzmz (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-mzmz (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mzmz (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mzmz (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mzmz (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-mzmz (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mzmz (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mzmz (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mzmz (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-mzmz (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mzmz (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzmz (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mzmz (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mzmz (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-mzzm (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-mzzm (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-mzzm (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-mzzm (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mzzm (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mzzm (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzzm (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mzzm (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzzm (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzzm (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mzzm (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mzzm (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzzm (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mzzm (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzzm (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzzm (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzzm (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzzm (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzzm (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mzzm (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-mzzm (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzzm (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-mzzm (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzzm (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mzzm (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mzzm (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mzzm (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-mpmp (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mpmp (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mpmp (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpmp (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mpmp (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpmp (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-mpmp (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpmp (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-mpmp (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-mpmp (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mpmp (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpmp (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpmp (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpmp (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpmp (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-mpmp (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mpmp (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mpmp xs ys zs = refl
associateWithCarries bal-mpmp (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-mpmp (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpmp (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpmp (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpmp (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mpmp (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mpmp (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-mpmp (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mpmp (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-mpmp (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-mpzz (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mpzz (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mpzz (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpzz (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-mpzz (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpzz (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpzz (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpzz (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpzz (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-mpzz (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mpzz (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpzz (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpzz (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpzz (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpzz (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpzz (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mpzz (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mpzz (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-mpzz (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-mpzz (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpzz (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mpzz (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mpzz (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mpzz (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-mpzz (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mpzz (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-mpzz (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-mppm (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mppm (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mppm (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mppm (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mppm (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mppm (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mppm (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mppm (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mppm (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mppm (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-mppm (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-mppm (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mppm (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-mppm (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mppm (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mppm (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mppm (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mppm (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-mppm (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-mppm (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-mppm (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-mppm (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mppm xs ys zs = refl
associateWithCarries bal-mppm (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mppm (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-mppm (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-mppm (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-mppm (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-zmmz (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-zmmz (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-zmmz (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-zmmz (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-zmmz (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-zmmz (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-zmmz (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-zmmz (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmmz (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-zmmz (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-zmmz (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-zmmz (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-zmmz (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-zmmz (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmmz (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmmz (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmmz (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmmz (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-zmmz (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-zmmz (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmmz (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmmz (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmmz (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmmz (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmmz (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmmz (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmmz (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-zmzm (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-zmzm (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-zmzm (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-zmzm (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-zmzm (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-zmzm (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-zmzm (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-zmzm (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmzm (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmzm (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-zmzm (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-zmzm (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-zmzm (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-zmzm (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmzm (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmzm (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmzm (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmzm (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmzm (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-zmzm (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-zmzm (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmzm (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-zmzm (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmzm (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmzm (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmzm (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zmzm (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-zzmp (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-zzmp (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-zzmp (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-zzmp (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-zzmp (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzmp (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-zzmp (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzmp (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-zzmp (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-zzmp (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-zzmp (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzmp (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzmp (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzmp (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzmp (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-zzmp (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzmp (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-zzmp (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-zzmp (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzmp (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzmp (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzmp (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzmp (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzmp (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-zzmp (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-zzmp (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-zzmp (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-zzzz (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-zzzz (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-zzzz (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-zzzz (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-zzzz (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-zzzz (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-zzzz (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-zzzz (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-zzzz (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzzz (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-zzzz (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-zzzz (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-zzzz (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-zzpm (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-zzpm (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-zzpm (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-zzpm (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-zzpm (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzpm (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzpm (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzpm (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzpm (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzpm (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-zzpm (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-zzpm (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzpm (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-zzpm (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzpm (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzpm (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzpm (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzpm (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-zzpm (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-zzpm (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-zzpm (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzpm (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-zzpm (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zzpm (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-zzpm (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-zzpm (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-zzpm (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-zpzp (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzmz xs ys zs = refl
associateWithCarries bal-zpzp (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zpzp (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zpzp (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zpzp (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zpzp (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-zpzp (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zpzp (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-zpzp (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-zpzp (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zpzp (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zpzp (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zpzp (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zpzp (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zpzp (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-zpzp (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-zpzp (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-zpzp (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-zpzp (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zpzp (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zpzp (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-zpzp (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-zpzp (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-zpzp (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-zpzp (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-zpzp (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-zpzp (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-zppz (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mzzm xs ys zs = refl
associateWithCarries bal-zppz (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zppz (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zppz (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zppz (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zppz (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zppz (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zppz (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zppz (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-zppz (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-zppz (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zppz (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zppz (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zppz (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zppz (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-zppz (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-zppz (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-zppz (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-zppz (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-zppz (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-zppz (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-zppz (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-mpzz xs ys zs = refl
associateWithCarries bal-zppz (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-zppz (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-zppz (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-zppz (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-zppz (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-pmmp (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-pmmp (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-pmmp (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmmp (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-pmmp (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmmp (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmmp xs ys zs = refl
associateWithCarries bal-pmmp (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmmp (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-pmmp (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-pmmp (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-pmmp (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmmp (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmmp (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmmp (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmmp (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-pmmp (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmmp (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-pmmp (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pmmp (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmmp (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmmp (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmmp (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmmp (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmmp (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pmmp (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmmp (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pmmp (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pmzz (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-pmzz (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-pmzz (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmzz (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-pmzz (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmzz (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmzz (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmzz (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmzz (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-pmzz (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-pmzz (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmzz (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmzz (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmzz (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmzz (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmzz (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmzz (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmzz (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pmzz (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-pmzz (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmzz (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmzz (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmzz (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmzz (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pmzz (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmzz (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pmzz (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pmpm (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-pmpm (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-pmpm (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmpm (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-pmpm (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmpm (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmpm (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmpm (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmpm (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmpm (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-pmpm (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pmpm xs ys zs = refl
associateWithCarries bal-pmpm (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pmpm (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-pmpm (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmpm (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmpm (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmpm (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmpm (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pmpm (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-pmpm (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-pmpm (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmpm (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-pmpm (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmpm (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pmpm (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pmpm (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pmpm (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pzzp (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmmz xs ys zs = refl
associateWithCarries bal-pzzp (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pzzp (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pzzp (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzzp (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzzp (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-pzzp (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzzp (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzmp xs ys zs = refl
associateWithCarries bal-pzzp (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pzzp (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzzp (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzzp (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzzp (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzzp (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzzp (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pzzp (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzzp (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pzzp (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pzzp (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzzp (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzzp (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pzzp (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzzp (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pzzp (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pzzp (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-pzzp (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-pzzp (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-pzpz (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zmzm xs ys zs = refl
associateWithCarries bal-pzpz (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pzpz (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pmzz xs ys zs = refl
associateWithCarries bal-pzpz (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzpz (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzpz (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzpz (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzpz (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzpz (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pzpz (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-pzpz (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzpz (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzpz (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzpz (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzpz (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pzpz (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzpz (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pzpz (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pzpz (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzpm xs ys zs = refl
associateWithCarries bal-pzpz (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzpz (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pzpz (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pzpz (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pzpz (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pzpz (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-pzpz (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-pzpz (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-pppp (neg ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pppp (neg ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pppp (neg ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pppp (neg ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pppp (neg ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pppp (neg ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pppp (neg ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pppp (neg ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pppp (neg ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pppp (zer ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pppp (zer ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pppp (zer ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pppp (zer ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pppp (zer ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pppp (zer ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzzp xs ys zs = refl
associateWithCarries bal-pppp (zer ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-pppp (zer ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-pppp (zer ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-pppp (pos ∷ xs) (neg ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zzzz xs ys zs = refl
associateWithCarries bal-pppp (pos ∷ xs) (neg ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pppp (pos ∷ xs) (neg ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pzpz xs ys zs = refl
associateWithCarries bal-pppp (pos ∷ xs) (zer ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-pppp (pos ∷ xs) (zer ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-pppp (pos ∷ xs) (zer ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-pppp (pos ∷ xs) (pos ∷ ys) (neg ∷ zs)
  rewrite associateWithCarries bal-zppz xs ys zs = refl
associateWithCarries bal-pppp (pos ∷ xs) (pos ∷ ys) (zer ∷ zs)
  rewrite associateWithCarries bal-zpzp xs ys zs = refl
associateWithCarries bal-pppp (pos ∷ xs) (pos ∷ ys) (pos ∷ zs)
  rewrite associateWithCarries bal-pppp xs ys zs = refl

------------------------------------------------------------------------
-- Public arbitrary-depth laws.

commutativeAllDepth :
  ∀ {n : Nat} →
  (x y : Q.Residue3Pow n) →
  Arithmetic.addResidue x y ≡ Arithmetic.addResidue y x
commutativeAllDepth = commuteWithCarry zer

associativeAllDepth :
  ∀ {n : Nat} →
  (x y z : Q.Residue3Pow n) →
  Arithmetic.addResidue (Arithmetic.addResidue x y) z
  ≡ Arithmetic.addResidue x (Arithmetic.addResidue y z)
associativeAllDepth = associateWithCarries bal-zzzz

open Arithmetic.TriadicArithmeticLawReceipt

allDepthArithmeticLaws :
  (n : Nat) →
  Arithmetic.TriadicArithmeticLawReceipt n
allDepthArithmeticLaws n =
  record
    { associativity = associativeAllDepth
    ; commutative = commutativeAllDepth
    }

finiteAdditiveGroupAllDepth :
  (n : Nat) →
  Irrep.FiniteAdditiveGroup n
finiteAdditiveGroupAllDepth n =
  Arithmetic.finiteAdditiveGroup n (allDepthArithmeticLaws n)

arithmeticLawsStatement : String
arithmeticLawsStatement =
  "The ripple-carry balanced-ternary operation is associative and commutative at every finite depth; the proof is a carry-balance bisimulation whose complete finite local transition table is checked definitionally."
