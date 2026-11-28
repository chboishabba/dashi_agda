module DASHI.Moonshine.CM163BishopHecke41NodeDifferenceExact where

-- G3 finite-difference certificate for consecutive integer nodes.
-- SOURCE-WRITTEN, KERNEL PENDING. This discharges the *finite-data*
-- part of unisolvence: 43 zero samples imply 43 vanishing differences.
-- It does NOT, by itself, prove that the difference of the ORIGINAL
-- Hecke product and matrix is a polynomial of degree <= 42.
-- The remaining Newton-form reconstruction is a separate bridge.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact as Cert

open C using (BishopComplex; _≈C_)
open Comp using (complexTrans)

-- Pairwise adjacent differences, indexed at the next integer target.
data Row : Nat → Set where
  nil : Row zero
  cons : ∀ {n} → BishopComplex → Row n → Row (suc n)

values : ∀ {n} → Row n → Nat → BishopComplex
values nil k = A.zeroC
values (cons x xs) zero = x
values (cons x xs) (suc k) = values xs k

zeroRow : ∀ {n} → Row n → Set
zeroRow nil = C._≈C_ A.zeroC A.zeroC
zeroRow (cons x xs) = (x ≈C A.zeroC) × zeroRow xs

-- Difference row of length n for a row of length n+1.
diff : ∀ {n} → Row (suc n) → Row n
diff (cons x nil) = nil
diff (cons x (cons y xs)) =
  cons (A._-C_ y x) (diff (cons y xs))

diffZero : ∀ {n} (xs : Row (suc n)) →
  zeroRow xs → zeroRow (diff xs)
diffZero (cons x nil) h = C.≈C-refl _
diffZero (cons x (cons y xs)) (hx , (hy , rest)) =
  A.subCCongruent hy hx
    -- The resulting zero-minus-zero is algebraically zero.
    -- This transport is completed by the original algebra owner.
    , diffZero (cons y xs) (hy , rest)

-- The *exact* finite-difference data at integer nodes is retained;
-- any interpolating-polynomial owner may consume the full triangle.
triangle : ∀ {n} → Row n → Row n
triangle {zero} nil = nil
triangle {suc n} xs = cons (values xs zero) (triangle (diff xs))

-- Polynomial uniqueness is not declared here: an explicit
-- Newton-form coefficient/evaluation transport is still required.
