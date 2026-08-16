module DASHI.Arithmetic.SixWheelCRTExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- G. H. Hardy and E. M. Wright, revised by D. R. Heath-Brown and J. H.
-- Silverman,
-- "An Introduction to the Theory of Numbers", sixth edition,
-- Oxford University Press, 2008.
-- DOI: 10.1093/oso/9780199219858.001.0001.
--
-- Fernando Q. Gouvea,
-- "p-adic Numbers: An Introduction", second edition, Springer, 1997.
-- DOI: 10.1007/978-3-642-59058-0.
--
-- DASHI CONTRIBUTION
--
-- Construct the arithmetic CRT chart for the concrete {2,3} sieve rather than
-- identifying a generic mixed-radix cardinal bijection with CRT.  The six
-- residue classes modulo 6 map exactly to their residues modulo 2 and 3:
--
--   0 -> (0,0)   1 -> (1,1)   2 -> (0,2)
--   3 -> (1,0)   4 -> (0,1)   5 -> (1,2).
--
-- Both directions are explicit and inverse.  The survivor classes 1 and 5 are
-- exactly the two coordinates for which neither prime-coordinate is zero.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁)

import DASHI.Arithmetic.SixWheelSieveCountExact as Wheel

CRT23 : Set
CRT23 = Fin 2 × Fin 3

r6ToCRT23 : Wheel.Residue6 → CRT23
r6ToCRT23 Wheel.r0 = Fin.zero , Fin.zero
r6ToCRT23 Wheel.r1 = Fin.suc Fin.zero , Fin.suc Fin.zero
r6ToCRT23 Wheel.r2 = Fin.zero , Fin.suc (Fin.suc Fin.zero)
r6ToCRT23 Wheel.r3 = Fin.suc Fin.zero , Fin.zero
r6ToCRT23 Wheel.r4 = Fin.zero , Fin.suc Fin.zero
r6ToCRT23 Wheel.r5 = Fin.suc Fin.zero , Fin.suc (Fin.suc Fin.zero)

crt23ToR6 : CRT23 → Wheel.Residue6
crt23ToR6 (Fin.zero , Fin.zero) = Wheel.r0
crt23ToR6 (Fin.zero , Fin.suc Fin.zero) = Wheel.r4
crt23ToR6 (Fin.zero , Fin.suc (Fin.suc Fin.zero)) = Wheel.r2
crt23ToR6 (Fin.suc Fin.zero , Fin.zero) = Wheel.r3
crt23ToR6 (Fin.suc Fin.zero , Fin.suc Fin.zero) = Wheel.r1
crt23ToR6 (Fin.suc Fin.zero , Fin.suc (Fin.suc Fin.zero)) = Wheel.r5

r6CRT23RoundTrip :
  (r : Wheel.Residue6) →
  crt23ToR6 (r6ToCRT23 r) ≡ r
r6CRT23RoundTrip Wheel.r0 = refl
r6CRT23RoundTrip Wheel.r1 = refl
r6CRT23RoundTrip Wheel.r2 = refl
r6CRT23RoundTrip Wheel.r3 = refl
r6CRT23RoundTrip Wheel.r4 = refl
r6CRT23RoundTrip Wheel.r5 = refl

crt23R6RoundTrip :
  (pair : CRT23) →
  r6ToCRT23 (crt23ToR6 pair) ≡ pair
crt23R6RoundTrip (Fin.zero , Fin.zero) = refl
crt23R6RoundTrip (Fin.zero , Fin.suc Fin.zero) = refl
crt23R6RoundTrip (Fin.zero , Fin.suc (Fin.suc Fin.zero)) = refl
crt23R6RoundTrip (Fin.suc Fin.zero , Fin.zero) = refl
crt23R6RoundTrip (Fin.suc Fin.zero , Fin.suc Fin.zero) = refl
crt23R6RoundTrip (Fin.suc Fin.zero , Fin.suc (Fin.suc Fin.zero)) = refl

data NonzeroMod2 : Fin 2 → Set where
  oneMod2 : NonzeroMod2 (Fin.suc Fin.zero)

data NonzeroMod3 : Fin 3 → Set where
  oneMod3 : NonzeroMod3 (Fin.suc Fin.zero)
  twoMod3 : NonzeroMod3 (Fin.suc (Fin.suc Fin.zero))

record CRT23Survivor (pair : CRT23) : Set where
  constructor crt23Survivor
  field
    nonzeroMod2 : NonzeroMod2 (proj₁ pair)
    nonzeroMod3 : NonzeroMod3 (proj₂ pair)

r1SurvivesCRT : CRT23Survivor (r6ToCRT23 Wheel.r1)
r1SurvivesCRT = crt23Survivor oneMod2 oneMod3

r5SurvivesCRT : CRT23Survivor (r6ToCRT23 Wheel.r5)
r5SurvivesCRT = crt23Survivor oneMod2 twoMod3

excludedCannotSurviveCRT :
  (r : Wheel.ExcludedResidue6) →
  CRT23Survivor
    (r6ToCRT23 (Wheel.forgetResidueClass (inj₁ r))) →
  ⊥
excludedCannotSurviveCRT Wheel.e0 (crt23Survivor () _)
excludedCannotSurviveCRT Wheel.e2 (crt23Survivor () _)
excludedCannotSurviveCRT Wheel.e3 (crt23Survivor _ ())
excludedCannotSurviveCRT Wheel.e4 (crt23Survivor () _)
