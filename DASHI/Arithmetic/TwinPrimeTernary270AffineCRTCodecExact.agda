module DASHI.Arithmetic.TwinPrimeTernary270AffineCRTCodecExact where

------------------------------------------------------------------------
-- FINITE C2-EQUIVARIANT 3^3 -> 27 CERTIFIED LOCAL CRT SURVIVOR CODE
--
-- Prior source owners: Ternary27Point x/y/z cube, strict C2 sign action,
-- CertifiedPrimePairModulusExact (real local prime-pair sieve), the
-- original 3x5=15 Ibrahim phase quotient and Conway/Guy FRACTRAN
-- history. Distinguish the global 14-orbit action from the 15 quotient.
--
-- Chosen arithmetic wheel: 270 = 27*2*5. Conditions n,n+2 are
-- not divisible by 2,3,5. Exactly 27 residue representatives survive.
-- Encode x,y,z in {-1,0,+1} with digit d in {0,1,2}:
--      n = (41 + 108*d(x) + 30*d(y) + 90*d(z)) mod 270.
-- The map is injective via an EXPLICIT (finite) Nat -> Maybe cube
-- left inverse. The involution of the cube corresponds to
--      n -> -n-2 (mod 270).
-- Finite witnesses prove the real arithmetic local filters; no CRT
-- inverse for arbitrary moduli and no general prime certificate.
--
-- Equal 27 cardinalities DO NOT identify arbitrary spectral or Monster
-- representations. The affine map is chosen by concrete CRT residues,
-- not by a Moonshine/Monster 3B/4B same-object theorem. Original
-- mathematical authors and Ibrahim PR proof ownership preserved.
-- Source-written; no successful Agda kernel typecheck claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Unit using (tt)
open import Data.Nat.DivMod using (_%_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≢_; trans; sym)

import DASHI.Foundations.SSPTritCarrier as T
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Arithmetic.CertifiedPrimePairModulusExact as Pair

ternaryDigit : T.SSPTrit → Nat
ternaryDigit T.sspNegOne = 0
ternaryDigit T.sspZero = 1
ternaryDigit T.sspPosOne = 2

cubeToWheel270 : Geometry.Ternary27Point → Nat
cubeToWheel270 (Geometry.ternary27Point x y z) =
  (41 + 108 * ternaryDigit x + 30 * ternaryDigit y
    + 90 * ternaryDigit z) % 270

-- Exhaustive inverse on the 27 named canonical survivor outputs.
-- Unlisted Nats return nothing. A separate covering theorem for ALL
-- modulo-270 sieve survivors is not asserted by this finite lookup.
wheel270ToCube : Nat → Maybe Geometry.Ternary27Point
wheel270ToCube 41 = just (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspNegOne)
wheel270ToCube 131 = just (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspZero)
wheel270ToCube 221 = just (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspPosOne)
wheel270ToCube 71 = just (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspNegOne)
wheel270ToCube 161 = just (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspZero)
wheel270ToCube 251 = just (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspPosOne)
wheel270ToCube 101 = just (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspNegOne)
wheel270ToCube 191 = just (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspZero)
wheel270ToCube 11 = just (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspPosOne)
wheel270ToCube 149 = just (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspNegOne)
wheel270ToCube 239 = just (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspZero)
wheel270ToCube 59 = just (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspPosOne)
wheel270ToCube 179 = just (Geometry.ternary27Point T.sspZero T.sspZero T.sspNegOne)
wheel270ToCube 269 = just (Geometry.ternary27Point T.sspZero T.sspZero T.sspZero)
wheel270ToCube 89 = just (Geometry.ternary27Point T.sspZero T.sspZero T.sspPosOne)
wheel270ToCube 209 = just (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspNegOne)
wheel270ToCube 29 = just (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspZero)
wheel270ToCube 119 = just (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspPosOne)
wheel270ToCube 257 = just (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspNegOne)
wheel270ToCube 77 = just (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspZero)
wheel270ToCube 167 = just (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspPosOne)
wheel270ToCube 17 = just (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspNegOne)
wheel270ToCube 107 = just (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspZero)
wheel270ToCube 197 = just (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspPosOne)
wheel270ToCube 47 = just (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspNegOne)
wheel270ToCube 137 = just (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspZero)
wheel270ToCube 227 = just (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspPosOne)
wheel270ToCube _ = nothing

wheel270DecodeEncode :
  (point : Geometry.Ternary27Point) →
  wheel270ToCube (cubeToWheel270 point) ≡ just point
wheel270DecodeEncode (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspNegOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspZero) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspPosOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspNegOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspZero) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspPosOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspNegOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspZero) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspPosOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspNegOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspZero) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspPosOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspZero T.sspZero T.sspNegOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspZero T.sspZero T.sspZero) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspZero T.sspZero T.sspPosOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspNegOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspZero) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspPosOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspNegOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspZero) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspPosOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspNegOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspZero) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspPosOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspNegOne) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspZero) = refl
wheel270DecodeEncode (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspPosOne) = refl

cube270GlobalAntipode : Geometry.Ternary27Point → Geometry.Ternary27Point
cube270GlobalAntipode (Geometry.ternary27Point x y z) =
  Geometry.ternary27Point
    (Orbit.strictAntipode x)
    (Orbit.strictAntipode y)
    (Orbit.strictAntipode z)

-- This is the exact affine *unordered pair* swap, not ordinary
-- additive inverse n -> -n (it is centred at n=-1).
wheel270AffinePairReversal :
  (point : Geometry.Ternary27Point) →
  (cubeToWheel270 point +
    cubeToWheel270 (cube270GlobalAntipode point) + 2) % 270 ≡ 0
wheel270AffinePairReversal (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspNegOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspZero) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspPosOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspNegOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspZero) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspPosOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspNegOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspZero) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspPosOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspNegOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspZero) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspPosOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspZero T.sspZero T.sspNegOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspZero T.sspZero T.sspZero) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspZero T.sspZero T.sspPosOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspNegOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspZero) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspPosOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspNegOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspZero) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspPosOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspNegOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspZero) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspPosOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspNegOne) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspZero) = refl
wheel270AffinePairReversal (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspPosOne) = refl

wheel270ModTwo :
  (point : Geometry.Ternary27Point) →
  (cubeToWheel270 point) % 2 ≡ 1
wheel270ModTwo (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspNegOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspZero) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspPosOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspNegOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspZero) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspPosOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspNegOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspZero) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspPosOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspNegOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspZero) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspPosOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspZero T.sspZero T.sspNegOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspZero T.sspZero T.sspZero) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspZero T.sspZero T.sspPosOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspNegOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspZero) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspPosOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspNegOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspZero) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspPosOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspNegOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspZero) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspPosOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspNegOne) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspZero) = refl 
wheel270ModTwo (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspPosOne) = refl 

wheel270PlusTwoModTwo :
  (point : Geometry.Ternary27Point) →
  (cubeToWheel270 point + 2) % 2 ≡ 1
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspNegOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspZero) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspPosOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspNegOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspZero) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspPosOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspNegOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspZero) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspPosOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspNegOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspZero) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspPosOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspZero T.sspZero T.sspNegOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspZero T.sspZero T.sspZero) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspZero T.sspZero T.sspPosOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspNegOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspZero) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspPosOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspNegOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspZero) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspPosOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspNegOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspZero) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspPosOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspNegOne) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspZero) = refl 
wheel270PlusTwoModTwo (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspPosOne) = refl 

wheel270ModThree :
  (point : Geometry.Ternary27Point) →
  (cubeToWheel270 point) % 3 ≡ 2
wheel270ModThree (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspNegOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspZero) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspPosOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspNegOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspZero) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspPosOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspNegOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspZero) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspPosOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspNegOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspZero) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspPosOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspZero T.sspZero T.sspNegOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspZero T.sspZero T.sspZero) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspZero T.sspZero T.sspPosOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspNegOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspZero) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspPosOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspNegOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspZero) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspPosOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspNegOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspZero) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspPosOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspNegOne) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspZero) = refl 
wheel270ModThree (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspPosOne) = refl 

wheel270PlusTwoModThree :
  (point : Geometry.Ternary27Point) →
  (cubeToWheel270 point + 2) % 3 ≡ 1
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspNegOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspZero) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspPosOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspNegOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspZero) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspPosOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspNegOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspZero) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspPosOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspNegOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspZero) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspPosOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspZero T.sspZero T.sspNegOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspZero T.sspZero T.sspZero) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspZero T.sspZero T.sspPosOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspNegOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspZero) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspPosOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspNegOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspZero) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspPosOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspNegOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspZero) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspPosOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspNegOne) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspZero) = refl 
wheel270PlusTwoModThree (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspPosOne) = refl 

wheel270NotZeroModFive :
  (point : Geometry.Ternary27Point) →
  (cubeToWheel270 point) % 5 ≢ 0
wheel270NotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspNegOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspZero) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspPosOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspNegOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspZero) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspPosOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspNegOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspZero) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspPosOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspNegOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspZero) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspPosOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspZero T.sspZero T.sspNegOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspZero T.sspZero T.sspZero) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspZero T.sspZero T.sspPosOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspNegOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspZero) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspPosOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspNegOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspZero) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspPosOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspNegOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspZero) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspPosOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspNegOne) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspZero) ()
wheel270NotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspPosOne) ()

wheel270PlusTwoNotZeroModFive :
  (point : Geometry.Ternary27Point) →
  (cubeToWheel270 point + 2) % 5 ≢ 0
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspNegOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspZero) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspNegOne T.sspPosOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspNegOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspZero) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspZero T.sspPosOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspNegOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspZero) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspNegOne T.sspPosOne T.sspPosOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspNegOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspZero) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspZero T.sspNegOne T.sspPosOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspZero T.sspZero T.sspNegOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspZero T.sspZero T.sspZero) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspZero T.sspZero T.sspPosOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspNegOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspZero) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspZero T.sspPosOne T.sspPosOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspNegOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspZero) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspNegOne T.sspPosOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspNegOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspZero) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspZero T.sspPosOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspNegOne) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspZero) ()
wheel270PlusTwoNotZeroModFive (Geometry.ternary27Point T.sspPosOne T.sspPosOne T.sspPosOne) ()

oneNotZero : 1 ≡ 0 → ⊥
oneNotZero ()

twoNotZero : 2 ≡ 0 → ⊥
twoNotZero ()

-- Actual *certified* prime-axis local filters, not a surrogate Boolean.
-- The axis is supplied with a real Data.Nat.Primality.Prime witness.
wheel270LocalPrimeTwo :
  (axis : Pair.CertifiedPrimeAxis) →
  Pair.primeModulus axis ≡ 2 →
  (point : Geometry.Ternary27Point) →
  Pair.LocalPairSurvives axis (cubeToWheel270 point)
wheel270LocalPrimeTwo axis same point
  rewrite same =
  (λ z → oneNotZero (trans (sym (wheel270ModTwo point)) z))
  ,
  (λ z → oneNotZero (trans (sym (wheel270PlusTwoModTwo point)) z))

wheel270LocalPrimeThree :
  (axis : Pair.CertifiedPrimeAxis) →
  Pair.primeModulus axis ≡ 3 →
  (point : Geometry.Ternary27Point) →
  Pair.LocalPairSurvives axis (cubeToWheel270 point)
wheel270LocalPrimeThree axis same point
  rewrite same =
  (λ z → twoNotZero (trans (sym (wheel270ModThree point)) z))
  ,
  (λ z → oneNotZero (trans (sym (wheel270PlusTwoModThree point)) z))

wheel270LocalPrimeFive :
  (axis : Pair.CertifiedPrimeAxis) →
  Pair.primeModulus axis ≡ 5 →
  (point : Geometry.Ternary27Point) →
  Pair.LocalPairSurvives axis (cubeToWheel270 point)
wheel270LocalPrimeFive axis same point
  rewrite same =
  wheel270NotZeroModFive point ,
  wheel270PlusTwoNotZeroModFive point

-- Reuse the declared pair-sieve predicate on three ACTUAL
-- separately certified axes, preserving their exact order.
wheel270PassesCertifiedTwoThreeFive :
  (axis2 axis3 axis5 : Pair.CertifiedPrimeAxis) →
  Pair.primeModulus axis2 ≡ 2 →
  Pair.primeModulus axis3 ≡ 3 →
  Pair.primeModulus axis5 ≡ 5 →
  (point : Geometry.Ternary27Point) →
  Pair.AllPairSurvive (axis2 ∷ axis3 ∷ axis5 ∷ [])
    (cubeToWheel270 point)
wheel270PassesCertifiedTwoThreeFive axis2 axis3 axis5
    eq2 eq3 eq5 point =
  wheel270LocalPrimeTwo axis2 eq2 point
  ,
  ( wheel270LocalPrimeThree axis3 eq3 point
  , (wheel270LocalPrimeFive axis5 eq5 point , tt)
  )
