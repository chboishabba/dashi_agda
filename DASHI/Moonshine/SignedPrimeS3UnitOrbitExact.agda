module DASHI.Moonshine.SignedPrimeS3UnitOrbitExact where

-- Source-written, kernel pending. Finite candidate scan independent of Ogg.
-- A nonsquare reflection multiplier and an order-three root produce
-- regular S3 orbits even when the unit-group C3 extension does not split.
-- Use the canonical 43 nonabelian alphabet, not a second group table.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_∸_; _≤_)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥)
open import DASHI.Foundations.Base369Nat using (_%_)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Codec.BalancedTritBitFibre using (positiveSign; negativeSign)
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as G
import DASHI.Moonshine.SignedNonaryPrime43CodecExact as W
open W using (Hex; hex)
import DASHI.Moonshine.SignedNonaryPrime43S3GeometryExact as S
import DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact as Cert

data Level : Set where
  p7 p13 p19 p31 p37 p43 p61 p67 p73 : Level

orbitCount generator reflectionExponent : Level → Nat
orbitCount p7 = 1
orbitCount p13 = 2
orbitCount p19 = 3
orbitCount p31 = 5
orbitCount p37 = 6
orbitCount p43 = 7
orbitCount p61 = 10
orbitCount p67 = 11
orbitCount p73 = 12

generator p7 = 3
generator p13 = 2
generator p19 = 2
generator p31 = 3
generator p37 = 2
generator p43 = 3
generator p61 = 2
generator p67 = 2
generator p73 = 5

reflectionExponent p7 = 3
reflectionExponent p13 = 1
reflectionExponent p19 = 9
reflectionExponent p31 = 15
reflectionExponent p37 = 1
reflectionExponent p43 = 21
reflectionExponent p61 = 1
reflectionExponent p67 = 33
reflectionExponent p73 = 1

unitCount modulus : Level → Nat
unitCount l = 6 * orbitCount l
modulus l = suc (unitCount l)

reduce : Level → Nat → Nat
reduce l n = n % suc (unitCount l)

power : Level → Nat → Nat → Nat
power l a zero = 1
power l a (suc n) = reduce l (a * power l a n)

root reflectionConstant : Level → Nat
root l = power l (generator l) (4 * orbitCount l)
reflectionConstant l = power l (generator l) (reflectionExponent l)

phase : Trit → Nat
phase neg = 0
phase zer = 1
phase pos = 2

-- Even exponents 2j, 0<=j<m, choose representatives of the free
-- C3 action on squares. Their reflected partners are nonsquares.
-- The exponent 6m-2j computes the inverse without integer division.
label : Level → Nat → Hex → Nat
label l j (hex t positiveSign) =
  power l (generator l) (2 * j + 4 * orbitCount l * phase t)
label l j (hex t negativeSign) =
  power l (generator l) (reflectionExponent l + 2 * (3 * orbitCount l ∸ j)
                         + 4 * orbitCount l * phase t)

incBase : Nat × Hex → Nat × Hex
incBase (j , h) = suc j , h

state : Nat → Nat × Hex
state zero = 0 , hex neg positiveSign
state (suc zero) = 0 , hex neg negativeSign
state (suc (suc zero)) = 0 , hex zer positiveSign
state (suc (suc (suc zero))) = 0 , hex zer negativeSign
state (suc (suc (suc (suc zero)))) = 0 , hex pos positiveSign
state (suc (suc (suc (suc (suc zero))))) = 0 , hex pos negativeSign
state (suc (suc (suc (suc (suc (suc n)))))) = incBase (state n)

encode : Level → Nat → Nat
encode l k = label l (proj₁ (state k)) (proj₂ (state k))

search : Level → Nat → Nat → Nat → Nat
search l u i zero = i
search l u i (suc n) with encode l i ≟ u
... | yes _ = i
... | no _ = search l u (suc i) n

decode : Level → Nat → Nat
decode l u = search l u 0 (unitCount l)

actLabel : Level → G.TriPermutation → Nat → Nat
actLabel l g k =
  label l (proj₁ (state k)) (S.actHex g (proj₂ (state k)))

top : Level → Nat
top l = unitCount l ∸ 1

-- Reuse the original finite proof-bearing prefix gate, not hashes.
record FamilyGate (l : Level) : Set where
  field
    decodeEncode : Cert.Through (top l) (λ k → decode l (encode l k) ≡ k)
    encodeDecode : Cert.Through (top l) (λ k → encode l (decode l (suc k)) ≡ suc k)
    rotateRead : Cert.Through (top l) (λ k →
      actLabel l G.permRotate k ≡ reduce l (root l * encode l k))
    reflectRead : Cert.Through (top l) (λ k →
      reduce l (actLabel l G.permSwapMidHigh k * encode l k) ≡ reflectionConstant l)
open FamilyGate public

-- These explicit witnesses are concrete reductions; kernel not yet run.
familyGate : (l : Level) → FamilyGate l
familyGate p7 = record
  { decodeEncode = (((((refl , refl) , refl) , refl) , refl) , refl)
  ; encodeDecode = (((((refl , refl) , refl) , refl) , refl) , refl)
  ; rotateRead = (((((refl , refl) , refl) , refl) , refl) , refl)
  ; reflectRead = (((((refl , refl) , refl) , refl) , refl) , refl) }

familyGate p13 = record
  { decodeEncode = (((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; encodeDecode = (((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; rotateRead = (((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; reflectRead = (((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) }

familyGate p19 = record
  { decodeEncode = (((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; encodeDecode = (((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; rotateRead = (((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; reflectRead = (((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) }

familyGate p31 = record
  { decodeEncode = (((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; encodeDecode = (((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; rotateRead = (((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; reflectRead = (((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) }

familyGate p37 = record
  { decodeEncode = (((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; encodeDecode = (((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; rotateRead = (((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; reflectRead = (((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) }

familyGate p43 = record
  { decodeEncode = (((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; encodeDecode = (((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; rotateRead = (((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; reflectRead = (((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) }

familyGate p61 = record
  { decodeEncode = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; encodeDecode = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; rotateRead = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; reflectRead = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) }

familyGate p67 = record
  { decodeEncode = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; encodeDecode = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; rotateRead = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; reflectRead = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) }

familyGate p73 = record
  { decodeEncode = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; encodeDecode = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; rotateRead = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl)
  ; reflectRead = (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((refl , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) , refl) }

rootCube : ∀ l → power l (root l) 3 ≡ 1
rootCube p7 = refl
rootCube p13 = refl
rootCube p19 = refl
rootCube p31 = refl
rootCube p37 = refl
rootCube p43 = refl
rootCube p61 = refl
rootCube p67 = refl
rootCube p73 = refl

rootNontrivial : ∀ l → root l ≡ 1 → ⊥
rootNontrivial p7 ()
rootNontrivial p13 ()
rootNontrivial p19 ()
rootNontrivial p31 ()
rootNontrivial p37 ()
rootNontrivial p43 ()
rootNontrivial p61 ()
rootNontrivial p67 ()
rootNontrivial p73 ()

-- The cyclic orientation matches the corrected original 43 chart.
root43 : root p43 ≡ 6
root43 = refl

reflection43 : reflectionConstant p43 ≡ 42
reflection43 = refl

-- Retain the full original native S3 composition on each Hex. This
-- finite family is a bijection of observed unit residues; no claim of
-- Ogg classification, modular Hecke equivariance, or physical isometry.
