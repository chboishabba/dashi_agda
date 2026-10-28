module DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact where

------------------------------------------------------------------------
-- Q26: UNBOUNDED NAT = (BOUNDED RESIDUE, UNBOUNDED PERIOD)
--
-- Retain the original 3x3x3 wheel and its exact 27-case survivor
-- inverse. The FULL residue code is not enough for actual prime
-- classification (59 and 329 share one wheel point). The unbounded
-- Nat quotient must be carried independently of every sign/phase
-- quotient. This is *not* the general prime-modulus CRT theorem.
--
-- Original owner: TwinPrimeTernary270AffineCRTCodecExact.
-- Existing sieve-completeness source:
-- TwinPrimeTernary270SurvivorCoverageExact.
-- Arithmetic: inherited Euclidean division, standard library.
-- No postulates; no unproved primality claim; kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Data.Nat using (_/_; _%_; _<_)
open import Data.Nat.DivMod using
  (m%n<n; m≡m%n+[m/n]*n; [m+kn]%n≡m%n; m<n⇒m%n≡m)
open import Data.Fin.Base using (Fin; fromℕ<; toℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.SSPTritCarrier as T
import DASHI.Arithmetic.TwinPrimeTernary270AffineCRTCodecExact as Codec
import DASHI.Arithmetic.TwinPrimeTernary270SurvivorCoverageExact as Coverage

finiteResidue270 : Nat → Fin 270
finiteResidue270 n = fromℕ< (m%n<n n 270)

finiteResidue270Value : (n : Nat) →
  toℕ (finiteResidue270 n) ≡ n % 270
finiteResidue270Value n = refl

record NatPeriod270 : Set where
  constructor natPeriod270
  field
    periodIndex : Nat
    boundedResidue : Fin 270
open NatPeriod270 public

encodeNatPeriod270 : Nat → NatPeriod270
encodeNatPeriod270 n =
  natPeriod270 (n / 270) (finiteResidue270 n)

decodeNatPeriod270 : NatPeriod270 → Nat
decodeNatPeriod270 code =
  toℕ (boundedResidue code) + periodIndex code * 270

-- The unbounded quotient is NOT optional. This holds for ALL Nats,
-- unlike the 27-cell survivor codec, which has a restricted domain.
decodeEncodeNatPeriod270 : (n : Nat) →
  decodeNatPeriod270 (encodeNatPeriod270 n) ≡ n
decodeEncodeNatPeriod270 n =
  sym (m≡m%n+[m/n]*n n 270)

-- Reuse the existing complete inverse for the actual 27
-- admissible residue values, retaining the original x/y/z type.
certifiedResidueHasCube :
  (n : Nat) →
  Coverage.Wheel270Survives (n % 270) →
  Σ Geometry.Ternary27Point
    (λ cube → Codec.cubeToWheel270 cube ≡ n % 270)
certifiedResidueHasCube n surviving =
  Coverage.wheel270CompleteFin (finiteResidue270 n) surviving

-- A signed cube with a separately retained period index.
-- This representation applies only to the periodic survivor set.
NatCubePeriod270 : Set
NatCubePeriod270 = Nat × Geometry.Ternary27Point

decodeCubePeriod270 : NatCubePeriod270 → Nat
decodeCubePeriod270 (period , cube) =
  Codec.cubeToWheel270 cube + period * 270

-- Every admitted integer has an exact cube + unbounded period
-- representation. The decoded Nat is *the original integer*, not
-- just the residue or its sign orbit.
encodeCertifiedCubePeriod270 :
  (n : Nat) →
  Coverage.Wheel270Survives (n % 270) →
  Σ NatCubePeriod270
    (λ code → decodeCubePeriod270 code ≡ n)
encodeCertifiedCubePeriod270 n survives
  with certifiedResidueHasCube n survives
... | cube , cubeAtResidue =
  (n / 270 , cube) ,
    trans
      (cong (λ r → r + (n / 270) * 270) cubeAtResidue)
      (sym (m≡m%n+[m/n]*n n 270))

cubeResidueBound :
  (cube : Geometry.Ternary27Point) →
  Codec.cubeToWheel270 cube < 270
cubeResidueBound (Geometry.ternary27Point x y z) =
  m%n<n
    (41 + 108 * Codec.ternaryDigit x +
       30 * Codec.ternaryDigit y + 90 * Codec.ternaryDigit z)
    270

cubePeriodResidueRoundTrip :
  (period : Nat) (cube : Geometry.Ternary27Point) →
  decodeCubePeriod270 (period , cube) % 270 ≡
    Codec.cubeToWheel270 cube
cubePeriodResidueRoundTrip period cube =
  trans
    ([m+kn]%n≡m%n (Codec.cubeToWheel270 cube) period 270)
    (m<n⇒m%n≡m (cubeResidueBound cube))

cubePeriodDecodeToCube :
  (period : Nat) (cube : Geometry.Ternary27Point) →
  Codec.wheel270ToCube
    (decodeCubePeriod270 (period , cube) % 270) ≡
  just cube
cubePeriodDecodeToCube period cube =
  trans
    (cong Codec.wheel270ToCube
      (cubePeriodResidueRoundTrip period cube))
    (Codec.wheel270DecodeEncode cube)

-- Semantic cut: to decide genuine TwinPrimeAt one must apply
-- the existing Nat prime decider to decodeCubePeriod270.
-- The quotient-only rule cannot determine it, as Q25 witnesses.
