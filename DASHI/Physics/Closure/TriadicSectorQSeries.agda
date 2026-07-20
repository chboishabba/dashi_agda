module DASHI.Physics.Closure.TriadicSectorQSeries where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Small exact vector carrier for finite q-series prefixes.

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n : Nat} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_

mapVec :
  ∀ {A B : Set} {n : Nat} →
  (A → B) →
  Vec A n →
  Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

------------------------------------------------------------------------
-- Coefficient algebra and sector trace tower.

record QSeriesCarrier : Set₁ where
  field
    Coeff : Set
    zeroᶜ : Coeff
    oneᶜ : Coeff
    _+ᶜ_ : Coeff → Coeff → Coeff
    _*ᶜ_ : Coeff → Coeff → Coeff

open QSeriesCarrier public

record SectorTraceTower (C : QSeriesCarrier) : Set₁ where
  field
    Sector : Set
    traceCoefficient :
      Nat →
      Sector →
      Coeff C

open SectorTraceTower public

coefficientSequence :
  (C : QSeriesCarrier) →
  (T : SectorTraceTower C) →
  Sector T →
  Nat →
  Coeff C
coefficientSequence C T s n = traceCoefficient T n s

shiftTraceTower :
  (C : QSeriesCarrier) →
  SectorTraceTower C →
  SectorTraceTower C
shiftTraceTower C T =
  record
    { Sector = Sector T
    ; traceCoefficient = λ k sector → traceCoefficient T (suc k) sector
    }

qSeriesPrefix :
  (C : QSeriesCarrier) →
  (T : SectorTraceTower C) →
  (s : Sector T) →
  (n : Nat) →
  Vec (Coeff C) n
qSeriesPrefix C T s zero = []
qSeriesPrefix C T s (suc n) =
  traceCoefficient T zero s
  ∷ qSeriesPrefix C (shiftTraceTower C T) s n

------------------------------------------------------------------------
-- Exact finite reconstruction of a coefficient prefix.

record FiniteQSeriesCodec
  (C : QSeriesCarrier)
  (n : Nat) : Set₁ where
  field
    Latent : Set
    compress : Vec (Coeff C) n → Latent
    decode : Latent → Vec (Coeff C) n
    decodeCompress :
      (xs : Vec (Coeff C) n) →
      decode (compress xs) ≡ xs

open FiniteQSeriesCodec public

identityQSeriesCodec :
  (C : QSeriesCarrier) →
  (n : Nat) →
  FiniteQSeriesCodec C n
identityQSeriesCodec C n =
  record
    { Latent = Vec (Coeff C) n
    ; compress = λ xs → xs
    ; decode = λ xs → xs
    ; decodeCompress = λ xs → refl
    }

------------------------------------------------------------------------
-- Candidate laws to test before promotion to an automorphic lane.

record RationalRecurrenceGate
  (C : QSeriesCarrier)
  (T : SectorTraceTower C) : Set₁ where
  field
    sector : Sector T
    recurrenceOrder : Nat
    recurrenceCoefficients : Vec (Coeff C) recurrenceOrder
    recurrenceHoldsFrom : Nat
    recurrenceLaw : (n : Nat) → Set

open RationalRecurrenceGate public

record HeckeProbe
  (C : QSeriesCarrier)
  (T : SectorTraceTower C) : Set₁ where
  field
    sector : Sector T
    OperatorIndex : Set
    heckeOperator :
      OperatorIndex →
      (Nat → Coeff C) →
      Nat →
      Coeff C
    eigenvalue : OperatorIndex → Coeff C
    heckeEigenLaw : (index : OperatorIndex) → Set

open HeckeProbe public

record PAdicCongruenceGate
  (C : QSeriesCarrier)
  (T : SectorTraceTower C) : Set₁ where
  field
    sector : Sector T
    Modulus : Set
    congruent : Modulus → Coeff C → Coeff C → Set
    modulusAtDepth : Nat → Modulus
    depthCongruence : (n : Nat) → Set

open PAdicCongruenceGate public

------------------------------------------------------------------------
-- Explicit claim boundary.

qSeriesStatement : String
qSeriesStatement =
  "Sector traces produce exact finite q-series prefixes. Rational recurrence, Hecke-eigen, and p-adic congruence behaviour are separate typed gates rather than consequences of naming a generating function."

qSeriesBoundary : String
qSeriesBoundary =
  "No modular transformation law, convergence domain, Eisenstein expansion, or automorphic representation is inferred from a finite coefficient prefix alone."
