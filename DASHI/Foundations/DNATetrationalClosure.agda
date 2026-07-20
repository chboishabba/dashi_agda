module DASHI.Foundations.DNATetrationalClosure where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_^_)

four : Nat
four = suc (suc (suc (suc zero)))

tower : Nat → Nat
tower zero = four
tower (suc n) = four ^ tower n

tower-zero : tower zero ≡ four
tower-zero = refl

tower-one : tower (suc zero) ≡ four ^ four
tower-one = refl

data ScaleReading : Set where
  tensorRankReading : ScaleReading
  supportSizeReading : ScaleReading
  configurationCountReading : ScaleReading
  recursiveClosureDepthReading : ScaleReading

record RecursiveConfigurationClosure : Set₁ where
  constructor closure
  field
    cell : Set
    successor : Set
    successorIsLabellingSpace : successor ≡ (cell → Set)
open RecursiveConfigurationClosure public

record DNATetrationalBoundary : Set where
  constructor boundary
  field
    rankAndDepthSeparated : ScaleReading
    finiteSupportReading : ScaleReading
    configurationReading : ScaleReading
    towerDepthReading : ScaleReading
    surrealCutConstructionProvided : Set
open DNATetrationalBoundary public

canonicalDNATetrationalBoundary : DNATetrationalBoundary
canonicalDNATetrationalBoundary =
  boundary
    tensorRankReading
    supportSizeReading
    configurationCountReading
    recursiveClosureDepthReading
    Nat

-- `surrealCutConstructionProvided` is deliberately only a carrier field here;
-- this module does not claim that tetration alone yields Conway surreal numbers.
