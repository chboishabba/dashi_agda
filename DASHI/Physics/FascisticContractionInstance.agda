module DASHI.Physics.FascisticContractionInstance where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _<_)
open import Data.Product using (Σ; _,_)

import Contraction as C
import DASHI.Metric.AgreementUltrametric as AU
import DASHI.Physics.RealTernaryCarrier as RTC

record FascisticEndoMap (n : Nat) : Set where
  constructor fascisticEndoMap
  field
    K : RTC.Carrier n → RTC.Carrier n
    nonExpanding :
      ∀ x y →
      AU.dNat (K x) (K y) ≤ AU.dNat x y

record StrictFascisticMap (n : Nat) : Set where
  constructor strictFascisticMap
  field
    K : RTC.Carrier n → RTC.Carrier n
    strictlyContracting :
      ∀ {x y} →
      x C.≢ y →
      AU.dNat (K x) (K y) < AU.dNat x y

strictToContractive≢ :
  ∀ {n} (M : StrictFascisticMap n) →
  C.Contractive≢
    (AU.ultrametricVec {n = n})
    (StrictFascisticMap.K M)
strictToContractive≢ M =
  record
    { contraction≢ = StrictFascisticMap.strictlyContracting M
    }

record FixedPointCertificate {n : Nat} (M : StrictFascisticMap n) : Set where
  constructor fixedPointCertificate
  field
    fp : RTC.Carrier n
    fixed : StrictFascisticMap.K M fp ≡ fp
    unique : ∀ x → StrictFascisticMap.K M x ≡ x → x ≡ fp

strictContractionFromCertificate :
  ∀ {n} (M : StrictFascisticMap n) →
  FixedPointCertificate M →
  C.StrictContraction
    (AU.ultrametricVec {n = n})
    (StrictFascisticMap.K M)
strictContractionFromCertificate M cert =
  record
    { contractive≢ = strictToContractive≢ M
    ; fp = FixedPointCertificate.fp cert
    ; fixed = FixedPointCertificate.fixed cert
    ; unique = FixedPointCertificate.unique cert
    }

record ContractionDescent {n : Nat} (M : StrictFascisticMap n) : Set where
  constructor contractionDescent
  field
    depthBound : Nat
    descent :
      Σ (RTC.Carrier n)
        (λ fp → StrictFascisticMap.K M fp ≡ fp)

fixedPointFromDescent :
  ∀ {n} {M : StrictFascisticMap n} →
  ContractionDescent M →
  Σ (RTC.Carrier n)
    (λ fp → StrictFascisticMap.K M fp ≡ fp)
fixedPointFromDescent descent =
  ContractionDescent.descent descent
