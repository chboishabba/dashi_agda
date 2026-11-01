module Ontology.GodelScalarization where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

open import MonsterOntos using
  ( SSP; toNat
  ; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71
  )
open import Ontology.GodelLattice using (FactorVec; Vec15)
import Ontology.Hecke.FactorVecSignedTransport as SignedTransport

------------------------------------------------------------------------
-- Executable scalar Gödel map for the canonical SSP exponent lattice.
------------------------------------------------------------------------

pow : Nat → Nat → Nat
pow _ zero    = suc zero
pow b (suc n) = b * pow b n

primePower : SSP → Nat → Nat
primePower p e = pow (toNat p) e

G : FactorVec → Nat
G v =
  pow 2  (Vec15.e2  v) *
  (pow 3  (Vec15.e3  v) *
  (pow 5  (Vec15.e5  v) *
  (pow 7  (Vec15.e7  v) *
  (pow 11 (Vec15.e11 v) *
  (pow 13 (Vec15.e13 v) *
  (pow 17 (Vec15.e17 v) *
  (pow 19 (Vec15.e19 v) *
  (pow 23 (Vec15.e23 v) *
  (pow 29 (Vec15.e29 v) *
  (pow 31 (Vec15.e31 v) *
  (pow 41 (Vec15.e41 v) *
  (pow 47 (Vec15.e47 v) *
  (pow 59 (Vec15.e59 v) *
   pow 71 (Vec15.e71 v))))))))))))))

godelScalar : FactorVec → Nat
godelScalar = G

------------------------------------------------------------------------
-- Transport-compatible scalarization surface.
--
-- The law is stated in multiplication-only form:
--
--   p * G(target) = q * G(source)
--
-- so consumers never need division over Nat.  A concrete transport
-- implementation proves compatibility by producing ScalarTransportStep.
------------------------------------------------------------------------

record ScalarTransportStep (p q : SSP) (source : FactorVec) : Set₁ where
  constructor scalarTransportStep
  field
    target    : FactorVec
    Legal     : Set
    legal     : Legal
    scalarLaw : toNat p * G target ≡ toNat q * G source

open ScalarTransportStep public

transportScalarLaw :
  ∀ {p q source}
  → (step : ScalarTransportStep p q source)
  → toNat p * G (target step) ≡ toNat q * G source
transportScalarLaw step = scalarLaw step

signedTransferScalarStep :
  ∀ {p source target}
  → SignedTransport.transferPrime p source ≡ just target
  → toNat p * G target ≡ toNat (SignedTransport.nextPrime p) * G source
  → ScalarTransportStep p (SignedTransport.nextPrime p) source
signedTransferScalarStep {p} {source} {target} transferEq law =
  scalarTransportStep
    target
    (SignedTransport.transferPrime p source ≡ just target)
    transferEq
    law

record ScalarizationTheorem : Set₁ where
  field
    scalar              : FactorVec → Nat
    scalar-is-G         : ∀ v → scalar v ≡ G v
    transportCompatible :
      ∀ {p q source}
      → (step : ScalarTransportStep p q source)
      → toNat p * scalar (target step) ≡ toNat q * scalar source

open ScalarizationTheorem public

canonicalScalarizationTheorem : ScalarizationTheorem
canonicalScalarizationTheorem =
  record
    { scalar = G
    ; scalar-is-G = λ _ → refl
    ; transportCompatible = λ step → scalarLaw step
    }
