module DASHI.Physics.Closure.SSPPrimeLane369ResidueFactorBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₂)
open import Ontology.GodelLattice using (Vec15)

open import Base369 using (TriTruth; tri-low; tri-mid; tri-high; NonaryTruth; non-1; non-2; non-7; non-8)

open import DASHI.Foundations.Base369MobiusTransport using (positive; negative)
open import DASHI.Foundations.HexTruthPolarityFactor as HexFactor using
  (Polarity; hexTruthToFactor)
open import DASHI.Foundations.SSPPrimeLane369Signature as Signature using
  (Prime369Signature; prime369Signature)
open import DASHI.TrackedPrimes using (mapTrackedPrimes15)
open import MonsterOntos using (SSP; p7; p11; p19; p71)

ResidueFactor : Set
ResidueFactor = TriTruth × Polarity × NonaryTruth

record SSPPrimeLane369ResidueFactorBridge : Set where
  constructor mkSSPPrimeLane369ResidueFactorBridge
  field
    primeIdentity : SSP
    residueSignature : Prime369Signature
    residueSignatureMatchesPrimeIdentity :
      Signature.prime residueSignature ≡ primeIdentity
    residueFactor : ResidueFactor
    residueFactorMatchesSignature :
      residueFactor ≡
      ( Signature.triResidue residueSignature
      , proj₂ (hexTruthToFactor (Signature.hexResidue residueSignature))
      , Signature.nonaryResidue residueSignature
      )

open SSPPrimeLane369ResidueFactorBridge public

primeLane369ResidueFactorBridge : SSP → SSPPrimeLane369ResidueFactorBridge
primeLane369ResidueFactorBridge p = record
  { primeIdentity = p
  ; residueSignature = signature
  ; residueSignatureMatchesPrimeIdentity = refl
  ; residueFactor =
      Signature.triResidue signature
      , proj₂ (hexTruthToFactor (Signature.hexResidue signature))
      , Signature.nonaryResidue signature
  ; residueFactorMatchesSignature = refl
  }
  where
    signature : Prime369Signature
    signature = prime369Signature p

canonicalSSPPrimeLane369ResidueFactorVec15 : Vec15 SSPPrimeLane369ResidueFactorBridge
canonicalSSPPrimeLane369ResidueFactorVec15 =
  mapTrackedPrimes15 primeLane369ResidueFactorBridge

p7SSPPrimeLane369ResidueFactorBridge : SSPPrimeLane369ResidueFactorBridge
p7SSPPrimeLane369ResidueFactorBridge = primeLane369ResidueFactorBridge p7

p11SSPPrimeLane369ResidueFactorBridge : SSPPrimeLane369ResidueFactorBridge
p11SSPPrimeLane369ResidueFactorBridge = primeLane369ResidueFactorBridge p11

p19SSPPrimeLane369ResidueFactorBridge : SSPPrimeLane369ResidueFactorBridge
p19SSPPrimeLane369ResidueFactorBridge = primeLane369ResidueFactorBridge p19

p71SSPPrimeLane369ResidueFactorBridge : SSPPrimeLane369ResidueFactorBridge
p71SSPPrimeLane369ResidueFactorBridge = primeLane369ResidueFactorBridge p71

p7ResidueFactorIsCanonical :
  residueFactor p7SSPPrimeLane369ResidueFactorBridge ≡
  (tri-mid , positive , non-7)
p7ResidueFactorIsCanonical = refl

p11ResidueFactorIsCanonical :
  residueFactor p11SSPPrimeLane369ResidueFactorBridge ≡
  (tri-high , negative , non-2)
p11ResidueFactorIsCanonical = refl

p19ResidueFactorIsCanonical :
  residueFactor p19SSPPrimeLane369ResidueFactorBridge ≡
  (tri-mid , positive , non-1)
p19ResidueFactorIsCanonical = refl

p71ResidueFactorIsCanonical :
  residueFactor p71SSPPrimeLane369ResidueFactorBridge ≡
  (tri-high , negative , non-8)
p71ResidueFactorIsCanonical = refl
