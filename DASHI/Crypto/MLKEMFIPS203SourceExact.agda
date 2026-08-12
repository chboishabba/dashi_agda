module DASHI.Crypto.MLKEMFIPS203SourceExact where

------------------------------------------------------------------------
-- FIPS 203 SOURCE-FAITHFUL ML-KEM STATE SURFACE
--
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, published August 13, 2024.
-- DOI: 10.6028/NIST.FIPS.203.
--
-- This file formalises exact constants, sizes, algorithm-role boundaries and
-- implicit-rejection state selection directly from FIPS 203.  It is not a
-- byte-for-byte implementation of SHAKE/NTT/K-PKE/ML-KEM and makes no security
-- claim beyond the source-stated interface/requirement boundaries.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

------------------------------------------------------------------------
-- Global FIPS constants and approved parameter sets.
------------------------------------------------------------------------

n q : Nat
n = 256
q = 3329

data MLKEMParameterName : Set where
  mlKem512 mlKem768 mlKem1024 : MLKEMParameterName

record MLKEMParameters : Set where
  constructor mlkemParameters
  field
    name : MLKEMParameterName
    k eta1 eta2 du dv : Nat
    requiredRBGStrengthBits : Nat

open MLKEMParameters public

params512 : MLKEMParameters
params512 = mlkemParameters mlKem512 2 3 2 10 4 128

params768 : MLKEMParameters
params768 = mlkemParameters mlKem768 3 2 2 10 4 192

params1024 : MLKEMParameters
params1024 = mlkemParameters mlKem1024 4 2 2 11 5 256

encapsulationKeyBytes : MLKEMParameters → Nat
encapsulationKeyBytes p = 384 * k p + 32

decapsulationKeyBytes : MLKEMParameters → Nat
decapsulationKeyBytes p = 768 * k p + 96

ciphertextBytes : MLKEMParameters → Nat
ciphertextBytes p = 32 * (du p * k p + dv p)

params512EkBytes : encapsulationKeyBytes params512 ≡ 800
params512EkBytes = refl

params512DkBytes : decapsulationKeyBytes params512 ≡ 1632
params512DkBytes = refl

params512CiphertextBytes : ciphertextBytes params512 ≡ 768
params512CiphertextBytes = refl

params768EkBytes : encapsulationKeyBytes params768 ≡ 1184
params768EkBytes = refl

params768DkBytes : decapsulationKeyBytes params768 ≡ 2400
params768DkBytes = refl

params768CiphertextBytes : ciphertextBytes params768 ≡ 1088
params768CiphertextBytes = refl

params1024EkBytes : encapsulationKeyBytes params1024 ≡ 1568
params1024EkBytes = refl

params1024DkBytes : decapsulationKeyBytes params1024 ≡ 3168
params1024DkBytes = refl

params1024CiphertextBytes : ciphertextBytes params1024 ≡ 1568
params1024CiphertextBytes = refl

------------------------------------------------------------------------
-- Table-1 failure-rate labels represented as tenths of the exponent in
-- 2^(-x/10): 1388, 1648, 1748 correspond to 138.8, 164.8, 174.8.
------------------------------------------------------------------------

decapsulationFailureExponentTenths : MLKEMParameters → Nat
decapsulationFailureExponentTenths p with name p
... | mlKem512 = 1388
... | mlKem768 = 1648
... | mlKem1024 = 1748

failure512 : decapsulationFailureExponentTenths params512 ≡ 1388
failure512 = refl

failure768 : decapsulationFailureExponentTenths params768 ≡ 1648
failure768 = refl

failure1024 : decapsulationFailureExponentTenths params1024 ≡ 1748
failure1024 = refl

------------------------------------------------------------------------
-- Algorithm identities and state roles.
------------------------------------------------------------------------

data FIPS203Algorithm : Set where
  kPkeKeyGen kPkeEncrypt kPkeDecrypt
  mlKemKeyGenInternal mlKemEncapsInternal mlKemDecapsInternal
  mlKemKeyGen mlKemEncaps mlKemDecaps : FIPS203Algorithm

algorithm13IsKPKEKeyGen : FIPS203Algorithm
algorithm13IsKPKEKeyGen = kPkeKeyGen

algorithm14IsKPKEEncrypt : FIPS203Algorithm
algorithm14IsKPKEEncrypt = kPkeEncrypt

algorithm15IsKPKEDecrypt : FIPS203Algorithm
algorithm15IsKPKEDecrypt = kPkeDecrypt

algorithm16IsMLKEMKeyGenInternal : FIPS203Algorithm
algorithm16IsMLKEMKeyGenInternal = mlKemKeyGenInternal

algorithm17IsMLKEMEncapsInternal : FIPS203Algorithm
algorithm17IsMLKEMEncapsInternal = mlKemEncapsInternal

algorithm18IsMLKEMDecapsInternal : FIPS203Algorithm
algorithm18IsMLKEMDecapsInternal = mlKemDecapsInternal

------------------------------------------------------------------------
-- Algorithm-18 implicit rejection selection.
-- match=true corresponds to c == c'; match=false selects J(z || c).
------------------------------------------------------------------------

selectDecapsulationSecret : {SharedSecret : Set} →
  Bool → SharedSecret → SharedSecret → SharedSecret
selectDecapsulationSecret true candidate fallback = candidate
selectDecapsulationSecret false candidate fallback = fallback

matchingCiphertextKeepsCandidate :
  ∀ {SharedSecret : Set} candidate fallback →
  selectDecapsulationSecret {SharedSecret} true candidate fallback ≡ candidate
matchingCiphertextKeepsCandidate candidate fallback = refl

mismatchingCiphertextUsesFallback :
  ∀ {SharedSecret : Set} candidate fallback →
  selectDecapsulationSecret {SharedSecret} false candidate fallback ≡ fallback
mismatchingCiphertextUsesFallback candidate fallback = refl

------------------------------------------------------------------------
-- Source requirements stated explicitly in FIPS 203 Sections 3.3 and 7.
------------------------------------------------------------------------

record FIPS203BlueTeamBoundary : Set where
  constructor fips203BlueTeamBoundary
  field
    kPKEApprovedStandalone : Bool
    kPKEApprovedStandaloneIsFalse : kPKEApprovedStandalone ≡ false
    internalInterfacesApplicationFacing : Bool
    internalInterfacesApplicationFacingIsFalse :
      internalInterfacesApplicationFacing ≡ false
    implicitRejectFlagMayBeReturned : Bool
    implicitRejectFlagMayBeReturnedIsFalse :
      implicitRejectFlagMayBeReturned ≡ false
    ciphertextCheckedEveryDecapsulation : Bool
    ciphertextCheckedEveryDecapsulationIsTrue :
      ciphertextCheckedEveryDecapsulation ≡ true
    encapsulationKeyIsPublic : Bool
    encapsulationKeyIsPublicIsTrue : encapsulationKeyIsPublic ≡ true
    decapsulationKeyIsPrivate : Bool
    decapsulationKeyIsPrivateIsTrue : decapsulationKeyIsPrivate ≡ true
    conformanceImpliesSecureImplementation : Bool
    conformanceImpliesSecureImplementationIsFalse :
      conformanceImpliesSecureImplementation ≡ false

open FIPS203BlueTeamBoundary public

canonicalFIPS203BlueTeamBoundary : FIPS203BlueTeamBoundary
canonicalFIPS203BlueTeamBoundary =
  fips203BlueTeamBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
