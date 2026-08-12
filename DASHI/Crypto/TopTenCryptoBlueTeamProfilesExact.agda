module DASHI.Crypto.TopTenCryptoBlueTeamProfilesExact where

------------------------------------------------------------------------
-- TEN REPRESENTATIVE CRYPTOGRAPHIC CANDIDATES: TYPED BLUE-TEAM PROFILES
--
-- This is the educational comparison used in the DASHI thread.  It is not a
-- claim that these are objectively the world's "top ten encryption algorithms".
-- In particular DH/X25519 are key agreement, HPKE is a composition, ML-KEM is
-- a KEM, and QKD is key distribution.
--
-- Primary references / provenance:
-- Claude E. Shannon, "Communication Theory of Secrecy Systems", BSTJ 28(4),
-- 1949. DOI: 10.1002/j.1538-7305.1949.tb00928.x.
--
-- NIST, "Advanced Encryption Standard (AES)", FIPS 197-upd1, 2023.
-- DOI: 10.6028/NIST.FIPS.197-upd1.
-- Morris Dworkin, NIST SP 800-38D, GCM/GMAC.
-- DOI: 10.6028/NIST.SP.800-38D.
--
-- Yoav Nir and Adam Langley, RFC 8439, "ChaCha20 and Poly1305 for IETF
-- Protocols". DOI: 10.17487/RFC8439.
--
-- Kathleen Moriarty, Burt Kaliski, Jakob Jonsson, Andreas Rusch,
-- RFC 8017, "PKCS #1: RSA Cryptography Specifications Version 2.2".
-- DOI: 10.17487/RFC8017.
--
-- Whitfield Diffie and Martin E. Hellman, "New Directions in Cryptography",
-- IEEE Trans. Inf. Theory 22(6), 1976. DOI: 10.1109/TIT.1976.1055638.
--
-- Adam Langley, Mike Hamburg, Sean Turner, RFC 7748, "Elliptic Curves for
-- Security". DOI: 10.17487/RFC7748.  The X25519 profile below follows RFC
-- 7748's special input semantics and therefore tracks all-zero shared-secret
-- handling rather than importing generic Weierstrass-point validation rules.
--
-- Taher ElGamal, "A Public Key Cryptosystem and a Signature Scheme Based on
-- Discrete Logarithms", IEEE Trans. Inf. Theory 31(4), 1985.
-- DOI: 10.1109/TIT.1985.1057074.
--
-- Richard Barnes, Karthikeyan Bhargavan, Benjamin Lipp, Christopher A. Wood,
-- RFC 9180, "Hybrid Public Key Encryption". DOI: 10.17487/RFC9180.
--
-- NIST et al., FIPS 203, "Module-Lattice-Based Key-Encapsulation Mechanism
-- Standard", 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Artur K. Ekert, "Quantum cryptography based on Bell's theorem",
-- Phys. Rev. Lett. 67 (1991). DOI: 10.1103/PhysRevLett.67.661.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)

------------------------------------------------------------------------
-- Primitive kinds prevent category errors.
------------------------------------------------------------------------

data PrimitiveKind : Set where
  informationTheoreticEncryption
  symmetricAEAD
  trapdoorPublicKeyEncryption
  finiteGroupKeyAgreement
  ellipticCurveKeyAgreement
  randomizedPublicKeyEncryption
  hybridPublicKeyEncryption
  postQuantumKEM
  quantumKeyDistribution : PrimitiveKind

data CryptoCandidate : Set where
  oneTimePad
  aesGcm
  chacha20Poly1305
  rsaOaep
  diffieHellman
  x25519
  elGamal
  hpke
  mlKem
  qkdWithSymmetric : CryptoCandidate

allTen : List CryptoCandidate
allTen =
  oneTimePad ∷ aesGcm ∷ chacha20Poly1305 ∷ rsaOaep ∷
  diffieHellman ∷ x25519 ∷ elGamal ∷ hpke ∷ mlKem ∷
  qkdWithSymmetric ∷ []

allTenCount : length allTen ≡ 10
allTenCount = refl

kind : CryptoCandidate → PrimitiveKind
kind oneTimePad = informationTheoreticEncryption
kind aesGcm = symmetricAEAD
kind chacha20Poly1305 = symmetricAEAD
kind rsaOaep = trapdoorPublicKeyEncryption
kind diffieHellman = finiteGroupKeyAgreement
kind x25519 = ellipticCurveKeyAgreement
kind elGamal = randomizedPublicKeyEncryption
kind hpke = hybridPublicKeyEncryption
kind mlKem = postQuantumKEM
kind qkdWithSymmetric = quantumKeyDistribution

------------------------------------------------------------------------
-- Structural attack surfaces.  These name proof obligations / falsification
-- targets, not claims that the corresponding standardized primitive is broken.
------------------------------------------------------------------------

data AttackSurface : Set where
  padReuse
  nonceReuseUnderKey
  weakKeyEntropy
  publicInverseShortcut
  paddingOrValidityOracle
  discreteLogShortcut
  publicElementValidation
  allZeroSharedSecretOutcome
  ephemeralReuse
  componentKEMFailure
  componentKDFFailure
  componentAEADFailure
  contextBindingFailure
  moduleLWEResidualSearch
  publicSecretFactorisation
  implicitRejectVisibility
  unauthenticatedClassicalChannel
  quantumParameterTestFailure
  followOnSymmetricFailure
  computationalModelShift : AttackSurface

record BlueTeamProfile : Set where
  constructor blueTeamProfile
  field
    candidate : CryptoCandidate
    primitiveKind : PrimitiveKind
    kindCorrect : primitiveKind ≡ kind candidate
    directEncryptionPrimitive : Bool
    attackSurfaces : List AttackSurface

open BlueTeamProfile public

otpProfile : BlueTeamProfile
otpProfile = blueTeamProfile oneTimePad informationTheoreticEncryption refl true
  (padReuse ∷ weakKeyEntropy ∷ [])

aesGcmProfile : BlueTeamProfile
aesGcmProfile = blueTeamProfile aesGcm symmetricAEAD refl true
  (nonceReuseUnderKey ∷ weakKeyEntropy ∷ contextBindingFailure ∷ [])

chacha20Poly1305Profile : BlueTeamProfile
chacha20Poly1305Profile =
  blueTeamProfile chacha20Poly1305 symmetricAEAD refl true
    (nonceReuseUnderKey ∷ weakKeyEntropy ∷ contextBindingFailure ∷ [])

rsaOaepProfile : BlueTeamProfile
rsaOaepProfile =
  blueTeamProfile rsaOaep trapdoorPublicKeyEncryption refl true
    (publicInverseShortcut ∷ paddingOrValidityOracle ∷
     computationalModelShift ∷ [])

diffieHellmanProfile : BlueTeamProfile
diffieHellmanProfile =
  blueTeamProfile diffieHellman finiteGroupKeyAgreement refl false
    (discreteLogShortcut ∷ publicElementValidation ∷ ephemeralReuse ∷
     computationalModelShift ∷ [])

x25519Profile : BlueTeamProfile
x25519Profile =
  blueTeamProfile x25519 ellipticCurveKeyAgreement refl false
    (discreteLogShortcut ∷ allZeroSharedSecretOutcome ∷ ephemeralReuse ∷
     contextBindingFailure ∷ computationalModelShift ∷ [])

elGamalProfile : BlueTeamProfile
elGamalProfile =
  blueTeamProfile elGamal randomizedPublicKeyEncryption refl true
    (discreteLogShortcut ∷ ephemeralReuse ∷ publicElementValidation ∷
     computationalModelShift ∷ [])

hpkeProfile : BlueTeamProfile
hpkeProfile =
  blueTeamProfile hpke hybridPublicKeyEncryption refl true
    (componentKEMFailure ∷ componentKDFFailure ∷ componentAEADFailure ∷
     contextBindingFailure ∷ [])

mlKemProfile : BlueTeamProfile
mlKemProfile =
  blueTeamProfile mlKem postQuantumKEM refl false
    (moduleLWEResidualSearch ∷ publicSecretFactorisation ∷
     implicitRejectVisibility ∷ computationalModelShift ∷ [])

qkdWithSymmetricProfile : BlueTeamProfile
qkdWithSymmetricProfile =
  blueTeamProfile qkdWithSymmetric quantumKeyDistribution refl false
    (unauthenticatedClassicalChannel ∷ quantumParameterTestFailure ∷
     followOnSymmetricFailure ∷ contextBindingFailure ∷ [])

allProfiles : List BlueTeamProfile
allProfiles =
  otpProfile ∷ aesGcmProfile ∷ chacha20Poly1305Profile ∷
  rsaOaepProfile ∷ diffieHellmanProfile ∷ x25519Profile ∷
  elGamalProfile ∷ hpkeProfile ∷ mlKemProfile ∷
  qkdWithSymmetricProfile ∷ []

allProfilesCount : length allProfiles ≡ 10
allProfilesCount = refl

-- Explicit category regressions.
mlKemIsKEMNotDirectEncryption : directEncryptionPrimitive mlKemProfile ≡ false
mlKemIsKEMNotDirectEncryption = refl

qkdIsDistributionNotDirectEncryption :
  directEncryptionPrimitive qkdWithSymmetricProfile ≡ false
qkdIsDistributionNotDirectEncryption = refl

dhIsAgreementNotDirectEncryption :
  directEncryptionPrimitive diffieHellmanProfile ≡ false
dhIsAgreementNotDirectEncryption = refl
