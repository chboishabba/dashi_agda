module DASHI.Crypto.MLKEMFIPS203SearchGeometryExact where

------------------------------------------------------------------------
-- FIPS 203 SEARCH-CARRIER GEOMETRY
--
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- The standard fixes n=256, q=3329 and parameter-dependent k, eta1, eta2,
-- du,dv.  K-PKE.KeyGen samples k secret polynomials and k error polynomials;
-- its public noisy system is t = A*s + e in the NTT domain.  This module turns
-- those source facts into exact finite search-carrier counts.  These counts are
-- not cryptographic work factors or security-strength claims.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

import DASHI.Crypto.MLKEMFIPS203SourceExact as FIPS

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc exponent) = base * pow base exponent

------------------------------------------------------------------------
-- Coefficient carrier sizes.
------------------------------------------------------------------------

secretCoefficientCount : FIPS.MLKEMParameters → Nat
secretCoefficientCount p = FIPS.n * FIPS.k p

errorCoefficientCount : FIPS.MLKEMParameters → Nat
errorCoefficientCount = secretCoefficientCount

publicVectorCoefficientCount : FIPS.MLKEMParameters → Nat
publicVectorCoefficientCount = secretCoefficientCount

publicMatrixPolynomialCount : FIPS.MLKEMParameters → Nat
publicMatrixPolynomialCount p = FIPS.k p * FIPS.k p

publicMatrixCoefficientCount : FIPS.MLKEMParameters → Nat
publicMatrixCoefficientCount p = FIPS.n * publicMatrixPolynomialCount p

secret512CoefficientCount : secretCoefficientCount FIPS.params512 ≡ 512
secret512CoefficientCount = refl

secret768CoefficientCount : secretCoefficientCount FIPS.params768 ≡ 768
secret768CoefficientCount = refl

secret1024CoefficientCount : secretCoefficientCount FIPS.params1024 ≡ 1024
secret1024CoefficientCount = refl

matrix512PolynomialCount : publicMatrixPolynomialCount FIPS.params512 ≡ 4
matrix512PolynomialCount = refl

matrix768PolynomialCount : publicMatrixPolynomialCount FIPS.params768 ≡ 9
matrix768PolynomialCount = refl

matrix1024PolynomialCount : publicMatrixPolynomialCount FIPS.params1024 ≡ 16
matrix1024PolynomialCount = refl

------------------------------------------------------------------------
-- CBD support carrier.
--
-- A SamplePolyCBD_eta coefficient lies in [-eta,eta], hence the finite support
-- alphabet has width 2*eta+1.  The product carrier below is an upper-level
-- support enumeration, not the probability distribution induced by PRF/CBD.
------------------------------------------------------------------------

secretCoefficientSupportWidth : FIPS.MLKEMParameters → Nat
secretCoefficientSupportWidth p = 2 * FIPS.eta1 p + 1

secret512SupportWidth : secretCoefficientSupportWidth FIPS.params512 ≡ 7
secret512SupportWidth = refl

secret768SupportWidth : secretCoefficientSupportWidth FIPS.params768 ≡ 5
secret768SupportWidth = refl

secret1024SupportWidth : secretCoefficientSupportWidth FIPS.params1024 ≡ 5
secret1024SupportWidth = refl

naiveSecretSupportCarrier : FIPS.MLKEMParameters → Nat
naiveSecretSupportCarrier p =
  pow (secretCoefficientSupportWidth p) (secretCoefficientCount p)

------------------------------------------------------------------------
-- Ciphertext coordinate geometry from K-PKE.Encrypt.
--
-- u has k polynomials compressed with du bits/coefficient; v has one polynomial
-- compressed with dv bits/coefficient.  Therefore the source-level bit count is
-- n*(du*k+dv), matching the standard byte formula 32*(du*k+dv).
------------------------------------------------------------------------

uCoefficientCount : FIPS.MLKEMParameters → Nat
uCoefficientCount p = FIPS.n * FIPS.k p

vCoefficientCount : FIPS.MLKEMParameters → Nat
vCoefficientCount p = FIPS.n

ciphertextBitCount : FIPS.MLKEMParameters → Nat
ciphertextBitCount p =
  FIPS.n * (FIPS.du p * FIPS.k p + FIPS.dv p)

ciphertext512Bits : ciphertextBitCount FIPS.params512 ≡ 6144
ciphertext512Bits = refl

ciphertext768Bits : ciphertextBitCount FIPS.params768 ≡ 8704
ciphertext768Bits = refl

ciphertext1024Bits : ciphertextBitCount FIPS.params1024 ≡ 12544
ciphertext1024Bits = refl

------------------------------------------------------------------------
-- Structural coupling audit.
--
-- At module-vector level every output row of A*s is a sum over k secret
-- polynomial coordinates.  This count is the source-level reconciliation seam:
-- treating the k secret polynomial lanes as independent search problems would
-- discard the matrix coupling that the public equation actually checks.
------------------------------------------------------------------------

termsPerPublicModuleEquation : FIPS.MLKEMParameters → Nat
termsPerPublicModuleEquation p = FIPS.k p

totalModuleProductsForPublicVector : FIPS.MLKEMParameters → Nat
totalModuleProductsForPublicVector p = FIPS.k p * FIPS.k p

moduleProducts512 : totalModuleProductsForPublicVector FIPS.params512 ≡ 4
moduleProducts512 = refl

moduleProducts768 : totalModuleProductsForPublicVector FIPS.params768 ≡ 9
moduleProducts768 = refl

moduleProducts1024 : totalModuleProductsForPublicVector FIPS.params1024 ≡ 16
moduleProducts1024 = refl

record SearchGeometryBoundary : Set where
  constructor searchGeometryBoundary
  field
    supportCarrierEqualsSecurityStrength : Bool
    supportCarrierEqualsSecurityStrengthIsFalse :
      supportCarrierEqualsSecurityStrength ≡ false
    nttCoordinatesProvedIndependentSearchLanes : Bool
    nttCoordinatesProvedIndependentSearchLanesIsFalse :
      nttCoordinatesProvedIndependentSearchLanes ≡ false
    matrixCouplingMustBeReconciled : Bool
    matrixCouplingMustBeReconciledIsTrue :
      matrixCouplingMustBeReconciled ≡ true

open SearchGeometryBoundary public

canonicalSearchGeometryBoundary : SearchGeometryBoundary
canonicalSearchGeometryBoundary =
  searchGeometryBoundary false refl false refl true refl
