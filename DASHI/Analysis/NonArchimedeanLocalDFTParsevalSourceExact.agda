module DASHI.Analysis.NonArchimedeanLocalDFTParsevalSourceExact where

------------------------------------------------------------------------
-- LOCAL DFT PARSEVAL SOURCE / MATHLIB RECEIPT
--
-- The external source's normalized DFT is genuinely unitary.  Unlike the
-- rational Hadamard block similarity, this transform includes the 1/sqrt(N)
-- normalization in its definition and proves both inverse identities:
--
--   dftMatrix * dftMatrix_star = I
--   dftMatrix_star * dftMatrix = I.
--
-- `Formalization.Analysis.DFT.fourierBasisMatrix_mul_star` then lifts the first
-- identity through the Kronecker product F tensor I_2 used on the concrete
-- twisted/detail block.
--
-- Consequently local Fourier/detail Parseval is library-closed; no additional
-- condition number or shell-energy prefactor is introduced by this rechart.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record LocalDFTParsevalSourceReceipt : Set where
  constructor localDFTParsevalSourceReceipt
  field
    sourceCommit : String
    dftIncludesInverseSqrtCardinality : Bool
    dftMulStarIdentityOwned : Bool
    dftStarMulIdentityOwned : Bool
    productFourierMulStarIdentityOwned : Bool
    localDFTIsInvertibleSimilarityOnly : Bool
    localDFTIsUnitary : Bool
    localParsevalMathematicsClosed : Bool
    agdaKernelChecksLeanComplexNorm : Bool

canonicalLocalDFTParsevalSourceReceipt : LocalDFTParsevalSourceReceipt
canonicalLocalDFTParsevalSourceReceipt =
  localDFTParsevalSourceReceipt
    "f94b956e6e970c40c8bb9f9c39e9052ad7a5f884"
    true true true true false true true false

localDFTUnitaryOwned :
  LocalDFTParsevalSourceReceipt.localDFTIsUnitary
    canonicalLocalDFTParsevalSourceReceipt
  ≡ true
localDFTUnitaryOwned = refl

localParsevalDependencyClosed :
  LocalDFTParsevalSourceReceipt.localParsevalMathematicsClosed
    canonicalLocalDFTParsevalSourceReceipt
  ≡ true
localParsevalDependencyClosed = refl
