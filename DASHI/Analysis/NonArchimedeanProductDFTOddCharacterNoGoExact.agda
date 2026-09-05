module DASHI.Analysis.NonArchimedeanProductDFTOddCharacterNoGoExact where

------------------------------------------------------------------------
-- PRODUCT-DFT / ODD-CHARACTER NO-GO
--
-- F_m tensor I_2 is cross-fibre sparse: entries with unequal I_2 coordinates
-- are zero.  The genuine odd-character Fourier kernel omega^((2j+1)v) is a
-- root-of-unity value at every entry and therefore nonzero.
--
-- Thus, once one exhibits one cross-fibre entry, the two matrices cannot be
-- literally equal under the stated product indexing.  This is stronger than
-- merely saying that source code has not proved the semantic identification.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

data Empty : Set where

record SparseDenseWitness : Set₁ where
  field
    Row Col Scalar : Set
    zero : Scalar

    productDFT : Row → Col → Scalar
    oddCharacterDFT : Row → Col → Scalar

    crossRow : Row
    crossCol : Col

    productCrossEntryZero :
      productDFT crossRow crossCol ≡ zero

    oddCharacterCrossEntryNonzero :
      oddCharacterDFT crossRow crossCol ≡ zero → Empty

open SparseDenseWitness public

productDFTCannotEqualOddCharacterDFT :
  (witness : SparseDenseWitness) →
  productDFT witness ≡ oddCharacterDFT witness → Empty
productDFTCannotEqualOddCharacterDFT witness matrixEquality =
  oddCharacterCrossEntryNonzero witness
    (let
      entryEquality :
        productDFT witness (crossRow witness) (crossCol witness)
        ≡ oddCharacterDFT witness (crossRow witness) (crossCol witness)
      entryEquality =
        cong
          (λ matrix → matrix (crossRow witness) (crossCol witness))
          matrixEquality
    in
      let
        -- productEntry = zero and productEntry = oddEntry imply oddEntry = zero
        open import Relation.Binary.PropositionalEquality using (sym; trans)
      in
      trans
        (sym entryEquality)
        (productCrossEntryZero witness))

record SourceProductDFTNoGoStatus : Set where
  constructor sourceProductDFTNoGoStatus
  field
    productDFTHasIdentityFactor : Bool
    crossIdentityFibresGiveStructuralZeros : Bool
    oddCharacterKernelEntriesAreRootsOfUnity : Bool
    oddCharacterKernelEntriesAreNonzero : Bool
    literalEqualityCanBeRejectedByOneEntryWitness : Bool
    sourceProductDFTMayServeAsOddCharacterDFTWithoutAnotherRechart : Bool

canonicalSourceProductDFTNoGoStatus : SourceProductDFTNoGoStatus
canonicalSourceProductDFTNoGoStatus =
  sourceProductDFTNoGoStatus true true true true true false

productDFTIsWrongLiteralCandidate :
  SourceProductDFTNoGoStatus.sourceProductDFTMayServeAsOddCharacterDFTWithoutAnotherRechart
    canonicalSourceProductDFTNoGoStatus
  ≡ false
productDFTIsWrongLiteralCandidate = refl
