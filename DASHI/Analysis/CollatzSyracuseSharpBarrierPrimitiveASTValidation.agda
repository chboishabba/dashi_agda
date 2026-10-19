module DASHI.Analysis.CollatzSyracuseSharpBarrierPrimitiveASTValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseSharpBarrierPrimitiveASTExact as AST

syntaxPaid :
  AST.PrimitiveASTBoundary.typedPrimitiveASTPaid
    AST.canonicalPrimitiveASTBoundary
  ≡ 1
syntaxPaid = refl

certifiedPathPaid :
  AST.PrimitiveASTBoundary.certifiedPathCarriesAllInvariants
    AST.canonicalPrimitiveASTBoundary
  ≡ 1
certifiedPathPaid = refl

openLemmaIsSingleLeaf :
  AST.PrimitiveASTBoundary.universalBarrierEscapeProducerPaid
    AST.canonicalPrimitiveASTBoundary
  ≡ 0
openLemmaIsSingleLeaf = refl

noLocalPromotion :
  AST.PrimitiveASTBoundary.localMonotonicityPromotedToUniversalEscape
    AST.canonicalPrimitiveASTBoundary
  ≡ 0
noLocalPromotion = refl
