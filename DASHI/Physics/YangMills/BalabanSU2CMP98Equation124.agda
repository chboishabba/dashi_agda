module DASHI.Physics.YangMills.BalabanSU2CMP98Equation124 where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong₂)

open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; lieAdd)

record CMP98Equation124Terms : Set where
  constructor equation124Terms
  field
    transportedBondAverage : SU2LieAlgebra
    minusBlockFaceCorrection : SU2LieAlgebra
    minusBlockBondCorrection : SU2LieAlgebra
    signedPlusBlockFaceCorrection : SU2LieAlgebra
    coarseBondCorrection : SU2LieAlgebra
open CMP98Equation124Terms public

cmp98Equation124 : CMP98Equation124Terms → SU2LieAlgebra
cmp98Equation124 terms =
  lieAdd (transportedBondAverage terms)
    (lieAdd (minusBlockFaceCorrection terms)
      (lieAdd (minusBlockBondCorrection terms)
        (lieAdd (signedPlusBlockFaceCorrection terms)
          (coarseBondCorrection terms))))

record CMP98Equation124Transcription
  {i : Level}
  (Input : Set i) : Set (lsuc i) where
  field
    terms : Input → CMP98Equation124Terms
    implementation : Input → SU2LieAlgebra
    implementationTermDecomposition :
      ∀ input → implementation input ≡ cmp98Equation124 (terms input)
open CMP98Equation124Transcription public

cmp98LinearizationSourceExact :
  ∀ {i} {Input : Set i}
  (transcription : CMP98Equation124Transcription Input) →
  ∀ input →
  implementation transcription input
    ≡ cmp98Equation124 (terms transcription input)
cmp98LinearizationSourceExact transcription =
  implementationTermDecomposition transcription

record Equation124TermwiseAudit
  {i : Level}
  (Input : Set i)
  (left right : Input → CMP98Equation124Terms) : Set (lsuc i) where
  field
    transportedBondAverageExact : ∀ input →
      transportedBondAverage (left input)
        ≡ transportedBondAverage (right input)
    minusBlockFaceCorrectionExact : ∀ input →
      minusBlockFaceCorrection (left input)
        ≡ minusBlockFaceCorrection (right input)
    minusBlockBondCorrectionExact : ∀ input →
      minusBlockBondCorrection (left input)
        ≡ minusBlockBondCorrection (right input)
    signedPlusBlockFaceCorrectionExact : ∀ input →
      signedPlusBlockFaceCorrection (left input)
        ≡ signedPlusBlockFaceCorrection (right input)
    coarseBondCorrectionExact : ∀ input →
      coarseBondCorrection (left input)
        ≡ coarseBondCorrection (right input)
open Equation124TermwiseAudit public

termwiseAuditClosesEquation124 :
  ∀ {i} {Input : Set i}
  {left right : Input → CMP98Equation124Terms} →
  Equation124TermwiseAudit Input left right →
  ∀ input → cmp98Equation124 (left input) ≡ cmp98Equation124 (right input)
termwiseAuditClosesEquation124 audit input =
  cong₂ lieAdd
    (transportedBondAverageExact audit input)
    (cong₂ lieAdd
      (minusBlockFaceCorrectionExact audit input)
      (cong₂ lieAdd
        (minusBlockBondCorrectionExact audit input)
        (cong₂ lieAdd
          (signedPlusBlockFaceCorrectionExact audit input)
          (coarseBondCorrectionExact audit input))))
