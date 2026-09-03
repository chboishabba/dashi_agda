{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation124GroupedCorrectionRound213Exact where

------------------------------------------------------------------------
-- ROUND213 BIDI: FIVE PRINTED EQ.(124) TERMS -> MAIN + GROUPED CORRECTION.
--
-- The existing Eq.(124) source owner stores five terms, whereas the executable
-- SU(2) linearized average is organized as
--
--       mainTerm + linearizedAverageCorrection.
--
-- These are not competing representations.  The source expression is
-- definitionally a main term plus the sum of its four correction terms.  Thus
-- the same-object audit needs only:
--
--   (1) executable main = printed transported-bond main;
--   (2) executable combined correction = sum of the four printed corrections.
--
-- This compiler turns those two equalities into the full Eq.(124) source
-- equality.  It therefore replaces a five-field termwise audit by the exact
-- two semantic seams actually induced by the executable decomposition.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanSU2CMP98Equation124 as Eq124

printedCorrection : Eq124.CMP98Equation124Terms → Lie.SU2LieAlgebra
printedCorrection terms =
  Lie.lieAdd (Eq124.minusBlockFaceCorrection terms)
    (Lie.lieAdd (Eq124.minusBlockBondCorrection terms)
      (Lie.lieAdd (Eq124.signedPlusBlockFaceCorrection terms)
        (Eq124.coarseBondCorrection terms)))

cmp98Equation124Grouped : ∀ terms →
  Eq124.cmp98Equation124 terms
  ≡ Lie.lieAdd (Eq124.transportedBondAverage terms) (printedCorrection terms)
cmp98Equation124Grouped terms = refl

record GroupedEquation124Implementation
    {Input : Set}
    (terms : Input → Eq124.CMP98Equation124Terms)
    : Set₁ where
  field
    executableMain executableCorrection : Input → Lie.SU2LieAlgebra
    implementation : Input → Lie.SU2LieAlgebra

    implementationIsMainPlusCorrection : ∀ input →
      implementation input
      ≡ Lie.lieAdd (executableMain input) (executableCorrection input)

    mainIsPrinted : ∀ input →
      executableMain input ≡ Eq124.transportedBondAverage (terms input)

    correctionIsPrinted : ∀ input →
      executableCorrection input ≡ printedCorrection (terms input)

open GroupedEquation124Implementation public

groupedImplementationIsEquation124 :
  ∀ {Input : Set}
    {terms : Input → Eq124.CMP98Equation124Terms}
    (dataSet : GroupedEquation124Implementation terms)
    input →
  implementation dataSet input ≡ Eq124.cmp98Equation124 (terms input)
groupedImplementationIsEquation124 {terms = terms} dataSet input =
  trans
    (implementationIsMainPlusCorrection dataSet input)
    (trans
      (cong₂ Lie.lieAdd
        (mainIsPrinted dataSet input)
        (correctionIsPrinted dataSet input))
      (symEq (cmp98Equation124Grouped (terms input))))
  where
    symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    symEq refl = refl

asEquation124Transcription :
  ∀ {Input : Set}
    {terms : Input → Eq124.CMP98Equation124Terms} →
  GroupedEquation124Implementation terms →
  Eq124.CMP98Equation124Transcription Input
asEquation124Transcription {terms = terms} dataSet = record
  { Eq124.CMP98Equation124Transcription.terms = terms
  ; Eq124.CMP98Equation124Transcription.implementation = implementation dataSet
  ; Eq124.CMP98Equation124Transcription.implementationTermDecomposition =
      groupedImplementationIsEquation124 dataSet
  }

cmp98Equation124GroupedCorrectionRound213Level : ProofLevel
cmp98Equation124GroupedCorrectionRound213Level = machineChecked

cmp98Equation124GroupedTranscriptionCompilerRound213Level : ProofLevel
cmp98Equation124GroupedTranscriptionCompilerRound213Level = machineChecked

-- The remaining literal source payment is now the grouped correction identity
-- on the actual SU(2) linearized-average inputs.  The main term already has its
-- own CMP98-(125) owner (`BalabanBlockedLinearAverageMainTerm`).
literalCMP98Equation124ExecutableCorrectionGroupingRound213Level : ProofLevel
literalCMP98Equation124ExecutableCorrectionGroupingRound213Level = conditional
