module DASHI.Moonshine.OggSSPMonster3BSymplecticCompressionFieldSelectorExact where

------------------------------------------------------------------------
-- MONSTER-3B SYMPLECTIC-12 -> K6 COMPRESSION FIELD SELECTOR
--
-- PR #1098 has located a certified 12-dimensional GF(3) symplectic source for
-- the Monster-3B normalizer and typed the same-basis weld to the repository
-- carrier
--
--     Symplectic12 = X6 + X6*.
--
-- The previous positive route on this branch required a selected source word
-- to stabilise the chosen translation Lagrangian X6 before it could induce an
-- X6 -> X6 operator.  That requirement is stronger than the actual K6 field-
-- selector contract.
--
-- For ANY F3-linear source action g on the same welded Symplectic12 carrier,
-- the canonical compression
--
--     A_g = pi_X o g o iota_X
--
-- is already an F3-linear endomorphism X6 -> X6, where
--
--     iota_X(x) = (x,0),    pi_X(x,xi) = x.
--
-- Therefore field selection does not require X6 to be g-invariant.  After the
-- concrete ATLAS matrices + symplectic basis change are imported, every source
-- generator/word can be screened directly through its translation block A_g.
-- If one such block breaks swap01 and carries an independently checked degree-6
-- field-generator receipt, it compiles immediately to the existing
-- K6FieldSelectingOperator.
--
-- This does NOT identify the source module with X6 by dimension/cardinality,
-- and it does NOT claim that the compressed block is itself a group action.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.OggSSPHeisenbergSymplecticFieldNoGoExact as NoGo
import DASHI.Moonshine.OggSSPK6FieldSelectingOperatorExact as K6

------------------------------------------------------------------------
-- 1. Standard inclusion/projection for the repository polarization.
------------------------------------------------------------------------

embedTranslation : G.X6 → H.Symplectic12
embedTranslation x = H.symplectic12 x H.zeroX6

projectTranslation : H.Symplectic12 → G.X6
projectTranslation = H.translationPart

addSymplectic12 : H.Symplectic12 → H.Symplectic12 → H.Symplectic12
addSymplectic12 left right =
  H.symplectic12
    (H.addX6 (H.translationPart left) (H.translationPart right))
    (H.addX6 (H.modulationPart left) (H.modulationPart right))

negSymplectic12 : H.Symplectic12 → H.Symplectic12
negSymplectic12 value =
  H.symplectic12
    (H.negX6 (H.translationPart value))
    (H.negX6 (H.modulationPart value))

embedTranslationPreservesAdd :
  (x y : G.X6) →
  embedTranslation (H.addX6 x y)
  ≡ addSymplectic12 (embedTranslation x) (embedTranslation y)
embedTranslationPreservesAdd x y = refl

embedTranslationPreservesNeg :
  (x : G.X6) →
  embedTranslation (H.negX6 x)
  ≡ negSymplectic12 (embedTranslation x)
embedTranslationPreservesNeg x = refl

------------------------------------------------------------------------
-- 2. Minimal same-basis source action needed by the compression compiler.
------------------------------------------------------------------------

record SameBasisSymplecticLinearAction : Set where
  field
    act : H.Symplectic12 → H.Symplectic12
    preservesAdd12 :
      (left right : H.Symplectic12) →
      act (addSymplectic12 left right)
      ≡ addSymplectic12 (act left) (act right)
    preservesNeg12 :
      (value : H.Symplectic12) →
      act (negSymplectic12 value)
      ≡ negSymplectic12 (act value)
open SameBasisSymplecticLinearAction public

compression : SameBasisSymplecticLinearAction → G.X6 → G.X6
compression source x = projectTranslation (act source (embedTranslation x))

compressionPreservesAdd :
  (source : SameBasisSymplecticLinearAction) →
  (x y : G.X6) →
  compression source (H.addX6 x y)
  ≡ H.addX6 (compression source x) (compression source y)
compressionPreservesAdd source x y
  rewrite embedTranslationPreservesAdd x y
        | preservesAdd12 source (embedTranslation x) (embedTranslation y)
  = refl

compressionPreservesNeg :
  (source : SameBasisSymplecticLinearAction) →
  (x : G.X6) →
  compression source (H.negX6 x)
  ≡ H.negX6 (compression source x)
compressionPreservesNeg source x
  rewrite embedTranslationPreservesNeg x
        | preservesNeg12 source (embedTranslation x)
  = refl

------------------------------------------------------------------------
-- 3. The exact additional receipts needed to promote one compression block to
--    the existing K6 field-selector contract.
------------------------------------------------------------------------

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record CompressionFieldGeneratorReceipt
    (source : SameBasisSymplecticLinearAction) : Set₁ where
  field
    swapBreakingWitness : G.X6
    breaksSwap01AtWitness :
      compression source (NoGo.swap01X6 swapBreakingWitness)
      ≢ NoGo.swap01X6 (compression source swapBreakingWitness)

    minimalPolynomialDegree : Nat
    minimalPolynomialDegreeIsSix : minimalPolynomialDegree ≡ 6

    cyclicSpanDimension : Nat
    cyclicSpanDimensionIsSix : cyclicSpanDimension ≡ 6

    FieldGeneratorReceipt : Set
    fieldGeneratorReceipt : FieldGeneratorReceipt
open CompressionFieldGeneratorReceipt public

compileCompressionToK6FieldSelector :
  (source : SameBasisSymplecticLinearAction) →
  CompressionFieldGeneratorReceipt source →
  K6.K6FieldSelectingOperator
compileCompressionToK6FieldSelector source receipt = record
  { operator = compression source
  ; preservesAdd = compressionPreservesAdd source
  ; preservesNeg = compressionPreservesNeg source
  ; swapBreakingWitness = swapBreakingWitness receipt
  ; breaksSwap01AtWitness = breaksSwap01AtWitness receipt
  ; minimalPolynomialDegree = minimalPolynomialDegree receipt
  ; minimalPolynomialDegreeIsSix = minimalPolynomialDegreeIsSix receipt
  ; cyclicSpanDimension = cyclicSpanDimension receipt
  ; cyclicSpanDimensionIsSix = cyclicSpanDimensionIsSix receipt
  ; FieldGeneratorReceipt = FieldGeneratorReceipt receipt
  ; fieldGeneratorReceipt = fieldGeneratorReceipt receipt
  }

------------------------------------------------------------------------
-- 4. Max-cut consequence.
------------------------------------------------------------------------

record SymplecticCompressionFieldSelectorBoundary : Set where
  constructor symplectic-compression-field-selector-boundary
  field
    sourceSymplectic12LocatedOn1098 : Bool
    sameBasisWeldStillRequiresConcreteMatrices : Bool
    wholeNormalizerX6InvariantSubmoduleRequired : Bool
    lagrangianStabilizerRequiredForFieldSelector : Bool
    everySameBasisLinearSourceActionHasX6Compression : Bool
    compressionLinearityPaidGenerically : Bool
    degreeSixPolynomialReceiptStillConcrete : Bool
    swapBreakingReceiptStillConcrete : Bool
    selectedCompressionCompilesToK6Selector : Bool

open SymplecticCompressionFieldSelectorBoundary public

canonicalSymplecticCompressionFieldSelectorBoundary :
  SymplecticCompressionFieldSelectorBoundary
canonicalSymplecticCompressionFieldSelectorBoundary =
  symplectic-compression-field-selector-boundary
    true
    true
    false
    false
    true
    true
    true
    true
    true
