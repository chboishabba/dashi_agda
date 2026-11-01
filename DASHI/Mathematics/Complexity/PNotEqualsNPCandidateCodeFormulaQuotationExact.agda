module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCodeFormulaQuotationExact where

------------------------------------------------------------------------
-- FIXED-WIDTH CANDIDATE CODE -> INJECTIVE COOK-FORMULA QUOTATION
--
-- Existing ProgramDescriptionFormulaEmbeddingExact embeds a fixed-width bit
-- vector as a tautological Boolean formula:
--
--   true  -> true OR false
--   false -> false OR true
--
-- chained by conjunction.
--
-- This owner proves that quotation is syntactically injective and lifts any
-- ordinary fixed-width candidate-code codec into an injective Cook-formula
-- quotation.  This is pure representation adequacy: no SAT semantics or
-- lower-bound statement is involved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Quote

------------------------------------------------------------------------
-- Constructor injectivity helpers for Cook.BooleanFormula.
------------------------------------------------------------------------

conjunctionLeftInjective :
  ∀ {left₁ right₁ left₂ right₂ : Cook.BooleanFormula} →
  Cook.conjunction left₁ right₁
  ≡
  Cook.conjunction left₂ right₂ →
  left₁ ≡ left₂
conjunctionLeftInjective refl =
  refl

conjunctionRightInjective :
  ∀ {left₁ right₁ left₂ right₂ : Cook.BooleanFormula} →
  Cook.conjunction left₁ right₁
  ≡
  Cook.conjunction left₂ right₂ →
  right₁ ≡ right₂
conjunctionRightInjective refl =
  refl

------------------------------------------------------------------------
-- Bit-token injectivity.
------------------------------------------------------------------------

bitTokenInjective :
  ∀ {left right : Bool} →
  Quote.bitToken left ≡ Quote.bitToken right →
  left ≡ right
bitTokenInjective {false} {false} equality =
  refl
bitTokenInjective {false} {true} ()
bitTokenInjective {true} {false} ()
bitTokenInjective {true} {true} equality =
  refl

------------------------------------------------------------------------
-- Whole fixed-width quotation injectivity.
------------------------------------------------------------------------

embedBitsAsTautologyInjective :
  ∀ {width : Nat}
    {left right : CNF.Bits width} →
  Quote.embedBitsAsTautology left
  ≡
  Quote.embedBitsAsTautology right →
  left ≡ right
embedBitsAsTautologyInjective
    {left = CNF.[]ᵇ}
    {right = CNF.[]ᵇ}
    equality =
  refl
embedBitsAsTautologyInjective
    {left = leftBit CNF.∷ᵇ leftRest}
    {right = rightBit CNF.∷ᵇ rightRest}
    equality
    with
      bitTokenInjective
        (conjunctionLeftInjective equality)
... | refl
    with
      embedBitsAsTautologyInjective
        (conjunctionRightInjective equality)
... | refl =
  refl

------------------------------------------------------------------------
-- Generic fixed-width code codec.
------------------------------------------------------------------------

record FixedWidthCandidateCodeCodec
    (CandidateCode : Set) : Set₁ where
  field
    width : Nat
    encode :
      CandidateCode →
      CNF.Bits width
    decode :
      CNF.Bits width →
      CandidateCode
    decodeEncode :
      (code : CandidateCode) →
      decode (encode code)
      ≡
      code

open FixedWidthCandidateCodeCodec public

candidateCodeEncodeInjective :
  ∀ {CandidateCode : Set}
    (codec : FixedWidthCandidateCodeCodec CandidateCode)
    {left right : CandidateCode} →
  encode codec left ≡ encode codec right →
  left ≡ right
candidateCodeEncodeInjective codec {left} {right} encodedEqual =
  trans
    (symmetryLeft)
    symmetryRight
  where
    symmetryLeft :
      left ≡ decode codec (encode codec left)
    symmetryLeft
      rewrite decodeEncode codec left =
      refl

    decodedEqual :
      decode codec (encode codec left)
      ≡
      decode codec (encode codec right)
    decodedEqual =
      cong (decode codec) encodedEqual

    symmetryRight :
      decode codec (encode codec left)
      ≡
      right
    symmetryRight =
      trans
        decodedEqual
        (decodeEncode codec right)

------------------------------------------------------------------------
-- Cook-formula quotation induced by the codec.
------------------------------------------------------------------------

quoteCandidateCode :
  ∀ {CandidateCode : Set} →
  FixedWidthCandidateCodeCodec CandidateCode →
  CandidateCode →
  Cook.BooleanFormula
quoteCandidateCode codec code =
  Quote.embedBitsAsTautology
    (encode codec code)

quoteCandidateCodeInjective :
  ∀ {CandidateCode : Set}
    (codec : FixedWidthCandidateCodeCodec CandidateCode)
    {left right : CandidateCode} →
  quoteCandidateCode codec left
  ≡
  quoteCandidateCode codec right →
  left ≡ right
quoteCandidateCodeInjective codec formulaEqual =
  candidateCodeEncodeInjective
    codec
    (embedBitsAsTautologyInjective formulaEqual)

------------------------------------------------------------------------
-- Exact size inherited from the existing bit quotation.
------------------------------------------------------------------------

quoteCandidateCodeNodeCount :
  ∀ {CandidateCode : Set}
    (codec : FixedWidthCandidateCodeCodec CandidateCode)
    (code : CandidateCode) →
  Quote.formulaNodeCount
    (quoteCandidateCode codec code)
  ≡
  suc (Quote.four * width codec)
quoteCandidateCodeNodeCount codec code =
  Quote.embedBitsNodeCount
    (encode codec code)

------------------------------------------------------------------------
-- FRONTIER
--
-- To instantiate this for the executable SAT cost refinement, the concrete
-- candidate-code type only needs a fixed-width codec.  The existing concrete
-- tape program owner already has precisely this style of finite bit encoding.
--
-- No reverse extraction from the old extensional PolynomialCostModel is used.
------------------------------------------------------------------------
