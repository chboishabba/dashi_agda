module DASHI.ComputerScience.GodelArithmeticPrefixStreamCodecExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.ComputerScience.GodelArithmeticRawSyntaxExact as Syntax

data SyntaxToken : Set where
  natZeroToken natSuccToken : SyntaxToken
  termVariableToken termZeroToken termSuccessorToken : SyntaxToken
  termAddToken termMultiplyToken : SyntaxToken
  formulaEqualToken formulaFalseToken : SyntaxToken
  formulaImplyToken formulaForallToken : SyntaxToken

data ParseResult (A : Set) : Set where
  parseFailure : ParseResult A
  parsed : A → List SyntaxToken → ParseResult A

encodeNatInto : Nat → List SyntaxToken → List SyntaxToken
encodeNatInto 0 rest = natZeroToken ∷ rest
encodeNatInto (suc n) rest = natSuccToken ∷ encodeNatInto n rest

encodeTermInto : Syntax.ArithmeticTerm → List SyntaxToken → List SyntaxToken
encodeTermInto (Syntax.variableTerm index) rest = termVariableToken ∷ encodeNatInto index rest
encodeTermInto Syntax.zeroTerm rest = termZeroToken ∷ rest
encodeTermInto (Syntax.successorTerm term) rest = termSuccessorToken ∷ encodeTermInto term rest
encodeTermInto (Syntax.addTerm left right) rest = termAddToken ∷ encodeTermInto left (encodeTermInto right rest)
encodeTermInto (Syntax.multiplyTerm left right) rest = termMultiplyToken ∷ encodeTermInto left (encodeTermInto right rest)

encodeFormulaInto : Syntax.ArithmeticFormula → List SyntaxToken → List SyntaxToken
encodeFormulaInto (Syntax.equalFormula left right) rest = formulaEqualToken ∷ encodeTermInto left (encodeTermInto right rest)
encodeFormulaInto Syntax.falseFormula rest = formulaFalseToken ∷ rest
encodeFormulaInto (Syntax.implyFormula left right) rest = formulaImplyToken ∷ encodeFormulaInto left (encodeFormulaInto right rest)
encodeFormulaInto (Syntax.forallFormula body) rest = formulaForallToken ∷ encodeFormulaInto body rest

encodeFormula : Syntax.ArithmeticFormula → List SyntaxToken
encodeFormula formula = encodeFormulaInto formula []

parseNat : List SyntaxToken → ParseResult Nat
parseNat [] = parseFailure
parseNat (natZeroToken ∷ rest) = parsed 0 rest
parseNat (natSuccToken ∷ rest) with parseNat rest
... | parseFailure = parseFailure
... | parsed n suffix = parsed (suc n) suffix
parseNat (_ ∷ _) = parseFailure

parseTerm : List SyntaxToken → ParseResult Syntax.ArithmeticTerm
parseTerm [] = parseFailure
parseTerm (termVariableToken ∷ rest) with parseNat rest
... | parseFailure = parseFailure
... | parsed index suffix = parsed (Syntax.variableTerm index) suffix
parseTerm (termZeroToken ∷ rest) = parsed Syntax.zeroTerm rest
parseTerm (termSuccessorToken ∷ rest) with parseTerm rest
... | parseFailure = parseFailure
... | parsed term suffix = parsed (Syntax.successorTerm term) suffix
parseTerm (termAddToken ∷ rest) with parseTerm rest
... | parseFailure = parseFailure
... | parsed left restAfterLeft with parseTerm restAfterLeft
...   | parseFailure = parseFailure
...   | parsed right suffix = parsed (Syntax.addTerm left right) suffix
parseTerm (termMultiplyToken ∷ rest) with parseTerm rest
... | parseFailure = parseFailure
... | parsed left restAfterLeft with parseTerm restAfterLeft
...   | parseFailure = parseFailure
...   | parsed right suffix = parsed (Syntax.multiplyTerm left right) suffix
parseTerm (_ ∷ _) = parseFailure

parseFormula : List SyntaxToken → ParseResult Syntax.ArithmeticFormula
parseFormula [] = parseFailure
parseFormula (formulaEqualToken ∷ rest) with parseTerm rest
... | parseFailure = parseFailure
... | parsed left restAfterLeft with parseTerm restAfterLeft
...   | parseFailure = parseFailure
...   | parsed right suffix = parsed (Syntax.equalFormula left right) suffix
parseFormula (formulaFalseToken ∷ rest) = parsed Syntax.falseFormula rest
parseFormula (formulaImplyToken ∷ rest) with parseFormula rest
... | parseFailure = parseFailure
... | parsed left restAfterLeft with parseFormula restAfterLeft
...   | parseFailure = parseFailure
...   | parsed right suffix = parsed (Syntax.implyFormula left right) suffix
parseFormula (formulaForallToken ∷ rest) with parseFormula rest
... | parseFailure = parseFailure
... | parsed body suffix = parsed (Syntax.forallFormula body) suffix
parseFormula (_ ∷ _) = parseFailure

parseNatEncodeInto : (n : Nat) → (suffix : List SyntaxToken) → parseNat (encodeNatInto n suffix) ≡ parsed n suffix
parseNatEncodeInto 0 suffix = refl
parseNatEncodeInto (suc n) suffix rewrite parseNatEncodeInto n suffix = refl

parseTermEncodeInto : (term : Syntax.ArithmeticTerm) → (suffix : List SyntaxToken) → parseTerm (encodeTermInto term suffix) ≡ parsed term suffix
parseTermEncodeInto (Syntax.variableTerm index) suffix rewrite parseNatEncodeInto index suffix = refl
parseTermEncodeInto Syntax.zeroTerm suffix = refl
parseTermEncodeInto (Syntax.successorTerm term) suffix rewrite parseTermEncodeInto term suffix = refl
parseTermEncodeInto (Syntax.addTerm left right) suffix rewrite parseTermEncodeInto left (encodeTermInto right suffix) | parseTermEncodeInto right suffix = refl
parseTermEncodeInto (Syntax.multiplyTerm left right) suffix rewrite parseTermEncodeInto left (encodeTermInto right suffix) | parseTermEncodeInto right suffix = refl

parseFormulaEncodeInto : (formula : Syntax.ArithmeticFormula) → (suffix : List SyntaxToken) → parseFormula (encodeFormulaInto formula suffix) ≡ parsed formula suffix
parseFormulaEncodeInto (Syntax.equalFormula left right) suffix rewrite parseTermEncodeInto left (encodeTermInto right suffix) | parseTermEncodeInto right suffix = refl
parseFormulaEncodeInto Syntax.falseFormula suffix = refl
parseFormulaEncodeInto (Syntax.implyFormula left right) suffix rewrite parseFormulaEncodeInto left (encodeFormulaInto right suffix) | parseFormulaEncodeInto right suffix = refl
parseFormulaEncodeInto (Syntax.forallFormula body) suffix rewrite parseFormulaEncodeInto body suffix = refl

parseEncodedFormula : (formula : Syntax.ArithmeticFormula) → parseFormula (encodeFormula formula) ≡ parsed formula []
parseEncodedFormula formula = parseFormulaEncodeInto formula []

decodeFormula : List SyntaxToken → Syntax.ArithmeticFormula
decodeFormula tokens with parseFormula tokens
... | parseFailure = Syntax.falseFormula
... | parsed formula _ = formula

decodeEncodeFormula : (formula : Syntax.ArithmeticFormula) → decodeFormula (encodeFormula formula) ≡ formula
decodeEncodeFormula formula rewrite parseEncodedFormula formula = refl

data PrefixStreamRoundtripImpliesNatRetraction : Set where
data TokenStreamIsArithmeticProvability : Set where
data ParserRoundtripImpliesRepresentability : Set where

streamRoundtripDoesNotSupplyNatRetraction : PrefixStreamRoundtripImpliesNatRetraction → ⊥
streamRoundtripDoesNotSupplyNatRetraction ()
tokenStreamDoesNotSupplyProvability : TokenStreamIsArithmeticProvability → ⊥
tokenStreamDoesNotSupplyProvability ()
parserRoundtripDoesNotSupplyRepresentability : ParserRoundtripImpliesRepresentability → ⊥
parserRoundtripDoesNotSupplyRepresentability ()

record GodelArithmeticPrefixStreamCodecBoundary : Set where
  constructor godelArithmeticPrefixStreamCodecBoundary
  field
    concretePrefixEncoderOwned : Bool
    concretePrefixParserOwned : Bool
    parserEncoderSuffixLawOwned : Bool
    formulaStreamLeftInverseOwned : Bool
    streamNatRetractionOwned : Bool
    provabilityOwned : Bool
    representabilityOwned : Bool

canonicalGodelArithmeticPrefixStreamCodecBoundary : GodelArithmeticPrefixStreamCodecBoundary
canonicalGodelArithmeticPrefixStreamCodecBoundary = godelArithmeticPrefixStreamCodecBoundary true true true true false false false
