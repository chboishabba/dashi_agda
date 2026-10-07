module DASHI.ComputerScience.TekumSourceParserTotalityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base using (_,_)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumRawAnchorRegimeBandExact as Raw
import DASHI.ComputerScience.TekumSourceAnchorRegimeBandExact as Band
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumSpecialValuesExact as Special
import DASHI.ComputerScience.TekumWidthAdmissibilityExact as Width

------------------------------------------------------------------------
-- EVERY NON-SPECIAL CORE-WIDTH SOURCE WORD HAS A SUCCESSFUL ORDINARY PARSE
------------------------------------------------------------------------

record OrdinaryParseWitness {extra}
    (word : Vec.Vec Trit.Trit (8 + extra)) : Set where
  constructor ordinaryParseWitness
  field
    regime : DASHI.ComputerScience.TekumRegimeExponentExact.RegimeCode
    payload : Vec.Vec Trit.Trit (5 + extra)
    parsed : Source.ParsedPayload extra regime payload
    parseEq :
      Source.parseOrdinaryAnchor word
      ≡ just (regime , payload , parsed)
open OrdinaryParseWitness public

nonSpecialParseTotal :
  ∀ {extra}
  (even : Width.EvenWidth (8 + extra))
  (word : Vec.Vec Trit.Trit (8 + extra)) →
  Special.classifySpecial word ≡ nothing →
  OrdinaryParseWitness word
nonSpecialParseTotal {extra} even word nonSpecial
  with Source.anchorMSB word in anchorEq
... | a Vec.∷ b Vec.∷ c Vec.∷ payload
  with Band.nonSpecialAnchorBand even word nonSpecial
... | lower , upper
  with Raw.anchorBandParsesRegime a b c payload
    (transportLower anchorEq lower)
    (transportUpper anchorEq upper)
... | Raw.legalRegimePrefix r decodeEq =
  ordinaryParseWitness r payload (Source.parsePayload r payload) parseProof
  where
  transportLower :
    Source.anchorMSB word ≡ a Vec.∷ b Vec.∷ c Vec.∷ payload →
    6 * Raw.payloadScale extra ≤ Raw.rawAnchorCode (Source.anchorMSB word) →
    6 * Raw.payloadScale extra
      ≤ Raw.rawAnchorCode (a Vec.∷ b Vec.∷ c Vec.∷ payload)
  transportLower eq lower =
    subst
      (λ anchor → 6 * Raw.payloadScale extra ≤ Raw.rawAnchorCode anchor)
      eq lower

  transportUpper :
    Source.anchorMSB word ≡ a Vec.∷ b Vec.∷ c Vec.∷ payload →
    Raw.rawAnchorCode (Source.anchorMSB word) < 21 * Raw.payloadScale extra →
    Raw.rawAnchorCode (a Vec.∷ b Vec.∷ c Vec.∷ payload)
      < 21 * Raw.payloadScale extra
  transportUpper eq upper =
    subst
      (λ anchor → Raw.rawAnchorCode anchor < 21 * Raw.payloadScale extra)
      eq upper

  parseProof :
    Source.parseOrdinaryAnchor word
    ≡ just (r , payload , Source.parsePayload r payload)
  parseProof
    rewrite anchorEq | decodeEq = refl

------------------------------------------------------------------------
-- SOURCE PARSER TOTALITY INCLUDING RESERVED SPECIALS
------------------------------------------------------------------------

data TotalSourceParse {extra}
    (word : Vec.Vec Trit.Trit (8 + extra)) : Set where
  parsedNaR :
    Special.classifySpecial word ≡ just Sem.naR →
    TotalSourceParse word
  parsedZero :
    Special.classifySpecial word ≡ just Sem.zeroValue →
    TotalSourceParse word
  parsedInfinity :
    Special.classifySpecial word ≡ just Sem.infinity →
    TotalSourceParse word
  parsedOrdinary :
    Special.classifySpecial word ≡ nothing →
    OrdinaryParseWitness word →
    TotalSourceParse word

totalSourceParse :
  ∀ {extra}
  (even : Width.EvenWidth (8 + extra))
  (word : Vec.Vec Trit.Trit (8 + extra)) →
  TotalSourceParse word
totalSourceParse even word
  with Special.classifySpecial word in classifyEq
... | just Sem.naR = parsedNaR classifyEq
... | just Sem.zeroValue = parsedZero classifyEq
... | just Sem.infinity = parsedInfinity classifyEq
... | nothing = parsedOrdinary classifyEq (nonSpecialParseTotal even word classifyEq)
