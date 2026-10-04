module DASHI.ComputerScience.TekumParsedAnchorListExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (_+_)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_,_)
import Data.List.Base as List
import Data.List.Properties as ListP
import Data.Vec.Base as Vec
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumParserSuccessfulRejoinExact as Rejoin
import DASHI.ComputerScience.TekumRegimeSuccessorExact as RegimeStep
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumSourceWordRoundTripExact as RoundTrip

------------------------------------------------------------------------
-- CAST-ERASED LST NORMAL FORM FOR A SUCCESSFULLY PARSED ANCHOR
--
-- Parser records are stored MSB first as
--
--   regime ++ exponent ++ fraction.
--
-- Carry analysis is LST first.  Moving to List erases the dependent Vec
-- length casts without erasing any trit data, giving the literal normal form
--
--   fractionLST ++ exponentLST ++ regimeLST.
------------------------------------------------------------------------

parsedAnchorList :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload →
  List.List Trit.Trit
parsedAnchorList {r = r} parsed =
  (Vec.toList (Source.fractionLST parsed)
    List.++ Vec.toList (Source.exponentLST parsed))
  List.++ Vec.toList (RegimeStep.regimeLST r)

rejoinPayloadReverseList :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  List.reverse (Vec.toList (RoundTrip.rejoinPayload parsed))
  ≡
  Vec.toList (Source.fractionLST parsed)
    List.++ Vec.toList (Source.exponentLST parsed)
rejoinPayloadReverseList parsed =
  trans
    (cong List.reverse
      (VecP.toList-cast
        (Source.fieldLength parsed)
        (Source.exponentMSB parsed Vec.++ Source.fractionMSB parsed)))
    (trans
      (cong List.reverse
        (VecP.toList-++
          (Source.exponentMSB parsed)
          (Source.fractionMSB parsed)))
      (trans
        (ListP.reverse-++
          (Vec.toList (Source.exponentMSB parsed))
          (Vec.toList (Source.fractionMSB parsed)))
        (cong₂ List._++_
          (sym (VecP.toList-reverse (Source.fractionMSB parsed)))
          (sym (VecP.toList-reverse (Source.exponentMSB parsed))))))

rejoinParsedAnchorReverseList :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  List.reverse (Vec.toList (RoundTrip.rejoinParsedAnchorMSB parsed))
  ≡ parsedAnchorList parsed
rejoinParsedAnchorReverseList {r = r} parsed =
  trans
    (cong List.reverse
      (VecP.toList-++
        (RoundTrip.regimePrefixMSB r)
        (RoundTrip.rejoinPayload parsed)))
    (trans
      (ListP.reverse-++
        (Vec.toList (RoundTrip.regimePrefixMSB r))
        (Vec.toList (RoundTrip.rejoinPayload parsed)))
      (cong₂ List._++_
        (rejoinPayloadReverseList parsed)
        (sym (VecP.toList-reverse (RoundTrip.regimePrefixMSB r)))))

anchorMSBReverseToSourceList :
  ∀ {extra}
  (word : Vec.Vec Trit.Trit (8 + extra)) →
  List.reverse (Vec.toList (Source.anchorMSB word))
  ≡ Vec.toList (Fixed.concreteAnchor word)
anchorMSBReverseToSourceList word =
  trans
    (cong List.reverse
      (VecP.toList-reverse (Fixed.concreteAnchor word)))
    (ListP.reverse-involutive (Vec.toList (Fixed.concreteAnchor word)))

successfulParseAnchorList :
  ∀ {extra r payload parsed}
  (word : Vec.Vec Trit.Trit (8 + extra)) →
  Source.parseOrdinaryAnchor word ≡ just (r , payload , parsed) →
  Vec.toList (Fixed.concreteAnchor word) ≡ parsedAnchorList parsed
successfulParseAnchorList word parseEq =
  trans
    (sym (anchorMSBReverseToSourceList word))
    (trans
      (cong (λ anchor → List.reverse (Vec.toList anchor))
        (Rejoin.parseOrdinaryAnchorSuccessfulRejoin word parseEq))
      (rejoinParsedAnchorReverseList _))
