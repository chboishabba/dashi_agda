module DASHI.ComputerScience.TekumSourceWordRoundTripExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Base using (_++_; cast)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- LOSSLESS IMAGE OF THE SOURCE FIELD PARSER
--
-- Source.parsePayload already carries the exact dependent equation
--
--   payload = cast(fieldLength) (exponentMSB ++ fractionMSB).
--
-- This owner turns that witness into an explicit rejoin operation.  It is the
-- structural inverse needed downstream by the no-redundant-encoding proof:
-- once sign/exponent/fraction data agree, there is no untracked payload data
-- left to recover.
------------------------------------------------------------------------

rejoinPayload :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload →
  Vec Trit.Trit (5 + extra)
rejoinPayload parsed =
  cast (Source.fieldLength parsed)
    (Source.exponentMSB parsed ++ Source.fractionMSB parsed)

rejoinPayloadCorrect :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  rejoinPayload parsed ≡ payload
rejoinPayloadCorrect parsed = sym (Source.payloadJoin parsed)

------------------------------------------------------------------------
-- Exact three-trit source regime prefix, in most-significant-first order.
------------------------------------------------------------------------

regimePrefixMSB : Regime.RegimeCode → Vec Trit.Trit 3
regimePrefixMSB Regime.rm7 = Trit.neg ∷ Trit.pos ∷ Trit.neg ∷ []
regimePrefixMSB Regime.rm6 = Trit.neg ∷ Trit.pos ∷ Trit.zer ∷ []
regimePrefixMSB Regime.rm5 = Trit.neg ∷ Trit.pos ∷ Trit.pos ∷ []
regimePrefixMSB Regime.rm4 = Trit.zer ∷ Trit.neg ∷ Trit.neg ∷ []
regimePrefixMSB Regime.rm3 = Trit.zer ∷ Trit.neg ∷ Trit.zer ∷ []
regimePrefixMSB Regime.rm2 = Trit.zer ∷ Trit.neg ∷ Trit.pos ∷ []
regimePrefixMSB Regime.rm1 = Trit.zer ∷ Trit.zer ∷ Trit.neg ∷ []
regimePrefixMSB Regime.r0  = Trit.zer ∷ Trit.zer ∷ Trit.zer ∷ []
regimePrefixMSB Regime.rp1 = Trit.zer ∷ Trit.zer ∷ Trit.pos ∷ []
regimePrefixMSB Regime.rp2 = Trit.zer ∷ Trit.pos ∷ Trit.neg ∷ []
regimePrefixMSB Regime.rp3 = Trit.zer ∷ Trit.pos ∷ Trit.zer ∷ []
regimePrefixMSB Regime.rp4 = Trit.zer ∷ Trit.pos ∷ Trit.pos ∷ []
regimePrefixMSB Regime.rp5 = Trit.pos ∷ Trit.neg ∷ Trit.neg ∷ []
regimePrefixMSB Regime.rp6 = Trit.pos ∷ Trit.neg ∷ Trit.zer ∷ []
regimePrefixMSB Regime.rp7 = Trit.pos ∷ Trit.neg ∷ Trit.pos ∷ []

rejoinAnchorMSB :
  ∀ {extra} →
  Regime.RegimeCode →
  Vec Trit.Trit (5 + extra) →
  Vec Trit.Trit (8 + extra)
rejoinAnchorMSB r payload = regimePrefixMSB r ++ payload

rejoinParsedAnchorMSB :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload →
  Vec Trit.Trit (8 + extra)
rejoinParsedAnchorMSB {r = r} parsed =
  rejoinAnchorMSB r (rejoinPayload parsed)

rejoinParsedAnchorPayloadCorrect :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  rejoinParsedAnchorMSB parsed
  ≡ rejoinAnchorMSB r payload
rejoinParsedAnchorPayloadCorrect {r = r} parsed =
  cong (rejoinAnchorMSB r) (rejoinPayloadCorrect parsed)

------------------------------------------------------------------------
-- Calibration: the prefix function is the source regime table, not a second
-- regime semantics.  These definitional rows deliberately mirror
-- Regime.regimeTrits/decodeEncodeRegime.
------------------------------------------------------------------------

negativeOuterPrefix :
  regimePrefixMSB Regime.rm7
  ≡ Trit.neg ∷ Trit.pos ∷ Trit.neg ∷ []
negativeOuterPrefix = refl

centralPrefix :
  regimePrefixMSB Regime.r0
  ≡ Trit.zer ∷ Trit.zer ∷ Trit.zer ∷ []
centralPrefix = refl

positiveOuterPrefix :
  regimePrefixMSB Regime.rp7
  ≡ Trit.pos ∷ Trit.neg ∷ Trit.pos ∷ []
positiveOuterPrefix = refl

record SourceParserRoundTripBoundary : Set where
  constructor sourceParserRoundTripBoundary
  field
    dependentPayloadRejoinPaid : Bool
    sourceRegimePrefixRejoinPaid : Bool
    ordinaryAnchorImageCarriesNoHiddenPayload : Bool
    inverseConcreteAnchorToSourceWordPaidHere : Bool

sourceParserImageIsLossless : SourceParserRoundTripBoundary
sourceParserImageIsLossless =
  sourceParserRoundTripBoundary true true true false
