module DASHI.ComputerScience.TekumProposition4PositiveChainExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base as ℚ using (ℚ; _<_)
import Data.Rational.Properties as ℚP
open import Data.Vec.Base using (Vec)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumBalancedSuccessorExact as Succ
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumMonotonicityExact as Monotone
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- PARSED-ANCHOR CHAIN CARRIER FOR HUNHOLD PROP. 4
--
-- The adjacent theorem is now paid separately.  This owner pays the arbitrary
-- finite-gap transitivity step without assuming parser totality: a client only
-- needs to construct the successfully parsed chain between two source codes.
------------------------------------------------------------------------

record ParsedAnchorNode (extra : Nat) : Set where
  constructor parsedAnchorNode
  field
    word : Vec Trit.Trit (8 + extra)
    regime : Regime.RegimeCode
    payload : Vec Trit.Trit (5 + extra)
    parsed : Source.ParsedPayload extra regime payload
    parseWitness :
      Source.parseOrdinaryAnchor word ≡ just (regime , payload , parsed)
open ParsedAnchorNode public

nodeMagnitude : ∀ {extra} → ParsedAnchorNode extra → ℚ
nodeMagnitude node = Parsed.parsedMagnitude (parsed node)

data ParsedAnchorStep {extra : Nat}
    (left right : ParsedAnchorNode extra) : Set where
  parsedAnchorStep :
    Succ.successorWord (Fixed.concreteAnchor (word left))
      ≡ Fixed.concreteAnchor (word right) →
    ParsedAnchorStep left right

parsedAnchorStepStrict :
  ∀ {extra} {left right : ParsedAnchorNode extra} →
  ParsedAnchorStep left right →
  nodeMagnitude left ℚ.< nodeMagnitude right
parsedAnchorStepStrict {left = left} {right = right}
    (parsedAnchorStep anchorStep) =
  Monotone.hunholdProposition4PositiveParsedAdjacent
    (word left) (word right)
    (parseWitness left) (parseWitness right) anchorStep

data ParsedAnchorChain {extra : Nat}
    (start : ParsedAnchorNode extra) :
    ParsedAnchorNode extra → Set where
  single :
    ∀ {finish} →
    ParsedAnchorStep start finish →
    ParsedAnchorChain start finish
  cons :
    ∀ {middle finish} →
    ParsedAnchorStep start middle →
    ParsedAnchorChain middle finish →
    ParsedAnchorChain start finish

parsedAnchorChainStrict :
  ∀ {extra} {start finish : ParsedAnchorNode extra} →
  ParsedAnchorChain start finish →
  nodeMagnitude start ℚ.< nodeMagnitude finish
parsedAnchorChainStrict (single step) = parsedAnchorStepStrict step
parsedAnchorChainStrict (cons step rest) =
  ℚP.<-trans (parsedAnchorStepStrict step) (parsedAnchorChainStrict rest)

------------------------------------------------------------------------
-- Max-cut boundary:
--
--   source integer-code order
--        -> construct ParsedAnchorChain
--        -> parsedAnchorChainStrict
--
-- All numerical/transitive work after chain construction is paid here.
------------------------------------------------------------------------
