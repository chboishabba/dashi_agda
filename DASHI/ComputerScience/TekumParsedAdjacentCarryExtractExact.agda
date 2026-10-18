module DASHI.ComputerScience.TekumParsedAdjacentCarryExtractExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base using (_×_; _,_)
import Data.List.Base as List
import Data.List.Properties as ListP
import Data.Nat.Properties as NatP
import Data.Integer.Properties as ℤP
import Data.Vec.Base as Vec
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumBalancedSuccessorExact as Succ
import DASHI.ComputerScience.TekumExactTriadicSemanticsExact as Exact
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumFractionSuccessorExact as FractionStep
import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor
import DASHI.ComputerScience.TekumParsedAnchorListExact as AnchorList
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumRegimeExponentIntervalExact as Interval
import DASHI.ComputerScience.TekumRegimeSuccessorExact as RegimeStep
import DASHI.ComputerScience.TekumSourceOrderExact as Order
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumSuccessorCarrySplitExact as Carry

------------------------------------------------------------------------
-- LIST-LEVEL CANCELLATION
--
-- Parser field widths are dependent on the regime.  The previous owner erases
-- only those length casts, not the data.  These elementary list lemmas let us
-- recover fixed-size prefixes/suffixes and then return to Vec equality.
------------------------------------------------------------------------

appendPrefixSplit :
  ∀ {A : Set}
  (xs ys us vs : List.List A) →
  List.length xs ≡ List.length us →
  xs List.++ ys ≡ us List.++ vs →
  (xs ≡ us) × (ys ≡ vs)
appendPrefixSplit List.[] ys List.[] vs lengthEq wholeEq = refl , wholeEq
appendPrefixSplit List.[] ys (u List.∷ us) vs () wholeEq
appendPrefixSplit (x List.∷ xs) ys List.[] vs () wholeEq
appendPrefixSplit (x List.∷ xs) ys (u List.∷ us) vs lengthEq wholeEq
  with ListP.∷-injective wholeEq
... | xEq , tailEq
  with appendPrefixSplit xs ys us vs (NatP.suc-injective lengthEq) tailEq
... | xsEq , ysEq = cong₂ List._∷_ xEq xsEq , ysEq

appendSuffixSplit :
  ∀ {A : Set}
  (xs zs ys ws : List.List A) →
  List.length zs ≡ List.length ws →
  xs List.++ zs ≡ ys List.++ ws →
  (xs ≡ ys) × (zs ≡ ws)
appendSuffixSplit xs zs ys ws suffixLength wholeEq
  with appendPrefixSplit
    (List.reverse zs) (List.reverse xs)
    (List.reverse ws) (List.reverse ys)
    reversedLength reversedEq
... | suffixReverseEq , prefixReverseEq =
  ListP.reverse-injective prefixReverseEq ,
  ListP.reverse-injective suffixReverseEq
  where
  reversedLength :
    List.length (List.reverse zs) ≡ List.length (List.reverse ws)
  reversedLength =
    trans (ListP.length-reverse zs)
      (trans suffixLength (sym (ListP.length-reverse ws)))

  reversedEq :
    List.reverse zs List.++ List.reverse xs
    ≡ List.reverse ws List.++ List.reverse ys
  reversedEq =
    trans
      (sym (ListP.reverse-++ xs zs))
      (trans (cong List.reverse wholeEq) (ListP.reverse-++ ys ws))

sameLengthToListInjective :
  ∀ {A : Set} {n : Nat}
  (xs ys : Vec.Vec A n) →
  Vec.toList xs ≡ Vec.toList ys →
  xs ≡ ys
sameLengthToListInjective Vec.[] Vec.[] eq = refl
sameLengthToListInjective (x Vec.∷ xs) (y Vec.∷ ys) eq
  with ListP.∷-injective eq
... | xEq , tailEq =
  cong₂ Vec._∷_ xEq (sameLengthToListInjective xs ys tailEq)

sameVectorListLength :
  ∀ {A : Set} {n : Nat}
  (xs ys : Vec.Vec A n) →
  List.length (Vec.toList xs) ≡ List.length (Vec.toList ys)
sameVectorListLength xs ys =
  trans (VecP.length-toList xs) (sym (VecP.length-toList ys))

------------------------------------------------------------------------
-- BALANCED SUCCESSOR COMMUTES WITH Vec -> List.
------------------------------------------------------------------------

successorList : List.List Trit.Trit → List.List Trit.Trit
successorList List.[] = List.[]
successorList (Trit.neg List.∷ xs) = Trit.zer List.∷ xs
successorList (Trit.zer List.∷ xs) = Trit.pos List.∷ xs
successorList (Trit.pos List.∷ xs) = Trit.neg List.∷ successorList xs

successorToList :
  ∀ {n} (word : Vec.Vec Trit.Trit n) →
  Vec.toList (Succ.successorWord word)
  ≡ successorList (Vec.toList word)
successorToList Vec.[] = refl
successorToList (Trit.neg Vec.∷ xs) = refl
successorToList (Trit.zer Vec.∷ xs) = refl
successorToList (Trit.pos Vec.∷ xs) =
  cong (Trit.neg List.∷_) (successorToList xs)

threeFieldsToList :
  ∀ {a b c}
  (first : Vec.Vec Trit.Trit a)
  (second : Vec.Vec Trit.Trit b)
  (third : Vec.Vec Trit.Trit c) →
  Vec.toList (first Vec.++ (second Vec.++ third))
  ≡
  (Vec.toList first List.++ Vec.toList second)
    List.++ Vec.toList third
threeFieldsToList first second third =
  trans
    (VecP.toList-++ first (second Vec.++ third))
    (trans
      (cong (Vec.toList first List.++_)
        (VecP.toList-++ second third))
      (sym (ListP.++-assoc
        (Vec.toList first) (Vec.toList second) (Vec.toList third))))

rawParsedFields :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  Vec.Vec Trit.Trit
    (Regime.fractionCount (8 + extra) r + (Regime.exponentCount r + 3))
rawParsedFields {r = r} parsed =
  Source.fractionLST parsed Vec.++
    (Source.exponentLST parsed Vec.++ RegimeStep.regimeLST r)

rawParsedFieldsToList :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  Vec.toList (rawParsedFields parsed) ≡ AnchorList.parsedAnchorList parsed
rawParsedFieldsToList {r = r} parsed =
  threeFieldsToList
    (Source.fractionLST parsed)
    (Source.exponentLST parsed)
    (RegimeStep.regimeLST r)

------------------------------------------------------------------------
-- WHOLE-ANCHOR ADJACENCY TRANSPORTS TO THE PARSED FIELD LISTS.
------------------------------------------------------------------------

adjacentParsedLists :
  ∀ {extra r s payload₁ payload₂ parsed₁ parsed₂}
  (left right : Vec.Vec Trit.Trit (8 + extra)) →
  Source.parseOrdinaryAnchor left ≡ just (r , payload₁ , parsed₁) →
  Source.parseOrdinaryAnchor right ≡ just (s , payload₂ , parsed₂) →
  Succ.successorWord (Fixed.concreteAnchor left)
    ≡ Fixed.concreteAnchor right →
  successorList (AnchorList.parsedAnchorList parsed₁)
    ≡ AnchorList.parsedAnchorList parsed₂
adjacentParsedLists left right leftParse rightParse anchorStep =
  trans
    (cong successorList
      (sym (AnchorList.successfulParseAnchorList left leftParse)))
    (trans
      (sym (successorToList (Fixed.concreteAnchor left)))
      (trans
        (cong Vec.toList anchorStep)
        (AnchorList.successfulParseAnchorList right rightParse)))

------------------------------------------------------------------------
-- CARRY NORMAL FORMS AT LIST LEVEL.
------------------------------------------------------------------------

fractionCarryList :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  Succ.HasSuccessor (Source.fractionLST parsed) →
  successorList (AnchorList.parsedAnchorList parsed)
  ≡
  (Vec.toList (Succ.successorWord (Source.fractionLST parsed))
    List.++ Vec.toList (Source.exponentLST parsed))
  List.++ Vec.toList (RegimeStep.regimeLST r)
fractionCarryList {r = r} parsed carry =
  trans
    (cong successorList (sym (rawParsedFieldsToList parsed)))
    (trans
      (sym (successorToList (rawParsedFields parsed)))
      (trans
        (cong Vec.toList (Carry.fractionCarryCase carry))
        (threeFieldsToList
          (Succ.successorWord (Source.fractionLST parsed))
          (Source.exponentLST parsed)
          (RegimeStep.regimeLST r))))

exponentCarryList :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  Source.fractionLST parsed ≡ Carry.allPositive (Regime.fractionCount (8 + extra) r) →
  Succ.HasSuccessor (Source.exponentLST parsed) →
  successorList (AnchorList.parsedAnchorList parsed)
  ≡
  (Vec.toList (Carry.allNegative (Regime.fractionCount (8 + extra) r))
    List.++ Vec.toList (Succ.successorWord (Source.exponentLST parsed)))
  List.++ Vec.toList (RegimeStep.regimeLST r)
exponentCarryList {extra} {r} parsed fractionMax carry =
  trans
    (cong successorList (sym (rawParsedFieldsToList parsed)))
    (trans
      (sym (successorToList (rawParsedFields parsed)))
      (trans
        (cong Vec.toList successorEq)
        (threeFieldsToList
          (Carry.allNegative (Regime.fractionCount (8 + extra) r))
          (Succ.successorWord (Source.exponentLST parsed))
          (RegimeStep.regimeLST r))))
  where
  rawMaxEq :
    rawParsedFields parsed
    ≡ Carry.allPositive (Regime.fractionCount (8 + extra) r) Vec.++
        (Source.exponentLST parsed Vec.++ RegimeStep.regimeLST r)
  rawMaxEq =
    cong
      (λ fraction → fraction Vec.++
        (Source.exponentLST parsed Vec.++ RegimeStep.regimeLST r))
      fractionMax

  successorEq :
    Succ.successorWord (rawParsedFields parsed)
    ≡ Carry.allNegative (Regime.fractionCount (8 + extra) r) Vec.++
        (Succ.successorWord (Source.exponentLST parsed) Vec.++ RegimeStep.regimeLST r)
  successorEq =
    trans
      (cong Succ.successorWord rawMaxEq)
      (Carry.exponentCarryCase carry)

regimeCarryList :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  Source.fractionLST parsed ≡ Carry.allPositive (Regime.fractionCount (8 + extra) r) →
  Source.exponentLST parsed ≡ Carry.allPositive (Regime.exponentCount r) →
  Succ.HasSuccessor (RegimeStep.regimeLST r) →
  successorList (AnchorList.parsedAnchorList parsed)
  ≡
  (Vec.toList (Carry.allNegative (Regime.fractionCount (8 + extra) r))
    List.++ Vec.toList (Carry.allNegative (Regime.exponentCount r)))
  List.++ Vec.toList (Succ.successorWord (RegimeStep.regimeLST r))
regimeCarryList {extra} {r} parsed fractionMax exponentMax carry =
  trans
    (cong successorList (sym (rawParsedFieldsToList parsed)))
    (trans
      (sym (successorToList (rawParsedFields parsed)))
      (trans
        (cong Vec.toList successorEq)
        (threeFieldsToList
          (Carry.allNegative (Regime.fractionCount (8 + extra) r))
          (Carry.allNegative (Regime.exponentCount r))
          (Succ.successorWord (RegimeStep.regimeLST r)))))
  where
  rawMaxEq :
    rawParsedFields parsed
    ≡ Carry.allPositive (Regime.fractionCount (8 + extra) r) Vec.++
        (Carry.allPositive (Regime.exponentCount r) Vec.++ RegimeStep.regimeLST r)
  rawMaxEq =
    cong₂
      (λ fraction exponent → fraction Vec.++ (exponent Vec.++ RegimeStep.regimeLST r))
      fractionMax exponentMax

  successorEq :
    Succ.successorWord (rawParsedFields parsed)
    ≡ Carry.allNegative (Regime.fractionCount (8 + extra) r) Vec.++
        (Carry.allNegative (Regime.exponentCount r) Vec.++
          Succ.successorWord (RegimeStep.regimeLST r))
  successorEq =
    trans
      (cong Succ.successorWord rawMaxEq)
      (Carry.regimeCarryCase carry)

------------------------------------------------------------------------
-- REGIME DECODING / VALID-SUCCESSOR RECOVERY.
------------------------------------------------------------------------

decodeRegimeLST : Vec.Vec Trit.Trit 3 → Data.Maybe.Base.Maybe Regime.RegimeCode
decodeRegimeLST (a Vec.∷ b Vec.∷ c Vec.∷ Vec.[]) =
  Regime.decodeRegime (Anchor.regime3 c b a)

decodeRegimeLSTSound :
  (r : Regime.RegimeCode) →
  decodeRegimeLST (RegimeStep.regimeLST r) ≡ just r
decodeRegimeLSTSound Regime.rm7 = refl
decodeRegimeLSTSound Regime.rm6 = refl
decodeRegimeLSTSound Regime.rm5 = refl
decodeRegimeLSTSound Regime.rm4 = refl
decodeRegimeLSTSound Regime.rm3 = refl
decodeRegimeLSTSound Regime.rm2 = refl
decodeRegimeLSTSound Regime.rm1 = refl
decodeRegimeLSTSound Regime.r0 = refl
decodeRegimeLSTSound Regime.rp1 = refl
decodeRegimeLSTSound Regime.rp2 = refl
decodeRegimeLSTSound Regime.rp3 = refl
decodeRegimeLSTSound Regime.rp4 = refl
decodeRegimeLSTSound Regime.rp5 = refl
decodeRegimeLSTSound Regime.rp6 = refl
decodeRegimeLSTSound Regime.rp7 = refl

justInjective :
  ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
justInjective refl = refl

nothingJustImpossible :
  ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothingJustImpossible ()

regimeLSTInjective :
  ∀ {r s} →
  RegimeStep.regimeLST r ≡ RegimeStep.regimeLST s →
  r ≡ s
regimeLSTInjective {r} {s} eq =
  justInjective
    (trans
      (sym (decodeRegimeLSTSound r))
      (trans (cong decodeRegimeLST eq) (decodeRegimeLSTSound s)))

validRegimeNotAllPositive :
  (r : Regime.RegimeCode) →
  RegimeStep.regimeLST r ≡ Carry.allPositive 3 → ⊥
validRegimeNotAllPositive Regime.rm7 ()
validRegimeNotAllPositive Regime.rm6 ()
validRegimeNotAllPositive Regime.rm5 ()
validRegimeNotAllPositive Regime.rm4 ()
validRegimeNotAllPositive Regime.rm3 ()
validRegimeNotAllPositive Regime.rm2 ()
validRegimeNotAllPositive Regime.rm1 ()
validRegimeNotAllPositive Regime.r0 ()
validRegimeNotAllPositive Regime.rp1 ()
validRegimeNotAllPositive Regime.rp2 ()
validRegimeNotAllPositive Regime.rp3 ()
validRegimeNotAllPositive Regime.rp4 ()
validRegimeNotAllPositive Regime.rp5 ()
validRegimeNotAllPositive Regime.rp6 ()
validRegimeNotAllPositive Regime.rp7 ()

data ParsedRegimeSuccessor (r s : Regime.RegimeCode) : Set where
  parsedRegimeSuccessor :
    (step : RegimeStep.RegimeSuccessor r) →
    RegimeStep.nextRegime r step ≡ s →
    ParsedRegimeSuccessor r s

regimeSuccessorFromWitness :
  ∀ {r s}
  (step : RegimeStep.RegimeSuccessor r) →
  Succ.successorWord (RegimeStep.regimeLST r) ≡ RegimeStep.regimeLST s →
  ParsedRegimeSuccessor r s
regimeSuccessorFromWitness {r} {s} step eq =
  parsedRegimeSuccessor step
    (regimeLSTInjective
      (trans (sym (RegimeStep.regimeWordSuccessor step)) eq))

rp7SuccessorDecodesNothing :
  decodeRegimeLST
    (Succ.successorWord (RegimeStep.regimeLST Regime.rp7))
  ≡ nothing
rp7SuccessorDecodesNothing = refl

regimeSuccessorFromParsedEquality :
  ∀ {r s} →
  Succ.successorWord (RegimeStep.regimeLST r)
    ≡ RegimeStep.regimeLST s →
  ParsedRegimeSuccessor r s
regimeSuccessorFromParsedEquality {Regime.rm7} eq =
  regimeSuccessorFromWitness RegimeStep.next-rm7 eq
regimeSuccessorFromParsedEquality {Regime.rm6} eq =
  regimeSuccessorFromWitness RegimeStep.next-rm6 eq
regimeSuccessorFromParsedEquality {Regime.rm5} eq =
  regimeSuccessorFromWitness RegimeStep.next-rm5 eq
regimeSuccessorFromParsedEquality {Regime.rm4} eq =
  regimeSuccessorFromWitness RegimeStep.next-rm4 eq
regimeSuccessorFromParsedEquality {Regime.rm3} eq =
  regimeSuccessorFromWitness RegimeStep.next-rm3 eq
regimeSuccessorFromParsedEquality {Regime.rm2} eq =
  regimeSuccessorFromWitness RegimeStep.next-rm2 eq
regimeSuccessorFromParsedEquality {Regime.rm1} eq =
  regimeSuccessorFromWitness RegimeStep.next-rm1 eq
regimeSuccessorFromParsedEquality {Regime.r0} eq =
  regimeSuccessorFromWitness RegimeStep.next-r0 eq
regimeSuccessorFromParsedEquality {Regime.rp1} eq =
  regimeSuccessorFromWitness RegimeStep.next-rp1 eq
regimeSuccessorFromParsedEquality {Regime.rp2} eq =
  regimeSuccessorFromWitness RegimeStep.next-rp2 eq
regimeSuccessorFromParsedEquality {Regime.rp3} eq =
  regimeSuccessorFromWitness RegimeStep.next-rp3 eq
regimeSuccessorFromParsedEquality {Regime.rp4} eq =
  regimeSuccessorFromWitness RegimeStep.next-rp4 eq
regimeSuccessorFromParsedEquality {Regime.rp5} eq =
  regimeSuccessorFromWitness RegimeStep.next-rp5 eq
regimeSuccessorFromParsedEquality {Regime.rp6} eq =
  regimeSuccessorFromWitness RegimeStep.next-rp6 eq
regimeSuccessorFromParsedEquality {Regime.rp7} {s} eq =
  ⊥-elim
    (nothingJustImpossible
      (trans
        (sym rp7SuccessorDecodesNothing)
        (trans (cong decodeRegimeLST eq) (decodeRegimeLSTSound s))))

------------------------------------------------------------------------
-- EXPONENT FIELD COMPILERS.
------------------------------------------------------------------------

sameRegimeExponentFieldEqual :
  ∀ {extra r payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra r payload₂) →
  Source.exponentLST p ≡ Source.exponentLST q →
  Factor.sourceExponentInteger p ≡ Factor.sourceExponentInteger q
sameRegimeExponentFieldEqual {r = r} p q exponentEq
  rewrite Source.exponentIntCodeInteger p
        | Source.exponentIntCodeInteger q
        | exponentEq = refl

sameRegimeExponentSuccessorStrict :
  ∀ {extra r payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra r payload₂) →
  Succ.HasSuccessor (Source.exponentLST p) →
  Source.exponentLST q ≡ Succ.successorWord (Source.exponentLST p) →
  Factor.sourceExponentInteger p Data.Integer.Base.< Factor.sourceExponentInteger q
sameRegimeExponentSuccessorStrict {r = r} p q carry exponentEq
  rewrite Source.exponentIntCodeInteger p
        | Source.exponentIntCodeInteger q
        | exponentEq
        | Succ.successorInteger carry =
  ℤP.+-monoˡ-<
    (Exact.intCodeToInteger (Regime.bias r))
    (FractionStep.integerAddOneStrict
      (BT.toInteger (BT.eval (Source.exponentLST p))))

regimeStepExponentStrict :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂)
  (step : RegimeStep.RegimeSuccessor r) →
  RegimeStep.nextRegime r step ≡ s →
  Factor.sourceExponentInteger p Data.Integer.Base.< Factor.sourceExponentInteger q
regimeStepExponentStrict p q step refl =
  ℤP.<-≤-trans
    (ℤP.≤-<-trans
      (Interval.parsedExponentUpper p)
      (RegimeStep.regimeExponentBlocksStrictlyIncrease step))
    (Interval.parsedExponentLower q)

------------------------------------------------------------------------
-- THE STRUCTURAL LEAF: SUCCESSFUL ADJACENT PARSES -> PositiveAdjacentOrder.
------------------------------------------------------------------------

extractPositiveAdjacentOrder :
  ∀ {extra r s payload₁ payload₂ parsed₁ parsed₂}
  (left right : Vec.Vec Trit.Trit (8 + extra)) →
  Source.parseOrdinaryAnchor left ≡ just (r , payload₁ , parsed₁) →
  Source.parseOrdinaryAnchor right ≡ just (s , payload₂ , parsed₂) →
  Succ.successorWord (Fixed.concreteAnchor left)
    ≡ Fixed.concreteAnchor right →
  Order.PositiveAdjacentOrder parsed₁ parsed₂
extractPositiveAdjacentOrder {extra} {r} {s}
    {parsed₁ = p} {parsed₂ = q}
    left right leftParse rightParse anchorStep
  with Carry.classifyThreeFieldCarry
    (Source.fractionLST p)
    (Source.exponentLST p)
    (RegimeStep.regimeLST r)
... | Carry.fractionStops fractionCarry =
  fractionBranch
  where
  wholeEq :
    ((Vec.toList (Succ.successorWord (Source.fractionLST p))
      List.++ Vec.toList (Source.exponentLST p))
      List.++ Vec.toList (RegimeStep.regimeLST r))
    ≡ AnchorList.parsedAnchorList q
  wholeEq =
    trans
      (sym (fractionCarryList p fractionCarry))
      (adjacentParsedLists left right leftParse rightParse anchorStep)

  splitSuffix :
    ((Vec.toList (Succ.successorWord (Source.fractionLST p))
      List.++ Vec.toList (Source.exponentLST p))
      ≡
      (Vec.toList (Source.fractionLST q)
        List.++ Vec.toList (Source.exponentLST q)))
    ×
    (Vec.toList (RegimeStep.regimeLST r)
      ≡ Vec.toList (RegimeStep.regimeLST s))
  splitSuffix =
    appendSuffixSplit
      (Vec.toList (Succ.successorWord (Source.fractionLST p))
        List.++ Vec.toList (Source.exponentLST p))
      (Vec.toList (RegimeStep.regimeLST r))
      (Vec.toList (Source.fractionLST q)
        List.++ Vec.toList (Source.exponentLST q))
      (Vec.toList (RegimeStep.regimeLST s))
      (sameVectorListLength (RegimeStep.regimeLST r) (RegimeStep.regimeLST s))
      wholeEq

  regimeEq : r ≡ s
  regimeEq =
    regimeLSTInjective
      (sameLengthToListInjective
        (RegimeStep.regimeLST r)
        (RegimeStep.regimeLST s)
        (Data.Product.Base.proj₂ splitSuffix))

  fractionBranch : Order.PositiveAdjacentOrder p q
  fractionBranch with regimeEq
  ... | refl =
    Order.fractionStops fractionCarry exponentEq (sym fractionEq)
    where
    splitPrefix :
      (Vec.toList (Succ.successorWord (Source.fractionLST p))
        ≡ Vec.toList (Source.fractionLST q))
      ×
      (Vec.toList (Source.exponentLST p)
        ≡ Vec.toList (Source.exponentLST q))
    splitPrefix =
      appendPrefixSplit
        (Vec.toList (Succ.successorWord (Source.fractionLST p)))
        (Vec.toList (Source.exponentLST p))
        (Vec.toList (Source.fractionLST q))
        (Vec.toList (Source.exponentLST q))
        (sameVectorListLength
          (Succ.successorWord (Source.fractionLST p))
          (Source.fractionLST q))
        (Data.Product.Base.proj₁ splitSuffix)

    fractionEq :
      Succ.successorWord (Source.fractionLST p) ≡ Source.fractionLST q
    fractionEq =
      sameLengthToListInjective
        (Succ.successorWord (Source.fractionLST p))
        (Source.fractionLST q)
        (Data.Product.Base.proj₁ splitPrefix)

    exponentFieldEq : Source.exponentLST p ≡ Source.exponentLST q
    exponentFieldEq =
      sameLengthToListInjective
        (Source.exponentLST p)
        (Source.exponentLST q)
        (Data.Product.Base.proj₂ splitPrefix)

    exponentEq :
      Factor.sourceExponentInteger p ≡ Factor.sourceExponentInteger q
    exponentEq = sameRegimeExponentFieldEqual p q exponentFieldEq

... | Carry.exponentStops fractionMax exponentCarry =
  exponentBranch
  where
  wholeEq :
    ((Vec.toList (Carry.allNegative (Regime.fractionCount (8 + extra) r))
      List.++ Vec.toList (Succ.successorWord (Source.exponentLST p)))
      List.++ Vec.toList (RegimeStep.regimeLST r))
    ≡ AnchorList.parsedAnchorList q
  wholeEq =
    trans
      (sym (exponentCarryList p fractionMax exponentCarry))
      (adjacentParsedLists left right leftParse rightParse anchorStep)

  splitSuffix =
    appendSuffixSplit
      (Vec.toList (Carry.allNegative (Regime.fractionCount (8 + extra) r))
        List.++ Vec.toList (Succ.successorWord (Source.exponentLST p)))
      (Vec.toList (RegimeStep.regimeLST r))
      (Vec.toList (Source.fractionLST q)
        List.++ Vec.toList (Source.exponentLST q))
      (Vec.toList (RegimeStep.regimeLST s))
      (sameVectorListLength (RegimeStep.regimeLST r) (RegimeStep.regimeLST s))
      wholeEq

  regimeEq : r ≡ s
  regimeEq =
    regimeLSTInjective
      (sameLengthToListInjective
        (RegimeStep.regimeLST r)
        (RegimeStep.regimeLST s)
        (Data.Product.Base.proj₂ splitSuffix))

  exponentBranch : Order.PositiveAdjacentOrder p q
  exponentBranch with regimeEq
  ... | refl =
    Order.exponentStops
      (sameRegimeExponentSuccessorStrict p q exponentCarry (sym exponentFieldEq))
    where
    splitPrefix =
      appendPrefixSplit
        (Vec.toList (Carry.allNegative (Regime.fractionCount (8 + extra) r)))
        (Vec.toList (Succ.successorWord (Source.exponentLST p)))
        (Vec.toList (Source.fractionLST q))
        (Vec.toList (Source.exponentLST q))
        (sameVectorListLength
          (Carry.allNegative (Regime.fractionCount (8 + extra) r))
          (Source.fractionLST q))
        (Data.Product.Base.proj₁ splitSuffix)

    exponentFieldEq :
      Succ.successorWord (Source.exponentLST p) ≡ Source.exponentLST q
    exponentFieldEq =
      sameLengthToListInjective
        (Succ.successorWord (Source.exponentLST p))
        (Source.exponentLST q)
        (Data.Product.Base.proj₂ splitPrefix)

... | Carry.regimeStops fractionMax exponentMax regimeCarry =
  regimeBranch
  where
  wholeEq :
    ((Vec.toList (Carry.allNegative (Regime.fractionCount (8 + extra) r))
      List.++ Vec.toList (Carry.allNegative (Regime.exponentCount r)))
      List.++ Vec.toList (Succ.successorWord (RegimeStep.regimeLST r)))
    ≡ AnchorList.parsedAnchorList q
  wholeEq =
    trans
      (sym (regimeCarryList p fractionMax exponentMax regimeCarry))
      (adjacentParsedLists left right leftParse rightParse anchorStep)

  splitSuffix =
    appendSuffixSplit
      (Vec.toList (Carry.allNegative (Regime.fractionCount (8 + extra) r))
        List.++ Vec.toList (Carry.allNegative (Regime.exponentCount r)))
      (Vec.toList (Succ.successorWord (RegimeStep.regimeLST r)))
      (Vec.toList (Source.fractionLST q)
        List.++ Vec.toList (Source.exponentLST q))
      (Vec.toList (RegimeStep.regimeLST s))
      (sameVectorListLength
        (Succ.successorWord (RegimeStep.regimeLST r))
        (RegimeStep.regimeLST s))
      wholeEq

  regimeWordEq :
    Succ.successorWord (RegimeStep.regimeLST r) ≡ RegimeStep.regimeLST s
  regimeWordEq =
    sameLengthToListInjective
      (Succ.successorWord (RegimeStep.regimeLST r))
      (RegimeStep.regimeLST s)
      (Data.Product.Base.proj₂ splitSuffix)

  regimeBranch : Order.PositiveAdjacentOrder p q
  regimeBranch with regimeSuccessorFromParsedEquality regimeWordEq
  ... | parsedRegimeSuccessor step nextEq =
    Order.regimeStops (regimeStepExponentStrict p q step nextEq)

... | Carry.terminalMaximum fractionMax exponentMax regimeMax =
  ⊥-elim (validRegimeNotAllPositive r regimeMax)
