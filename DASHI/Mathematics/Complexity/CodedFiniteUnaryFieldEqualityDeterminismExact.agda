module DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityDeterminismExact where

------------------------------------------------------------------------
-- FINITE KEY DETERMINISM FOR THE UNARY FIELD-EQUALITY MICROCODE
--
-- Decode the numeric `(source,read)` key back to the unique finite rule name.
-- Every listed rule round-trips through this decoder, so equal dispatch keys
-- imply equal names and therefore equal literal rules.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityExact as Eq

data RuleName : Set where
  ffMark ffTrue ffEnd : RuleName
  ssTrue ssMark ssEnd : RuleName
  fsMark fsTrue fsEnd : RuleName
  rlTrue rlEnd rlM1 rlM2 rlBlank : RuleName
  csMark csTrue csEnd : RuleName

namedRule :
  RuleName →
  Local.TapeRule (Fin.Fin Eq.stateCount) (Fin.Fin Eq.symbolCount)
namedRule ffMark = Eq.rFFmark
namedRule ffTrue = Eq.rFFtrue
namedRule ffEnd = Eq.rFFend
namedRule ssTrue = Eq.rSStrue
namedRule ssMark = Eq.rSSmark
namedRule ssEnd = Eq.rSSend
namedRule fsMark = Eq.rFSmark
namedRule fsTrue = Eq.rFStrue
namedRule fsEnd = Eq.rFSend
namedRule rlTrue = Eq.rRLtrue
namedRule rlEnd = Eq.rRLend
namedRule rlM1 = Eq.rRLm1
namedRule rlM2 = Eq.rRLm2
namedRule rlBlank = Eq.rRLblank
namedRule csMark = Eq.rCSmark
namedRule csTrue = Eq.rCStrue
namedRule csEnd = Eq.rCSend

allNames : List RuleName
allNames =
  ffMark ∷ ffTrue ∷ ffEnd ∷
  ssTrue ∷ ssMark ∷ ssEnd ∷
  fsMark ∷ fsTrue ∷ fsEnd ∷
  rlTrue ∷ rlEnd ∷ rlM1 ∷ rlM2 ∷ rlBlank ∷
  csMark ∷ csTrue ∷ csEnd ∷ []

mapRules : List RuleName →
  List (Local.TapeRule (Fin.Fin Eq.stateCount) (Fin.Fin Eq.symbolCount))
mapRules [] = []
mapRules (name ∷ rest) = namedRule name ∷ mapRules rest

rulesAreNamed : Eq.rules ≡ mapRules allNames
rulesAreNamed = refl

record NamedOccurrence
    (rule : Local.TapeRule (Fin.Fin Eq.stateCount) (Fin.Fin Eq.symbolCount)) : Set where
  constructor named-occurrence
  field
    name : RuleName
    exact : rule ≡ namedRule name

open NamedOccurrence public

invertNamed :
  ∀ {rule names} →
  Local.RuleOccurs rule (mapRules names) →
  NamedOccurrence rule
invertNamed {names = []} ()
invertNamed {names = name ∷ rest} Local.ruleHere =
  named-occurrence name refl
invertNamed {names = name ∷ rest} (Local.ruleThere occurs) =
  invertNamed occurs

invertRuleOccurrence :
  ∀ {rule} → Local.RuleOccurs rule Eq.rules → NamedOccurrence rule
invertRuleOccurrence occurs
  rewrite rulesAreNamed = invertNamed occurs

sourceIndex : RuleName → Nat
sourceIndex ffMark = 0
sourceIndex ffTrue = 0
sourceIndex ffEnd = 0
sourceIndex ssTrue = 1
sourceIndex ssMark = 1
sourceIndex ssEnd = 1
sourceIndex fsMark = 2
sourceIndex fsTrue = 2
sourceIndex fsEnd = 2
sourceIndex rlTrue = 3
sourceIndex rlEnd = 3
sourceIndex rlM1 = 3
sourceIndex rlM2 = 3
sourceIndex rlBlank = 3
sourceIndex csMark = 4
sourceIndex csTrue = 4
sourceIndex csEnd = 4

readIndex : RuleName → Nat
readIndex ffMark = 3
readIndex ffTrue = 1
readIndex ffEnd = 2
readIndex ssTrue = 1
readIndex ssMark = 3
readIndex ssEnd = 2
readIndex fsMark = 4
readIndex fsTrue = 1
readIndex fsEnd = 2
readIndex rlTrue = 1
readIndex rlEnd = 2
readIndex rlM1 = 3
readIndex rlM2 = 4
readIndex rlBlank = 0
readIndex csMark = 4
readIndex csTrue = 1
readIndex csEnd = 2

sourceIndexExact :
  (name : RuleName) →
  Fin.toℕ (Local.sourceState (namedRule name)) ≡ sourceIndex name
sourceIndexExact ffMark = refl
sourceIndexExact ffTrue = refl
sourceIndexExact ffEnd = refl
sourceIndexExact ssTrue = refl
sourceIndexExact ssMark = refl
sourceIndexExact ssEnd = refl
sourceIndexExact fsMark = refl
sourceIndexExact fsTrue = refl
sourceIndexExact fsEnd = refl
sourceIndexExact rlTrue = refl
sourceIndexExact rlEnd = refl
sourceIndexExact rlM1 = refl
sourceIndexExact rlM2 = refl
sourceIndexExact rlBlank = refl
sourceIndexExact csMark = refl
sourceIndexExact csTrue = refl
sourceIndexExact csEnd = refl

readIndexExact :
  (name : RuleName) →
  Fin.toℕ (Local.readSymbol (namedRule name)) ≡ readIndex name
readIndexExact ffMark = refl
readIndexExact ffTrue = refl
readIndexExact ffEnd = refl
readIndexExact ssTrue = refl
readIndexExact ssMark = refl
readIndexExact ssEnd = refl
readIndexExact fsMark = refl
readIndexExact fsTrue = refl
readIndexExact fsEnd = refl
readIndexExact rlTrue = refl
readIndexExact rlEnd = refl
readIndexExact rlM1 = refl
readIndexExact rlM2 = refl
readIndexExact rlBlank = refl
readIndexExact csMark = refl
readIndexExact csTrue = refl
readIndexExact csEnd = refl

decodeName : Nat → Nat → Maybe RuleName
decodeName 0 3 = just ffMark
decodeName 0 1 = just ffTrue
decodeName 0 2 = just ffEnd
decodeName 1 1 = just ssTrue
decodeName 1 3 = just ssMark
decodeName 1 2 = just ssEnd
decodeName 2 4 = just fsMark
decodeName 2 1 = just fsTrue
decodeName 2 2 = just fsEnd
decodeName 3 1 = just rlTrue
decodeName 3 2 = just rlEnd
decodeName 3 3 = just rlM1
decodeName 3 4 = just rlM2
decodeName 3 0 = just rlBlank
decodeName 4 4 = just csMark
decodeName 4 1 = just csTrue
decodeName 4 2 = just csEnd
decodeName _ _ = nothing

decodeNameRoundTrip :
  (name : RuleName) → decodeName (sourceIndex name) (readIndex name) ≡ just name
decodeNameRoundTrip ffMark = refl
decodeNameRoundTrip ffTrue = refl
decodeNameRoundTrip ffEnd = refl
decodeNameRoundTrip ssTrue = refl
decodeNameRoundTrip ssMark = refl
decodeNameRoundTrip ssEnd = refl
decodeNameRoundTrip fsMark = refl
decodeNameRoundTrip fsTrue = refl
decodeNameRoundTrip fsEnd = refl
decodeNameRoundTrip rlTrue = refl
decodeNameRoundTrip rlEnd = refl
decodeNameRoundTrip rlM1 = refl
decodeNameRoundTrip rlM2 = refl
decodeNameRoundTrip rlBlank = refl
decodeNameRoundTrip csMark = refl
decodeNameRoundTrip csTrue = refl
decodeNameRoundTrip csEnd = refl

cong₂ :
  ∀ {A B C : Set} (f : A → B → C) {a a' : A} {b b' : B} →
  a ≡ a' → b ≡ b' → f a b ≡ f a' b'
cong₂ f refl refl = refl

justInjective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
justInjective refl = refl

nameKeyInjective :
  (left right : RuleName) →
  Local.sourceState (namedRule left) ≡ Local.sourceState (namedRule right) →
  Local.readSymbol (namedRule left) ≡ Local.readSymbol (namedRule right) →
  left ≡ right
nameKeyInjective left right sourceEq readEq =
  justInjective
    (trans
      (sym (decodeNameRoundTrip left))
      (trans
        (cong₂ decodeName sourceNatEq readNatEq)
        (decodeNameRoundTrip right)))
  where
    sourceNatEq : sourceIndex left ≡ sourceIndex right
    sourceNatEq =
      trans
        (sym (sourceIndexExact left))
        (trans (cong Fin.toℕ sourceEq) (sourceIndexExact right))

    readNatEq : readIndex left ≡ readIndex right
    readNatEq =
      trans
        (sym (readIndexExact left))
        (trans (cong Fin.toℕ readEq) (readIndexExact right))

dispatchUnique :
  ∀ {left right} →
  Local.RuleOccurs left Eq.rules →
  Local.RuleOccurs right Eq.rules →
  Local.sourceState left ≡ Local.sourceState right →
  Local.readSymbol left ≡ Local.readSymbol right →
  left ≡ right
dispatchUnique leftOccurs rightOccurs sourceEq readEq
  with invertRuleOccurrence leftOccurs | invertRuleOccurrence rightOccurs
... | named-occurrence leftName refl | named-occurrence rightName refl
  with nameKeyInjective leftName rightName sourceEq readEq
... | refl = refl

equalityCode : Coded.CodedFiniteStandardTM
equalityCode = record
  { Coded.stateCount = Eq.stateCount
  ; Coded.symbolCount = Eq.symbolCount
  ; Coded.blank = Eq.blank
  ; Coded.initialState = Eq.findFirst
  ; Coded.acceptingState = Eq.equalState
  ; Coded.rules = Eq.rules
  ; Coded.dispatchUnique = dispatchUnique
  }

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The literal equality fragment is now an actual coded standard machine with no
-- assumed determinism field. Remaining work is the exact mark/shuttle run
-- theorem and any restoration policy needed by the universal interpreter.
------------------------------------------------------------------------
