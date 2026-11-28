module DASHI.Mathematics.Complexity.PNPCookFlattenedPrefixExact where

-- The actual CNF grammar has one terminal TRUE, not one per window.
-- A body prefix contains AND and clause tokens but NO terminal TRUE.
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Nat.Properties as N
import Data.Fin.Base as Fin
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as P
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as B
import DASHI.Mathematics.Complexity.CNFCookPrefixTokenExact as T
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitExact as Stream
import DASHI.Mathematics.Complexity.CanonicalVirtualFormulaBitSourceExact as Lookup
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L

natCount : ∀ n → P.natTokenCount n ≡ suc n
natCount zero = refl
natCount (suc n) = cong suc (natCount n)

literalWidth : ∀ {n} → CNF.Literal n → Nat
literalWidth (CNF.positive i) = suc (suc (Fin.toℕ i))
literalWidth (CNF.negative i) = suc (suc (suc (Fin.toℕ i)))

literalLength : ∀ {n} (l : CNF.Literal n) rest →
  P.listLength (T.literalTokensInto l rest) ≡ literalWidth l + P.listLength rest
literalLength (CNF.positive i) rest
  rewrite P.encodeNatIntoLength (Fin.toℕ i) rest | natCount (Fin.toℕ i) = refl
literalLength (CNF.negative i) rest
  rewrite P.encodeNatIntoLength (Fin.toℕ i) rest | natCount (Fin.toℕ i) = refl

clauseWidth : ∀ {n} → CNF.Clause n → Nat
clauseWidth [] = suc zero
clauseWidth (l ∷ ls) = suc (literalWidth l + clauseWidth ls)

clauseLength : ∀ {n} (c : CNF.Clause n) rest →
  P.listLength (T.clauseTokensInto c rest) ≡ clauseWidth c + P.listLength rest
clauseLength [] rest = refl
clauseLength (l ∷ ls) rest
  rewrite literalLength l (T.clauseTokensInto ls rest) | clauseLength ls rest =
  cong suc (sym (N.+-assoc (literalWidth l) (clauseWidth ls) (P.listLength rest)))

bodyWidth : ∀ {n} → CNF.CNF n → Nat
bodyWidth [] = zero
bodyWidth (c ∷ cs) = suc (clauseWidth c + bodyWidth cs)

bodyInto : ∀ {n} → CNF.CNF n → List P.CookSyntaxToken → List P.CookSyntaxToken
bodyInto [] rest = rest
bodyInto (c ∷ cs) rest = P.formulaAndToken ∷ T.clauseTokensInto c (bodyInto cs rest)

bodyLength : ∀ {n} (f : CNF.CNF n) rest →
  P.listLength (bodyInto f rest) ≡ bodyWidth f + P.listLength rest
bodyLength [] rest = refl
bodyLength (c ∷ cs) rest
  rewrite clauseLength c (bodyInto cs rest) | bodyLength cs rest =
  cong suc (sym (N.+-assoc (clauseWidth c) (bodyWidth cs) (P.listLength rest)))

bodyCompose : ∀ {n} (f g : CNF.CNF n) rest →
  bodyInto (L.append f g) rest ≡ bodyInto f (bodyInto g rest)
bodyCompose [] g rest = refl
bodyCompose (c ∷ cs) g rest rewrite bodyCompose cs g rest = refl

actualTokens : ∀ {n} (f : CNF.CNF n) rest →
  T.cnfTokensInto f rest ≡ bodyInto f (P.formulaTrueToken ∷ rest)
actualTokens [] rest = refl
actualTokens (c ∷ cs) rest rewrite actualTokens cs rest = refl

natAppend : ∀ n xs ys → P.encodeNatInto n (L.append xs ys)
  ≡ L.append (P.encodeNatInto n xs) ys
natAppend zero xs ys = refl
natAppend (suc n) xs ys rewrite natAppend n xs ys = refl

literalAppend : ∀ {n} (l : CNF.Literal n) xs ys →
  T.literalTokensInto l (L.append xs ys) ≡ L.append (T.literalTokensInto l xs) ys
literalAppend (CNF.positive i) xs ys rewrite natAppend (Fin.toℕ i) xs ys = refl
literalAppend (CNF.negative i) xs ys rewrite natAppend (Fin.toℕ i) xs ys = refl

clauseAppend : ∀ {n} (c : CNF.Clause n) xs ys →
  T.clauseTokensInto c (L.append xs ys) ≡ L.append (T.clauseTokensInto c xs) ys
clauseAppend [] xs ys = refl
clauseAppend (l ∷ ls) xs ys rewrite clauseAppend ls xs ys |
  literalAppend l (T.clauseTokensInto ls xs) ys = refl

bodyAppend : ∀ {n} (f : CNF.CNF n) xs ys →
  bodyInto f (L.append xs ys) ≡ L.append (bodyInto f xs) ys
bodyAppend [] xs ys = refl
bodyAppend (c ∷ cs) xs ys rewrite bodyAppend cs xs ys |
  clauseAppend c (bodyInto cs xs) ys = refl

lookupSkip : ∀ (xs ys : List Bool) k →
  Lookup.lookupBit (B.listLength xs + k) (L.append xs ys) ≡ Lookup.lookupBit k ys
lookupSkip [] ys k = refl
lookupSkip (x ∷ xs) ys k = lookupSkip xs ys k

appendAssoc : ∀ {A : Set} (xs ys zs : List A) →
  L.append (L.append xs ys) zs ≡ L.append xs (L.append ys zs)
appendAssoc [] ys zs = refl
appendAssoc (x ∷ xs) ys zs rewrite appendAssoc xs ys zs = refl

-- B.append and L.append are extensionally identical.
appendSame : ∀ {A : Set} (xs ys : List A) → B.append xs ys ≡ L.append xs ys
appendSame [] ys = refl
appendSame (x ∷ xs) ys rewrite appendSame xs ys = refl

binaryAppend : ∀ (xs ys : List P.CookSyntaxToken) →
  B.encodeTokenStream (L.append xs ys)
  ≡ L.append (B.encodeTokenStream xs) (B.encodeTokenStream ys)
binaryAppend [] ys = refl
binaryAppend (x ∷ xs) ys
  rewrite binaryAppend xs ys
        | appendSame (B.tokenBits x) (L.append (B.encodeTokenStream xs) (B.encodeTokenStream ys))
        | appendSame (B.tokenBits x) (B.encodeTokenStream xs) =
  sym (appendAssoc (B.tokenBits x) (B.encodeTokenStream xs) (B.encodeTokenStream ys))

-- Actual serialized bit at an exact body boundary. Neither side duplicates
-- the final TRUE. This is the flattened-stream receiver for arithmetic sums.
prefixBitExact : ∀ {n} (f g : CNF.CNF n) k →
  Lookup.lookupBit (3 * bodyWidth f + k) (T.cnfTokenBits (L.append f g))
  ≡ Lookup.lookupBit k (T.cnfTokenBits g)
prefixBitExact f g k
  rewrite actualTokens (L.append f g) [] | bodyCompose f g (P.formulaTrueToken ∷ [])
        | actualTokens g []
        | bodyAppend f [] (bodyInto g (P.formulaTrueToken ∷ []))
        | binaryAppend (bodyInto f []) (bodyInto g (P.formulaTrueToken ∷ []))
        = transport
  where
    prefix = B.encodeTokenStream (bodyInto f [])
    suffix = B.encodeTokenStream (bodyInto g (P.formulaTrueToken ∷ []))
    lengthExact : B.listLength prefix ≡ 3 * bodyWidth f
    lengthExact rewrite B.encodeTokenStreamLength (bodyInto f []) | bodyLength f [] |
      N.+-identityʳ (bodyWidth f) = refl
    transport : Lookup.lookupBit (3 * bodyWidth f + k) (L.append prefix suffix)
      ≡ Lookup.lookupBit k suffix
    transport rewrite sym lengthExact = lookupSkip prefix suffix k


bodyWidthAppend : ∀ {n} (f g : CNF.CNF n) →
  bodyWidth (L.append f g) ≡ bodyWidth f + bodyWidth g
bodyWidthAppend [] g = refl
bodyWidthAppend (c ∷ cs) g rewrite bodyWidthAppend cs g =
  cong suc (sym (N.+-assoc (clauseWidth c) (bodyWidth cs) (bodyWidth g)))

-- Actual global-stream consumer, rather than a second encoding.
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitFrontier as Cursor
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed

placedAppendSame : ∀ {A : Set} (xs ys : List A) → Placed.append xs ys ≡ L.append xs ys
placedAppendSame [] ys = refl
placedAppendSame (x ∷ xs) ys rewrite placedAppendSame xs ys = refl

streamedAtSplit :
  ∀ {machine : L.ConcreteTapeMachine}
  (sc : Canonical.EnumerationCoverage (L.finiteState machine))
  (ac : Canonical.EnumerationCoverage (L.finiteSymbol machine))
  (nonempty : Selector.NonemptyRuleTable machine)
  (steps cols : Nat)
  (initial : CNF.Bits (Decode.RowBitsWidth machine cols))
  (f g : CNF.CNF (Endpoint.ExtendedGlobalWidth machine steps cols))
  (k : Nat) →
  Global.globalCookLevinCNF sc ac nonempty steps cols initial ≡ L.append f g →
  Cursor.streamedCookBit sc ac nonempty steps cols initial (3 * bodyWidth f + k)
    ≡ Lookup.lookupBit k (T.cnfTokenBits g)
streamedAtSplit sc ac nonempty steps cols initial f g k split
  rewrite Stream.streamedCookBitExact sc ac nonempty steps cols initial (3 * bodyWidth f + k)
    | split | sym (T.cnfTokenBitsExact (L.append f g)) =
  prefixBitExact f g k

transitionSectionSplit :
  ∀ {machine : L.ConcreteTapeMachine}
  (sc : Canonical.EnumerationCoverage (L.finiteState machine))
  (ac : Canonical.EnumerationCoverage (L.finiteSymbol machine))
  (nonempty : Selector.NonemptyRuleTable machine)
  (steps cols : Nat)
  (initial : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Global.globalCookLevinCNF sc ac nonempty steps cols initial ≡
  L.append (Global.liftTransitionCNF sc ac nonempty steps cols)
    (Placed.append (Endpoint.initialEndpointCNF {steps = steps} initial)
      (Endpoint.acceptingEndpointCNF {steps = steps} {cols = cols} sc ac))
transitionSectionSplit sc ac nonempty steps cols initial =
  placedAppendSame (Global.liftTransitionCNF sc ac nonempty steps cols)
    (Placed.append (Endpoint.initialEndpointCNF {steps = steps} initial)
      (Endpoint.acceptingEndpointCNF {steps = steps} {cols = cols} sc ac))

-- Closed form arithmetic is attached below the same actual CNF prefix.
-- The remaining layout-specific equality is the affine length of each
-- placed local rejected-row block, including renaming order.
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

tri : Nat → Nat
tri zero = zero
tri (suc n) = tri n + n

linearSum : Nat → Nat → Nat → Nat
linearSum a c zero = zero
linearSum a c (suc n) = linearSum a c n + (a * n + c)

linearSumExact : ∀ a c n → linearSum a c n ≡ a * tri n + c * n
linearSumExact a c zero =
  solve 2 (λ a c → con 0 := a :* con 0 :+ c :* con 0) refl a c
linearSumExact a c (suc n) rewrite linearSumExact a c n =
  solve 4 (λ a c n t →
    (a :* t :+ c :* n) :+ (a :* n :+ c) :=
    a :* (t :+ n) :+ c :* (con 1 :+ n)) refl a c n (tri n)

rowSum : Nat → Nat → Nat → Nat → Nat → Nat
rowSum a b c t j = linearSum b (a * t + c) j

rectangleSum : Nat → Nat → Nat → Nat → Nat → Nat
rectangleSum a b c J zero = zero
rectangleSum a b c J (suc t) = rectangleSum a b c J t + rowSum a b c t J

rectangleExact : ∀ a b c J t →
  rectangleSum a b c J t ≡ J * (a * tri t + c * t) + b * t * tri J
rectangleExact a b c J zero =
  solve 5 (λ a b c J u → con 0 :=
    J :* (a :* con 0 :+ c :* con 0) :+ b :* con 0 :* u) refl a b c J (tri J)
rectangleExact a b c J (suc t)
  rewrite rectangleExact a b c J t | linearSumExact b (a * t + c) J =
  solve 7 (λ a b c J t u v →
    (J :* (a :* u :+ c :* t) :+ b :* t :* v) :+
    (b :* v :+ (a :* t :+ c) :* J) :=
    J :* (a :* (u :+ t) :+ c :* (con 1 :+ t)) :+
    b :* (con 1 :+ t) :* v) refl a b c J t (tri t) (tri J)
