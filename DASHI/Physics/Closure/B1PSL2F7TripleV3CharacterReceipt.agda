module DASHI.Physics.Closure.B1PSL2F7TripleV3CharacterReceipt where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _+_; _*_; _-_)
open import Data.List.Base using (List; _∷_; [])

infixl 6 _+α_
infixl 7 _*α_

------------------------------------------------------------------------
-- B1 PSL(2,F7) finite character computation.
--
-- The 3-dimensional character has values
--   [3,-1,0,1,α,β]
-- on classes [1A,2A,3A,4A,7A,7B], with β = -1 - α and
-- α² = -α - 2.  The full class-size weighted numerator is
--
--   1*3^3 + 21*(-1)^3 + 56*0^3 + 42*1^3
--     + 24*α^3 + 24*β^3
--   = 168.
--
-- Dividing by |PSL(2,F7)| = 168 gives
--   < V3 tensor V3 tensor V3 , V1 > = 1.

data PSL2F7Class : Set where
  oneA twoA threeA fourA sevenA sevenB :
    PSL2F7Class

canonicalClasses :
  List PSL2F7Class
canonicalClasses =
  oneA ∷ twoA ∷ threeA ∷ fourA ∷ sevenA ∷ sevenB ∷ []

record Qα : Set where
  constructor qα
  field
    rationalPart :
      ℤ

    alphaPart :
      ℤ

open Qα public

zeroQα :
  Qα
zeroQα =
  qα (+ 0) (+ 0)

oneQα :
  Qα
oneQα =
  qα (+ 1) (+ 0)

fromInteger :
  ℤ →
  Qα
fromInteger n =
  qα n (+ 0)

alpha :
  Qα
alpha =
  qα (+ 0) (+ 1)

beta :
  Qα
beta =
  qα (-[1+ 0 ]) (-[1+ 0 ])

_+α_ :
  Qα →
  Qα →
  Qα
qα r s +α qα u v =
  qα (r ℤ.+ u) (s ℤ.+ v)

_*α_ :
  Qα →
  Qα →
  Qα
qα r s *α qα u v =
  qα
    ((r ℤ.* u) ℤ.- ((+ 2) ℤ.* (s ℤ.* v)))
    (((r ℤ.* v) ℤ.+ (s ℤ.* u)) ℤ.- (s ℤ.* v))

scaleα :
  Nat →
  Qα →
  Qα
scaleα n x =
  fromInteger (+ n) *α x

cubeα :
  Qα →
  Qα
cubeα x =
  x *α x *α x

classSize :
  PSL2F7Class →
  Nat
classSize oneA =
  1
classSize twoA =
  21
classSize threeA =
  56
classSize fourA =
  42
classSize sevenA =
  24
classSize sevenB =
  24

chiV1 :
  PSL2F7Class →
  Qα
chiV1 _ =
  oneQα

chiV3 :
  PSL2F7Class →
  Qα
chiV3 oneA =
  fromInteger (+ 3)
chiV3 twoA =
  fromInteger (-[1+ 0 ])
chiV3 threeA =
  zeroQα
chiV3 fourA =
  oneQα
chiV3 sevenA =
  alpha
chiV3 sevenB =
  beta

tripleV3Character :
  PSL2F7Class →
  Qα
tripleV3Character c =
  cubeα (chiV3 c)

tripleV3AgainstV1WeightedTerm :
  PSL2F7Class →
  Qα
tripleV3AgainstV1WeightedTerm c =
  scaleα (classSize c) (tripleV3Character c *α chiV1 c)

sumClassTerms :
  List PSL2F7Class →
  Qα
sumClassTerms [] =
  zeroQα
sumClassTerms (c ∷ cs) =
  tripleV3AgainstV1WeightedTerm c +α sumClassTerms cs

tripleV3V1InnerProductNumerator :
  Qα
tripleV3V1InnerProductNumerator =
  sumClassTerms canonicalClasses

groupOrder :
  Nat
groupOrder =
  168

tripleV3V1InnerProductMultiplicity :
  Nat
tripleV3V1InnerProductMultiplicity =
  1

alphaSquaredLaw :
  alpha *α alpha ≡ qα (-[1+ 1 ]) (-[1+ 0 ])
alphaSquaredLaw =
  refl

betaIsConjugateAlpha :
  beta ≡ qα (-[1+ 0 ]) (-[1+ 0 ])
betaIsConjugateAlpha =
  refl

sevenClassCubeSum :
  cubeα alpha +α cubeα beta ≡ fromInteger (+ 5)
sevenClassCubeSum =
  refl

weightedOneAContribution :
  tripleV3AgainstV1WeightedTerm oneA ≡ fromInteger (+ 27)
weightedOneAContribution =
  refl

weightedTwoAContribution :
  tripleV3AgainstV1WeightedTerm twoA ≡ fromInteger (-[1+ 20 ])
weightedTwoAContribution =
  refl

weightedThreeAContribution :
  tripleV3AgainstV1WeightedTerm threeA ≡ zeroQα
weightedThreeAContribution =
  refl

weightedFourAContribution :
  tripleV3AgainstV1WeightedTerm fourA ≡ fromInteger (+ 42)
weightedFourAContribution =
  refl

weightedSevenAContribution :
  tripleV3AgainstV1WeightedTerm sevenA ≡ qα (+ 48) (-[1+ 23 ])
weightedSevenAContribution =
  refl

weightedSevenBContribution :
  tripleV3AgainstV1WeightedTerm sevenB ≡ qα (+ 72) (+ 24)
weightedSevenBContribution =
  refl

tripleV3V1NumeratorIsGroupOrder :
  tripleV3V1InnerProductNumerator ≡ fromInteger (+ groupOrder)
tripleV3V1NumeratorIsGroupOrder =
  refl

tripleV3V1MultiplicityIsOne :
  tripleV3V1InnerProductMultiplicity ≡ 1
tripleV3V1MultiplicityIsOne =
  refl

innerProductStatement :
  String
innerProductStatement =
  "<V3 tensor V3 tensor V3, V1> for PSL(2,F7) is 1 by the full class-character inner product numerator 168 over group order 168."

record B1PSL2F7TripleV3CharacterReceipt : Set where
  field
    classes :
      List PSL2F7Class

    classesAreCanonical :
      classes ≡ canonicalClasses

    order :
      Nat

    orderIsOneSixtyEight :
      order ≡ 168

    numerator :
      Qα

    numeratorIsOneSixtyEight :
      numerator ≡ fromInteger (+ 168)

    denominator :
      Nat

    denominatorIsGroupOrder :
      denominator ≡ groupOrder

    normalizedMultiplicity :
      Nat

    normalizedMultiplicityIsOne :
      normalizedMultiplicity ≡ 1

    fullCharacterInnerProductComputed :
      numerator ≡ fromInteger (+ denominator)

    statement :
      String

    statementIsCanonical :
      statement ≡ innerProductStatement

open B1PSL2F7TripleV3CharacterReceipt public

canonicalB1PSL2F7TripleV3CharacterReceipt :
  B1PSL2F7TripleV3CharacterReceipt
canonicalB1PSL2F7TripleV3CharacterReceipt =
  record
    { classes =
        canonicalClasses
    ; classesAreCanonical =
        refl
    ; order =
        groupOrder
    ; orderIsOneSixtyEight =
        refl
    ; numerator =
        tripleV3V1InnerProductNumerator
    ; numeratorIsOneSixtyEight =
        tripleV3V1NumeratorIsGroupOrder
    ; denominator =
        groupOrder
    ; denominatorIsGroupOrder =
        refl
    ; normalizedMultiplicity =
        tripleV3V1InnerProductMultiplicity
    ; normalizedMultiplicityIsOne =
        refl
    ; fullCharacterInnerProductComputed =
        tripleV3V1NumeratorIsGroupOrder
    ; statement =
        innerProductStatement
    ; statementIsCanonical =
        refl
    }

B1TripleV3CharacterInnerProductIsOne :
  normalizedMultiplicity canonicalB1PSL2F7TripleV3CharacterReceipt ≡ 1
B1TripleV3CharacterInnerProductIsOne =
  refl
