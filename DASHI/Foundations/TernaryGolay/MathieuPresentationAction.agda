module DASHI.Foundations.TernaryGolay.MathieuPresentationAction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

open import Base369 using
  ( TriTruth ; tri-low ; tri-mid ; tri-high )
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.Base369TriTruthField as F3
import DASHI.Foundations.TernaryGolay.CodeBoundary as Boundary
import DASHI.Foundations.TernaryGolay.ExplicitCode729 as Explicit
import DASHI.Foundations.TernaryGolay.MathieuSourceAtlas as Sources
import DASHI.Foundations.TernaryGolay.SourceAtlas as BaseSources
import DASHI.Foundations.TernaryGolay.SmallWittHexadCount as SmallWitt

data Coordinate12 : Set where
  c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Coordinate12

coordinateEq : Coordinate12 → Coordinate12 → Bool
coordinateEq c0 c0 = true
coordinateEq c1 c1 = true
coordinateEq c2 c2 = true
coordinateEq c3 c3 = true
coordinateEq c4 c4 = true
coordinateEq c5 c5 = true
coordinateEq c6 c6 = true
coordinateEq c7 c7 = true
coordinateEq c8 c8 = true
coordinateEq c9 c9 = true
coordinateEq c10 c10 = true
coordinateEq c11 c11 = true
coordinateEq _ _ = false

record Permutation12 : Set where
  constructor permutation12
  field
    forward : Coordinate12 → Coordinate12
    backward : Coordinate12 → Coordinate12
    backwardForward : (coordinate : Coordinate12) →
      backward (forward coordinate) ≡ coordinate
    forwardBackward : (coordinate : Coordinate12) →
      forward (backward coordinate) ≡ coordinate

open Permutation12 public

lookup12 : ∀ {A : Set} → Boundary.Vec12 A → Coordinate12 → A
lookup12 vector c0 = Boundary.e0 vector
lookup12 vector c1 = Boundary.e1 vector
lookup12 vector c2 = Boundary.e2 vector
lookup12 vector c3 = Boundary.e3 vector
lookup12 vector c4 = Boundary.e4 vector
lookup12 vector c5 = Boundary.e5 vector
lookup12 vector c6 = Boundary.e6 vector
lookup12 vector c7 = Boundary.e7 vector
lookup12 vector c8 = Boundary.e8 vector
lookup12 vector c9 = Boundary.e9 vector
lookup12 vector c10 = Boundary.e10 vector
lookup12 vector c11 = Boundary.e11 vector

tabulate12 : ∀ {A : Set} → (Coordinate12 → A) → Boundary.Vec12 A
tabulate12 f =
  Boundary.vec12
    (f c0) (f c1) (f c2) (f c3) (f c4) (f c5)
    (f c6) (f c7) (f c8) (f c9) (f c10) (f c11)

actVector :
  ∀ {A : Set} →
  Permutation12 →
  Boundary.Vec12 A →
  Boundary.Vec12 A
actVector permutation vector =
  tabulate12
    (λ coordinate →
      lookup12 vector (backward permutation coordinate))

transportForward : Coordinate12 → Coordinate12
transportForward c0 = c0
transportForward c1 = c9
transportForward c2 = c3
transportForward c3 = c1
transportForward c4 = c5
transportForward c5 = c7
transportForward c6 = c2
transportForward c7 = c10
transportForward c8 = c8
transportForward c9 = c11
transportForward c10 = c6
transportForward c11 = c4

transportBackward : Coordinate12 → Coordinate12
transportBackward c0 = c0
transportBackward c1 = c3
transportBackward c2 = c6
transportBackward c3 = c2
transportBackward c4 = c11
transportBackward c5 = c4
transportBackward c6 = c10
transportBackward c7 = c5
transportBackward c8 = c8
transportBackward c9 = c1
transportBackward c10 = c7
transportBackward c11 = c9

transportBackwardForward :
  (coordinate : Coordinate12) →
  transportBackward (transportForward coordinate) ≡ coordinate
transportBackwardForward c0 = refl
transportBackwardForward c1 = refl
transportBackwardForward c2 = refl
transportBackwardForward c3 = refl
transportBackwardForward c4 = refl
transportBackwardForward c5 = refl
transportBackwardForward c6 = refl
transportBackwardForward c7 = refl
transportBackwardForward c8 = refl
transportBackwardForward c9 = refl
transportBackwardForward c10 = refl
transportBackwardForward c11 = refl

transportForwardBackward :
  (coordinate : Coordinate12) →
  transportForward (transportBackward coordinate) ≡ coordinate
transportForwardBackward c0 = refl
transportForwardBackward c1 = refl
transportForwardBackward c2 = refl
transportForwardBackward c3 = refl
transportForwardBackward c4 = refl
transportForwardBackward c5 = refl
transportForwardBackward c6 = refl
transportForwardBackward c7 = refl
transportForwardBackward c8 = refl
transportForwardBackward c9 = refl
transportForwardBackward c10 = refl
transportForwardBackward c11 = refl

coordinateTransport : Permutation12
coordinateTransport =
  permutation12
    transportForward
    transportBackward
    transportBackwardForward
    transportForwardBackward

sForward : Coordinate12 → Coordinate12
sForward c0 = c0
sForward c1 = c5
sForward c2 = c10
sForward c3 = c1
sForward c4 = c9
sForward c5 = c7
sForward c6 = c4
sForward c7 = c2
sForward c8 = c11
sForward c9 = c3
sForward c10 = c8
sForward c11 = c6

sBackward : Coordinate12 → Coordinate12
sBackward c0 = c0
sBackward c1 = c3
sBackward c2 = c7
sBackward c3 = c9
sBackward c4 = c6
sBackward c5 = c1
sBackward c6 = c11
sBackward c7 = c5
sBackward c8 = c10
sBackward c9 = c4
sBackward c10 = c2
sBackward c11 = c8

sBackwardForward :
  (coordinate : Coordinate12) →
  sBackward (sForward coordinate) ≡ coordinate
sBackwardForward c0 = refl
sBackwardForward c1 = refl
sBackwardForward c2 = refl
sBackwardForward c3 = refl
sBackwardForward c4 = refl
sBackwardForward c5 = refl
sBackwardForward c6 = refl
sBackwardForward c7 = refl
sBackwardForward c8 = refl
sBackwardForward c9 = refl
sBackwardForward c10 = refl
sBackwardForward c11 = refl

sForwardBackward :
  (coordinate : Coordinate12) →
  sForward (sBackward coordinate) ≡ coordinate
sForwardBackward c0 = refl
sForwardBackward c1 = refl
sForwardBackward c2 = refl
sForwardBackward c3 = refl
sForwardBackward c4 = refl
sForwardBackward c5 = refl
sForwardBackward c6 = refl
sForwardBackward c7 = refl
sForwardBackward c8 = refl
sForwardBackward c9 = refl
sForwardBackward c10 = refl
sForwardBackward c11 = refl

sPermutation : Permutation12
sPermutation =
  permutation12
    sForward sBackward sBackwardForward sForwardBackward

tForward : Coordinate12 → Coordinate12
tForward c0 = c9
tForward c1 = c5
tForward c2 = c10
tForward c3 = c4
tForward c4 = c3
tForward c5 = c1
tForward c6 = c7
tForward c7 = c6
tForward c8 = c11
tForward c9 = c0
tForward c10 = c2
tForward c11 = c8

tBackward : Coordinate12 → Coordinate12
tBackward = tForward

tBackwardForward :
  (coordinate : Coordinate12) →
  tBackward (tForward coordinate) ≡ coordinate
tBackwardForward c0 = refl
tBackwardForward c1 = refl
tBackwardForward c2 = refl
tBackwardForward c3 = refl
tBackwardForward c4 = refl
tBackwardForward c5 = refl
tBackwardForward c6 = refl
tBackwardForward c7 = refl
tBackwardForward c8 = refl
tBackwardForward c9 = refl
tBackwardForward c10 = refl
tBackwardForward c11 = refl

tForwardBackward :
  (coordinate : Coordinate12) →
  tForward (tBackward coordinate) ≡ coordinate
tForwardBackward = tBackwardForward

tPermutation : Permutation12
tPermutation =
  permutation12
    tForward tBackward tBackwardForward tForwardBackward

actSupport :
  Permutation12 →
  SmallWitt.Support12 →
  SmallWitt.Support12
actSupport = actVector

sPreservesHexad : SmallWitt.Support12 → Bool
sPreservesHexad hexad =
  SmallWitt.memberSupport
    (actSupport sPermutation hexad)
    SmallWitt.hexadSupports

tPreservesHexad : SmallWitt.Support12 → Bool
tPreservesHexad hexad =
  SmallWitt.memberSupport
    (actSupport tPermutation hexad)
    SmallWitt.hexadSupports

sPreservesAllHexadsCheck : Bool
sPreservesAllHexadsCheck =
  Explicit.allList sPreservesHexad SmallWitt.hexadSupports

tPreservesAllHexadsCheck : Bool
tPreservesAllHexadsCheck =
  Explicit.allList tPreservesHexad SmallWitt.hexadSupports

sPreservesAllHexads :
  sPreservesAllHexadsCheck ≡ true
sPreservesAllHexads = refl

tPreservesAllHexads :
  tPreservesAllHexadsCheck ≡ true
tPreservesAllHexads = refl

orbitSeed : SmallWitt.Support12
orbitSeed =
  Boundary.vec12
    true true true true false true
    false false false true false false

closureStep :
  List SmallWitt.Support12 →
  List SmallWitt.Support12
closureStep supports =
  SmallWitt.deduplicateSupports
    (Explicit._++_
      supports
      (Explicit._++_
        (Explicit.map (actSupport sPermutation) supports)
        (Explicit.map (actSupport tPermutation) supports)))

iterate :
  ∀ {A : Set} →
  Nat →
  (A → A) →
  A →
  A
iterate zero step value = value
iterate (suc count) step value =
  iterate count step (step value)

hexadOrbit : List SmallWitt.Support12
hexadOrbit =
  iterate 13 closureStep (orbitSeed ∷ [])

hexadOrbitCountIs132 :
  Explicit.listCount hexadOrbit ≡ 132
hexadOrbitCountIs132 = refl

orbitCoversHexadsCheck : Bool
orbitCoversHexadsCheck =
  Explicit.allList
    (λ hexad →
      SmallWitt.memberSupport hexad hexadOrbit)
    SmallWitt.hexadSupports

orbitCoversAllHexads :
  orbitCoversHexadsCheck ≡ true
orbitCoversAllHexads = refl

one : TriTruth
one = tri-mid

minusOne : TriTruth
minusOne = tri-high

sSigns : Boundary.Word12
sSigns =
  Boundary.vec12
    one one minusOne minusOne one one
    minusOne minusOne minusOne one one minusOne

tSigns : Boundary.Word12
tSigns =
  Boundary.vec12
    one minusOne minusOne one minusOne one
    one minusOne one minusOne one minusOne

scaleWord : Boundary.Word12 → Boundary.Word12 → Boundary.Word12
scaleWord signs word =
  Boundary.vec12
    (F3.triMul (Boundary.e0 signs) (Boundary.e0 word))
    (F3.triMul (Boundary.e1 signs) (Boundary.e1 word))
    (F3.triMul (Boundary.e2 signs) (Boundary.e2 word))
    (F3.triMul (Boundary.e3 signs) (Boundary.e3 word))
    (F3.triMul (Boundary.e4 signs) (Boundary.e4 word))
    (F3.triMul (Boundary.e5 signs) (Boundary.e5 word))
    (F3.triMul (Boundary.e6 signs) (Boundary.e6 word))
    (F3.triMul (Boundary.e7 signs) (Boundary.e7 word))
    (F3.triMul (Boundary.e8 signs) (Boundary.e8 word))
    (F3.triMul (Boundary.e9 signs) (Boundary.e9 word))
    (F3.triMul (Boundary.e10 signs) (Boundary.e10 word))
    (F3.triMul (Boundary.e11 signs) (Boundary.e11 word))

liftS : Boundary.Word12 → Boundary.Word12
liftS word =
  scaleWord sSigns (actVector sPermutation word)

liftT : Boundary.Word12 → Boundary.Word12
liftT word =
  scaleWord tSigns (actVector tPermutation word)

wordEq : Boundary.Word12 → Boundary.Word12 → Bool
wordEq left right =
  Explicit._&&_ (Explicit.triEq (Boundary.e0 left) (Boundary.e0 right))
  (Explicit._&&_ (Explicit.triEq (Boundary.e1 left) (Boundary.e1 right))
  (Explicit._&&_ (Explicit.triEq (Boundary.e2 left) (Boundary.e2 right))
  (Explicit._&&_ (Explicit.triEq (Boundary.e3 left) (Boundary.e3 right))
  (Explicit._&&_ (Explicit.triEq (Boundary.e4 left) (Boundary.e4 right))
  (Explicit._&&_ (Explicit.triEq (Boundary.e5 left) (Boundary.e5 right))
  (Explicit._&&_ (Explicit.triEq (Boundary.e6 left) (Boundary.e6 right))
  (Explicit._&&_ (Explicit.triEq (Boundary.e7 left) (Boundary.e7 right))
  (Explicit._&&_ (Explicit.triEq (Boundary.e8 left) (Boundary.e8 right))
  (Explicit._&&_ (Explicit.triEq (Boundary.e9 left) (Boundary.e9 right))
  (Explicit._&&_ (Explicit.triEq (Boundary.e10 left) (Boundary.e10 right))
                 (Explicit.triEq (Boundary.e11 left) (Boundary.e11 right))))))))))))

isEncodedWord : Boundary.Word12 → Bool
isEncodedWord word =
  wordEq
    (Explicit.encode (Explicit.decodeSystematic word))
    word

liftSPreservesCodeCheck : Bool
liftSPreservesCodeCheck =
  Explicit.allList
    (λ word → isEncodedWord (liftS word))
    Explicit.allCodewords

liftTPreservesCodeCheck : Bool
liftTPreservesCodeCheck =
  Explicit.allList
    (λ word → isEncodedWord (liftT word))
    Explicit.allCodewords

liftSPreservesCode :
  liftSPreservesCodeCheck ≡ true
liftSPreservesCode = refl

liftTPreservesCode :
  liftTPreservesCodeCheck ≡ true
liftTPreservesCode = refl

negateWord : Boundary.Word12 → Boundary.Word12
negateWord word =
  scaleWord
    (Boundary.vec12
      minusOne minusOne minusOne minusOne minusOne minusOne
      minusOne minusOne minusOne minusOne minusOne minusOne)
    word

liftTSquareIsCentralNegationCheck : Bool
liftTSquareIsCentralNegationCheck =
  Explicit.allList
    (λ word →
      wordEq
        (liftT (liftT word))
        (negateWord word))
    Explicit.allCodewords

liftTSquareIsCentralNegation :
  liftTSquareIsCentralNegationCheck ≡ true
liftTSquareIsCentralNegation = refl

centralNegationSquareCheck : Bool
centralNegationSquareCheck =
  Explicit.allList
    (λ word →
      wordEq
        (negateWord (negateWord word))
        word)
    Explicit.allCodewords

centralNegationHasOrderTwo :
  centralNegationSquareCheck ≡ true
centralNegationHasOrderTwo = refl

inducedS : Boundary.Message6 → Boundary.Message6
inducedS message =
  Explicit.decodeSystematic
    (liftS (Explicit.encode message))

inducedT : Boundary.Message6 → Boundary.Message6
inducedT message =
  Explicit.decodeSystematic
    (liftT (Explicit.encode message))

inducedSCommutesCheck : Bool
inducedSCommutesCheck =
  Explicit.allList
    (λ message →
      wordEq
        (Explicit.encode (inducedS message))
        (liftS (Explicit.encode message)))
    Explicit.allMessages

inducedTCommutesCheck : Bool
inducedTCommutesCheck =
  Explicit.allList
    (λ message →
      wordEq
        (Explicit.encode (inducedT message))
        (liftT (Explicit.encode message)))
    Explicit.allMessages

inducedSCommutes :
  inducedSCommutesCheck ≡ true
inducedSCommutes = refl

inducedTCommutes :
  inducedTCommutesCheck ≡ true
inducedTCommutes = refl

record MathieuFiniteActionCertificate : Set where
  constructor mathieuFiniteActionCertificate
  field
    presentationAuthor : String
    presentationTitle : String
    presentationDOI : String
    doubleCoverAuthor : String
    doubleCoverTitle : String
    doubleCoverDOI : String
    coordinateTransportRecorded : Bool
    coordinateTransportRecordedIsTrue :
      coordinateTransportRecorded ≡ true
    sPreservesComputedDesign : sPreservesAllHexadsCheck ≡ true
    tPreservesComputedDesign : tPreservesAllHexadsCheck ≡ true
    generatedHexadOrbitCount : Explicit.listCount hexadOrbit ≡ 132
    generatedOrbitEqualsComputedDesign : orbitCoversHexadsCheck ≡ true
    signedSPreservesCode : liftSPreservesCodeCheck ≡ true
    signedTPreservesCode : liftTPreservesCodeCheck ≡ true
    tLiftSquaresToCentralNegation :
      liftTSquareIsCentralNegationCheck ≡ true
    centralKernelOrderTwo : centralNegationSquareCheck ≡ true
    permutationGroupOrderCheckedByOracle : Nat
    permutationGroupOrderIs95040 :
      permutationGroupOrderCheckedByOracle ≡ 95040
    monomialGroupOrderCheckedByOracle : Nat
    monomialGroupOrderIs190080 :
      monomialGroupOrderCheckedByOracle ≡ 190080
    sixDimensionalActionIrreducibleCheckedByOracle : Bool
    sixDimensionalActionIrreducibleCheckedByOracleIsTrue :
      sixDimensionalActionIrreducibleCheckedByOracle ≡ true
    groupIsomorphismKernelCheckedInAgda : Bool
    groupIsomorphismKernelCheckedInAgdaIsFalse :
      groupIsomorphismKernelCheckedInAgda ≡ false

canonicalMathieuFiniteActionCertificate :
  MathieuFiniteActionCertificate
canonicalMathieuFiniteActionCertificate =
  mathieuFiniteActionCertificate
    (BaseSources.author Sources.leechM12PresentationEntry)
    (BaseSources.title Sources.leechM12PresentationEntry)
    "10.4153/CMB-1969-005-8"
    (BaseSources.author Sources.conwayElkiesMartinEntry)
    (BaseSources.title Sources.conwayElkiesMartinEntry)
    "10.1080/10586458.2006.10128958"
    true refl
    sPreservesAllHexads
    tPreservesAllHexads
    hexadOrbitCountIs132
    orbitCoversAllHexads
    liftSPreservesCode
    liftTPreservesCode
    liftTSquareIsCentralNegation
    centralNegationHasOrderTwo
    95040 refl
    190080 refl
    true refl
    false refl

mathieuFiniteActionReceipt : GenericReceipt.GenericReceipt
mathieuFiniteActionReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "transported M12 design action and signed 2.M12 code lifts"
    "DASHI.Foundations.TernaryGolay.MathieuPresentationAction"
    "canonicalMathieuFiniteActionCertificate"
    "the transported generators preserve the locally computed 132-hexad design, generate its full orbit, admit explicit signed lifts preserving all 729 codewords, and the involutory permutation lift squares to central negation"
    "the dependency-free oracle enumerates permutation order 95040, monomial order 190080 and irreducibility of the induced six-dimensional F3 action; abstract group isomorphism is still an explicit theorem-import and kernel obligation"
    "agda -i . DASHI/Foundations/TernaryGolay/MathieuPresentationAction.agda"

mathieuFiniteActionReceiptNonPromoting :
  GenericReceipt.promotesClaim mathieuFiniteActionReceipt ≡ false
mathieuFiniteActionReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse mathieuFiniteActionReceipt
