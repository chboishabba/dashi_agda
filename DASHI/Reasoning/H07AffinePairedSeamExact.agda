module DASHI.Reasoning.H07AffinePairedSeamExact where

-- Selected literal nonzero-correction overlap of the original affine atlas:
-- direction span(e0+e2,e1+e4), marks 01 and 24 (midpoint 3).
-- Source-written, pending kernel. No universal atlas or physical-wave claim.

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_)
import DASHI.Codec.IndexedCubeMarkedAffine9Exact as A
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Reasoning.TypedHyperfabricCore as F
import DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact as G
import DASHI.Reasoning.RelationalBranchCobordismGeometry as P
import DASHI.Physics.ShiftPhaseTableInterference as Phase
import DASHI.Physics.ShiftDiscreteWaveStep as Wave

Offset : Set
Offset = M.Triple Trit

ones : Offset
ones = M.triple pos pos pos

correctionUnit : Offset
correctionUnit = M.triple pos pos zer

-- Coordinate order of source complement is (2,3,4);
-- target complement is (0,1,3). Both pivots are admissible.
toQ : Offset → Offset
toQ (M.triple a b c) = M.triple (A.mul3 neg a) (A.mul3 neg c) b

nativeShift : Trit → Offset → Offset
nativeShift n x = A.addTriple x (A.scaleTriple n ones)

seamCorrection : Trit → Offset
seamCorrection n = A.scaleTriple n correctionUnit

correctedEquality : (n : Trit) (x : Offset) →
  A.addTriple (nativeShift n (toQ x)) (seamCorrection n)
  ≡ toQ (nativeShift n x)
correctedEquality neg (M.triple neg neg neg) = refl
correctedEquality neg (M.triple neg neg zer) = refl
correctedEquality neg (M.triple neg neg pos) = refl
correctedEquality neg (M.triple neg zer neg) = refl
correctedEquality neg (M.triple neg zer zer) = refl
correctedEquality neg (M.triple neg zer pos) = refl
correctedEquality neg (M.triple neg pos neg) = refl
correctedEquality neg (M.triple neg pos zer) = refl
correctedEquality neg (M.triple neg pos pos) = refl
correctedEquality neg (M.triple zer neg neg) = refl
correctedEquality neg (M.triple zer neg zer) = refl
correctedEquality neg (M.triple zer neg pos) = refl
correctedEquality neg (M.triple zer zer neg) = refl
correctedEquality neg (M.triple zer zer zer) = refl
correctedEquality neg (M.triple zer zer pos) = refl
correctedEquality neg (M.triple zer pos neg) = refl
correctedEquality neg (M.triple zer pos zer) = refl
correctedEquality neg (M.triple zer pos pos) = refl
correctedEquality neg (M.triple pos neg neg) = refl
correctedEquality neg (M.triple pos neg zer) = refl
correctedEquality neg (M.triple pos neg pos) = refl
correctedEquality neg (M.triple pos zer neg) = refl
correctedEquality neg (M.triple pos zer zer) = refl
correctedEquality neg (M.triple pos zer pos) = refl
correctedEquality neg (M.triple pos pos neg) = refl
correctedEquality neg (M.triple pos pos zer) = refl
correctedEquality neg (M.triple pos pos pos) = refl
correctedEquality zer (M.triple neg neg neg) = refl
correctedEquality zer (M.triple neg neg zer) = refl
correctedEquality zer (M.triple neg neg pos) = refl
correctedEquality zer (M.triple neg zer neg) = refl
correctedEquality zer (M.triple neg zer zer) = refl
correctedEquality zer (M.triple neg zer pos) = refl
correctedEquality zer (M.triple neg pos neg) = refl
correctedEquality zer (M.triple neg pos zer) = refl
correctedEquality zer (M.triple neg pos pos) = refl
correctedEquality zer (M.triple zer neg neg) = refl
correctedEquality zer (M.triple zer neg zer) = refl
correctedEquality zer (M.triple zer neg pos) = refl
correctedEquality zer (M.triple zer zer neg) = refl
correctedEquality zer (M.triple zer zer zer) = refl
correctedEquality zer (M.triple zer zer pos) = refl
correctedEquality zer (M.triple zer pos neg) = refl
correctedEquality zer (M.triple zer pos zer) = refl
correctedEquality zer (M.triple zer pos pos) = refl
correctedEquality zer (M.triple pos neg neg) = refl
correctedEquality zer (M.triple pos neg zer) = refl
correctedEquality zer (M.triple pos neg pos) = refl
correctedEquality zer (M.triple pos zer neg) = refl
correctedEquality zer (M.triple pos zer zer) = refl
correctedEquality zer (M.triple pos zer pos) = refl
correctedEquality zer (M.triple pos pos neg) = refl
correctedEquality zer (M.triple pos pos zer) = refl
correctedEquality zer (M.triple pos pos pos) = refl
correctedEquality pos (M.triple neg neg neg) = refl
correctedEquality pos (M.triple neg neg zer) = refl
correctedEquality pos (M.triple neg neg pos) = refl
correctedEquality pos (M.triple neg zer neg) = refl
correctedEquality pos (M.triple neg zer zer) = refl
correctedEquality pos (M.triple neg zer pos) = refl
correctedEquality pos (M.triple neg pos neg) = refl
correctedEquality pos (M.triple neg pos zer) = refl
correctedEquality pos (M.triple neg pos pos) = refl
correctedEquality pos (M.triple zer neg neg) = refl
correctedEquality pos (M.triple zer neg zer) = refl
correctedEquality pos (M.triple zer neg pos) = refl
correctedEquality pos (M.triple zer zer neg) = refl
correctedEquality pos (M.triple zer zer zer) = refl
correctedEquality pos (M.triple zer zer pos) = refl
correctedEquality pos (M.triple zer pos neg) = refl
correctedEquality pos (M.triple zer pos zer) = refl
correctedEquality pos (M.triple zer pos pos) = refl
correctedEquality pos (M.triple pos neg neg) = refl
correctedEquality pos (M.triple pos neg zer) = refl
correctedEquality pos (M.triple pos neg pos) = refl
correctedEquality pos (M.triple pos zer neg) = refl
correctedEquality pos (M.triple pos zer zer) = refl
correctedEquality pos (M.triple pos zer pos) = refl
correctedEquality pos (M.triple pos pos neg) = refl
correctedEquality pos (M.triple pos pos zer) = refl
correctedEquality pos (M.triple pos pos pos) = refl

-- Historical indices are independent, not collapsed to a residue modulo 3.
-- The C3 residue and supplied Phase4 boundary phase are NOT identified.
record Context : Set where
  constructor context
  field
    history : List String
    time depth iteration version : Nat
    phase4 : Phase.Phase4
    integerWinding : ℤ

record LeftLocal : Set where
  constructor leftLocal
  field
    baseOffset : Offset
    windingResidue : Trit
    metadata : Context

record RightLocal : Set where
  constructor rightLocal
  field
    localTranslated : Offset
    retainedCorrection : Offset
    rightWinding : Trit
    rightContext : Context

record SeamValue : Set where
  constructor seamValue
  field
    normalized : Offset
    correction : Offset
    residue : Trit
    seamContext : Context

leftRestrict : LeftLocal → SeamValue
leftRestrict (leftLocal x n k) =
  seamValue (toQ (nativeShift n x)) (seamCorrection n) n k

makeRight : LeftLocal → RightLocal
makeRight (leftLocal x n k) =
  rightLocal (nativeShift n (toQ x)) (seamCorrection n) n k

rightRestrict : RightLocal → SeamValue
rightRestrict (rightLocal y r n k) =
  seamValue (A.addTriple y r) r n k

rightAgreement : (s : LeftLocal) →
  rightRestrict (makeRight s) ≡ leftRestrict s
rightAgreement (leftLocal x n k) =
  cong (λ y → seamValue y (seamCorrection n) n k) (correctedEquality n x)

-- The shared stalk is a full selected quotient coordinate, with correction,
-- winding and metadata retained. Unlike an empty-incidence witness, the
-- two chart vertices are actually incident to the same shared edge.
data Vertex : Set where
  chart01 chart24 : Vertex

data Edge : Set where
  leftBoundary rightBoundary sharedSeam : Edge

data Incidence : Vertex → Edge → Set where
  leftBound : Incidence chart01 leftBoundary
  rightBound : Incidence chart24 rightBoundary
  leftShared : Incidence chart01 sharedSeam
  rightShared : Incidence chart24 sharedSeam

localStalk : Vertex → Set
localStalk chart01 = LeftLocal
localStalk chart24 = RightLocal

restriction : ∀ {v e} → Incidence v e → localStalk v → SeamValue
restriction leftBound = leftRestrict
restriction rightBound = rightRestrict
restriction leftShared = leftRestrict
restriction rightShared = rightRestrict

edgeLabel : Edge → String
edgeLabel leftBoundary = "chart 01 boundary"
edgeLabel rightBoundary = "chart 24 boundary"
edgeLabel sharedSeam = "common normalized 24 quotient"

fabric : F.TypedHyperfabric Vertex Edge
fabric = record
  { vertexStalk = localStalk
  ; edgeStalk = λ _ → SeamValue
  ; incidence = Incidence
  ; restrict = restriction
  ; edgeProvenance = λ e → edgeLabel e ∷ "paired midpoint 3" ∷ []
  ; edgeSalience = λ _ → 9
  ; fabricLabel = "H07 selected affine plane seam"
  }

section : LeftLocal → F.GlobalSection fabric
section s = record
  { vertexValue = λ { chart01 → s ; chart24 → makeRight s }
  ; edgeValue = λ
      { leftBoundary → leftRestrict s
      ; rightBoundary → rightRestrict (makeRight s)
      ; sharedSeam → leftRestrict s }
  ; compatible = λ
      { leftBound → refl
      ; rightBound → refl
      ; leftShared → refl
      ; rightShared → rightAgreement s }
  ; sectionReceipt = "corrected signed affine restriction, nonempty incidence"
  }

-- Explicit domain interpretation: the selected proposition is equality
-- of normalized affine offset on the fixed direction; capacity counts
-- its nine points; admissible pivots are open. Wave is a signed radix
-- observer, NOT a physical wave or a C3-to-C4 phase conversion.
signed : Trit → ℤ
signed neg = -[1+ 0 ]
signed zer = + 0
signed pos = + 1

offsetWave : Offset → Wave.DiscreteWave
offsetWave (M.triple a b c) =
  Wave.mkDiscreteWave
    (signed a +ℤ signed b +ℤ signed b +ℤ signed b) (signed c)

channel : Edge → SeamValue → P.BranchChannel
channel e (seamValue x r n k) =
  P.branchChannel
    (P.boundaryInterface (edgeLabel e)
      "selected affine plane offset" "H07 fixed direction" 9
      (Context.phase4 k) true (edgeLabel e ∷ []))
    (offsetWave x) "normalized chart 24"
    "signed radix observation; original correction and context remain in stalk"

matchChannels : (l r : SeamValue) → l ≡ r →
  P.InterfaceMatch (channel leftBoundary l) (channel rightBoundary r)
matchChannels (seamValue x c n k) .(seamValue x c n k) refl =
  P.interfaceMatch refl refl refl refl refl

gluing : (s : LeftLocal) → G.HyperfabricPantsGluing (section s)
gluing s = G.hyperfabric-pants-gluing
  leftBoundary rightBoundary channel
  (matchChannels (leftRestrict s) (rightRestrict (makeRight s))
    (sym (rightAgreement s)))
  "actual shared restriction and all five selected finite interface fields"

-- Concrete nonzero example. Raw local q offset is (1,1,1);
-- physical normalized offset is (-1,-1,1), residual (1,1,0).
exampleContext : Context
exampleContext = context ("01-to-24" ∷ []) 0 0 0 0 Phase.φ0 (+ 1)

exampleLeft : LeftLocal
exampleLeft = leftLocal (M.triple zer zer zer) pos exampleContext

nonzeroCorrection : RightLocal.retainedCorrection (makeRight exampleLeft)
  ≡ M.triple pos pos zer
nonzeroCorrection = refl

rawWaveMismatch :
  offsetWave (RightLocal.localTranslated (makeRight exampleLeft))
  ≡ offsetWave (SeamValue.normalized (leftRestrict exampleLeft)) → ⊥
rawWaveMismatch ()

exampleGluing : G.HyperfabricPantsGluing (section exampleLeft)
exampleGluing = gluing exampleLeft

-- Context.integerWinding is retained metadata; its congruence with the
-- supplied residue is a separate upstream contract, not proved here.
-- Full atlas indexing and original six-face restriction attachment open.
