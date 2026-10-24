module DASHI.Biology.IITCubeConcreteTorusImageExact where

------------------------------------------------------------------------
-- CONCRETE 3x3x3 TERNARY TORUS IMAGE = TWO-FACE GRAPH
--
-- This is the dynamics payment that was actually missing after the repository's
-- older T^18 / six-T^3-cell structured-boundary roundtrip.  It does NOT claim
-- novelty for 18 coordinates, 27^6 = 3^18, or same-boundary/different-face;
-- those are already owned by TrialecticThreeCellHyperformSynthesisExact.
--
-- One face is the existing exact PhaseFineTable9 (a 3x3 F3 table).  Define
--
--   B = cyclic-row-shift + cyclic-column-shift
--
-- and on three z-layers
--
--   y0 = B u0 + u1
--   y1 = B u1 + u2
--   y2 = B u2 + u0.
--
-- The concrete finite proof below establishes B^3 = -I and then proves
--
--   output is in image(step)  <->  y2 = B y1 - B^2 y0.
--
-- The reverse direction is constructive, using the canonical source
--
--   u0 = 0, u1 = y0, u2 = y1 - B y0.
--
-- Thus the selected cube dynamics has exactly the graph-over-two-faces image;
-- the existing Q9-field weld and mature T^18 trialectic carrier may consume
-- this theorem without another rank/cardinality argument.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Base369 as Base
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Foundations.Base369FiniteRingLaws as Laws

Face9 : Set
Face9 = Fine.PhaseFineTable9

zeroFace : Face9
zeroFace = Fine.phaseFineTable9
  Base.tri-low Base.tri-low Base.tri-low
  Base.tri-low Base.tri-low Base.tri-low
  Base.tri-low Base.tri-low Base.tri-low

addFace : Face9 → Face9 → Face9
addFace a b = Fine.phaseFineTable9
  (Base.triXor (Fine.q00 a) (Fine.q00 b))
  (Base.triXor (Fine.q01 a) (Fine.q01 b))
  (Base.triXor (Fine.q02 a) (Fine.q02 b))
  (Base.triXor (Fine.q10 a) (Fine.q10 b))
  (Base.triXor (Fine.q11 a) (Fine.q11 b))
  (Base.triXor (Fine.q12 a) (Fine.q12 b))
  (Base.triXor (Fine.q20 a) (Fine.q20 b))
  (Base.triXor (Fine.q21 a) (Fine.q21 b))
  (Base.triXor (Fine.q22 a) (Fine.q22 b))

negFace : Face9 → Face9
negFace a = Fine.phaseFineTable9
  (Laws.triTruthNeg (Fine.q00 a))
  (Laws.triTruthNeg (Fine.q01 a))
  (Laws.triTruthNeg (Fine.q02 a))
  (Laws.triTruthNeg (Fine.q10 a))
  (Laws.triTruthNeg (Fine.q11 a))
  (Laws.triTruthNeg (Fine.q12 a))
  (Laws.triTruthNeg (Fine.q20 a))
  (Laws.triTruthNeg (Fine.q21 a))
  (Laws.triTruthNeg (Fine.q22 a))

subFace : Face9 → Face9 → Face9
subFace a b = addFace a (negFace b)

------------------------------------------------------------------------
-- Small scalar group identities.  The finite F3 cases are theorem authority;
-- Python is not used as a proof checker here.
------------------------------------------------------------------------

negNeg : (x : Base.TriTruth) →
  Laws.triTruthNeg (Laws.triTruthNeg x) ≡ x
negNeg Base.tri-low = refl
negNeg Base.tri-mid = refl
negNeg Base.tri-high = refl

negAdd : (x y : Base.TriTruth) →
  Laws.triTruthNeg (Base.triXor x y)
  ≡ Base.triXor (Laws.triTruthNeg x) (Laws.triTruthNeg y)
negAdd Base.tri-low Base.tri-low = refl
negAdd Base.tri-low Base.tri-mid = refl
negAdd Base.tri-low Base.tri-high = refl
negAdd Base.tri-mid Base.tri-low = refl
negAdd Base.tri-mid Base.tri-mid = refl
negAdd Base.tri-mid Base.tri-high = refl
negAdd Base.tri-high Base.tri-low = refl
negAdd Base.tri-high Base.tri-mid = refl
negAdd Base.tri-high Base.tri-high = refl

addSubCancel : (a b : Base.TriTruth) →
  Base.triXor a (Base.triXor b (Laws.triTruthNeg a)) ≡ b
addSubCancel Base.tri-low Base.tri-low = refl
addSubCancel Base.tri-low Base.tri-mid = refl
addSubCancel Base.tri-low Base.tri-high = refl
addSubCancel Base.tri-mid Base.tri-low = refl
addSubCancel Base.tri-mid Base.tri-mid = refl
addSubCancel Base.tri-mid Base.tri-high = refl
addSubCancel Base.tri-high Base.tri-low = refl
addSubCancel Base.tri-high Base.tri-mid = refl
addSubCancel Base.tri-high Base.tri-high = refl

subRearrange : (a b c : Base.TriTruth) →
  Base.triXor
    (Base.triXor a b)
    (Laws.triTruthNeg (Base.triXor c a))
  ≡ Base.triXor b (Laws.triTruthNeg c)
subRearrange Base.tri-low Base.tri-low Base.tri-low = refl
subRearrange Base.tri-low Base.tri-low Base.tri-mid = refl
subRearrange Base.tri-low Base.tri-low Base.tri-high = refl
subRearrange Base.tri-low Base.tri-mid Base.tri-low = refl
subRearrange Base.tri-low Base.tri-mid Base.tri-mid = refl
subRearrange Base.tri-low Base.tri-mid Base.tri-high = refl
subRearrange Base.tri-low Base.tri-high Base.tri-low = refl
subRearrange Base.tri-low Base.tri-high Base.tri-mid = refl
subRearrange Base.tri-low Base.tri-high Base.tri-high = refl
subRearrange Base.tri-mid Base.tri-low Base.tri-low = refl
subRearrange Base.tri-mid Base.tri-low Base.tri-mid = refl
subRearrange Base.tri-mid Base.tri-low Base.tri-high = refl
subRearrange Base.tri-mid Base.tri-mid Base.tri-low = refl
subRearrange Base.tri-mid Base.tri-mid Base.tri-mid = refl
subRearrange Base.tri-mid Base.tri-mid Base.tri-high = refl
subRearrange Base.tri-mid Base.tri-high Base.tri-low = refl
subRearrange Base.tri-mid Base.tri-high Base.tri-mid = refl
subRearrange Base.tri-mid Base.tri-high Base.tri-high = refl
subRearrange Base.tri-high Base.tri-low Base.tri-low = refl
subRearrange Base.tri-high Base.tri-low Base.tri-mid = refl
subRearrange Base.tri-high Base.tri-low Base.tri-high = refl
subRearrange Base.tri-high Base.tri-mid Base.tri-low = refl
subRearrange Base.tri-high Base.tri-mid Base.tri-mid = refl
subRearrange Base.tri-high Base.tri-mid Base.tri-high = refl
subRearrange Base.tri-high Base.tri-high Base.tri-low = refl
subRearrange Base.tri-high Base.tri-high Base.tri-mid = refl
subRearrange Base.tri-high Base.tri-high Base.tri-high = refl

addMedial : (a b c d : Base.TriTruth) →
  Base.triXor (Base.triXor a b) (Base.triXor c d)
  ≡ Base.triXor (Base.triXor a c) (Base.triXor b d)
addMedial a b c d =
  trans
    (sym (Base.triXor-assoc a b (Base.triXor c d)))
    (trans
      (cong (λ t → Base.triXor a t) (Base.triXor-assoc b c d))
      (trans
        (cong
          (λ t → Base.triXor a (Base.triXor t d))
          (Laws.triTruthAddComm b c))
        (trans
          (cong
            (λ t → Base.triXor a t)
            (sym (Base.triXor-assoc c b d)))
          (Base.triXor-assoc a c (Base.triXor b d)))))

------------------------------------------------------------------------
-- Table extensionality and pointwise group laws.
------------------------------------------------------------------------

faceExt : {a b : Face9} →
  Fine.q00 a ≡ Fine.q00 b → Fine.q01 a ≡ Fine.q01 b → Fine.q02 a ≡ Fine.q02 b →
  Fine.q10 a ≡ Fine.q10 b → Fine.q11 a ≡ Fine.q11 b → Fine.q12 a ≡ Fine.q12 b →
  Fine.q20 a ≡ Fine.q20 b → Fine.q21 a ≡ Fine.q21 b → Fine.q22 a ≡ Fine.q22 b →
  a ≡ b
faceExt {Fine.phaseFineTable9 _ _ _ _ _ _ _ _ _}
        {Fine.phaseFineTable9 _ _ _ _ _ _ _ _ _}
        refl refl refl refl refl refl refl refl refl = refl

addZeroLFace : (a : Face9) → addFace zeroFace a ≡ a
addZeroLFace a = faceExt
  (Base.triXor-identityˡ _) (Base.triXor-identityˡ _) (Base.triXor-identityˡ _)
  (Base.triXor-identityˡ _) (Base.triXor-identityˡ _) (Base.triXor-identityˡ _)
  (Base.triXor-identityˡ _) (Base.triXor-identityˡ _) (Base.triXor-identityˡ _)

addZeroRFace : (a : Face9) → addFace a zeroFace ≡ a
addZeroRFace a = faceExt
  (trans (Laws.triTruthAddComm _ _) (Base.triXor-identityˡ _))
  (trans (Laws.triTruthAddComm _ _) (Base.triXor-identityˡ _))
  (trans (Laws.triTruthAddComm _ _) (Base.triXor-identityˡ _))
  (trans (Laws.triTruthAddComm _ _) (Base.triXor-identityˡ _))
  (trans (Laws.triTruthAddComm _ _) (Base.triXor-identityˡ _))
  (trans (Laws.triTruthAddComm _ _) (Base.triXor-identityˡ _))
  (trans (Laws.triTruthAddComm _ _) (Base.triXor-identityˡ _))
  (trans (Laws.triTruthAddComm _ _) (Base.triXor-identityˡ _))
  (trans (Laws.triTruthAddComm _ _) (Base.triXor-identityˡ _))

negNegFace : (a : Face9) → negFace (negFace a) ≡ a
negNegFace a = faceExt
  (negNeg _) (negNeg _) (negNeg _)
  (negNeg _) (negNeg _) (negNeg _)
  (negNeg _) (negNeg _) (negNeg _)

addSubCancelFace : (a b : Face9) → addFace a (subFace b a) ≡ b
addSubCancelFace a b = faceExt
  (addSubCancel _ _) (addSubCancel _ _) (addSubCancel _ _)
  (addSubCancel _ _) (addSubCancel _ _) (addSubCancel _ _)
  (addSubCancel _ _) (addSubCancel _ _) (addSubCancel _ _)

subRearrangeFace : (a b c : Face9) →
  subFace (addFace a b) (addFace c a) ≡ addFace b (negFace c)
subRearrangeFace a b c = faceExt
  (subRearrange _ _ _) (subRearrange _ _ _) (subRearrange _ _ _)
  (subRearrange _ _ _) (subRearrange _ _ _) (subRearrange _ _ _)
  (subRearrange _ _ _) (subRearrange _ _ _) (subRearrange _ _ _)

------------------------------------------------------------------------
-- B operator and exact characteristic-three identity B^3 = -I.
------------------------------------------------------------------------

bop : Face9 → Face9
bop a = Fine.phaseFineTable9
  (Base.triXor (Fine.q10 a) (Fine.q01 a))
  (Base.triXor (Fine.q11 a) (Fine.q02 a))
  (Base.triXor (Fine.q12 a) (Fine.q00 a))
  (Base.triXor (Fine.q20 a) (Fine.q11 a))
  (Base.triXor (Fine.q21 a) (Fine.q12 a))
  (Base.triXor (Fine.q22 a) (Fine.q10 a))
  (Base.triXor (Fine.q00 a) (Fine.q21 a))
  (Base.triXor (Fine.q01 a) (Fine.q22 a))
  (Base.triXor (Fine.q02 a) (Fine.q20 a))

bop2 : Face9 → Face9
bop2 a = bop (bop a)

bop3 : Face9 → Face9
bop3 a = bop (bop2 a)

bopZero : bop zeroFace ≡ zeroFace
bopZero = refl

bopAdd : (a b : Face9) → bop (addFace a b) ≡ addFace (bop a) (bop b)
bopAdd a b = faceExt
  (addMedial _ _ _ _) (addMedial _ _ _ _) (addMedial _ _ _ _)
  (addMedial _ _ _ _) (addMedial _ _ _ _) (addMedial _ _ _ _)
  (addMedial _ _ _ _) (addMedial _ _ _ _) (addMedial _ _ _ _)

bopNeg : (a : Face9) → bop (negFace a) ≡ negFace (bop a)
bopNeg a = faceExt
  (sym (negAdd _ _)) (sym (negAdd _ _)) (sym (negAdd _ _))
  (sym (negAdd _ _)) (sym (negAdd _ _)) (sym (negAdd _ _))
  (sym (negAdd _ _)) (sym (negAdd _ _)) (sym (negAdd _ _))

bopSub : (a b : Face9) → bop (subFace a b) ≡ subFace (bop a) (bop b)
bopSub a b =
  trans (bopAdd a (negFace b))
    (cong (addFace (bop a)) (bopNeg b))

bop2Add : (a b : Face9) → bop2 (addFace a b) ≡ addFace (bop2 a) (bop2 b)
bop2Add a b =
  trans (cong bop (bopAdd a b)) (bopAdd (bop a) (bop b))

bop3Cell : Base.TriTruth → Base.TriTruth → Base.TriTruth → Base.TriTruth
bop3Cell x y z =
  Base.triXor
    (Base.triXor (Base.triXor x y) (Base.triXor y z))
    (Base.triXor (Base.triXor y z) (Base.triXor z x))

bop3CellNeg : (x y z : Base.TriTruth) → bop3Cell x y z ≡ Laws.triTruthNeg x
bop3CellNeg Base.tri-low Base.tri-low Base.tri-low = refl
bop3CellNeg Base.tri-low Base.tri-low Base.tri-mid = refl
bop3CellNeg Base.tri-low Base.tri-low Base.tri-high = refl
bop3CellNeg Base.tri-low Base.tri-mid Base.tri-low = refl
bop3CellNeg Base.tri-low Base.tri-mid Base.tri-mid = refl
bop3CellNeg Base.tri-low Base.tri-mid Base.tri-high = refl
bop3CellNeg Base.tri-low Base.tri-high Base.tri-low = refl
bop3CellNeg Base.tri-low Base.tri-high Base.tri-mid = refl
bop3CellNeg Base.tri-low Base.tri-high Base.tri-high = refl
bop3CellNeg Base.tri-mid Base.tri-low Base.tri-low = refl
bop3CellNeg Base.tri-mid Base.tri-low Base.tri-mid = refl
bop3CellNeg Base.tri-mid Base.tri-low Base.tri-high = refl
bop3CellNeg Base.tri-mid Base.tri-mid Base.tri-low = refl
bop3CellNeg Base.tri-mid Base.tri-mid Base.tri-mid = refl
bop3CellNeg Base.tri-mid Base.tri-mid Base.tri-high = refl
bop3CellNeg Base.tri-mid Base.tri-high Base.tri-low = refl
bop3CellNeg Base.tri-mid Base.tri-high Base.tri-mid = refl
bop3CellNeg Base.tri-mid Base.tri-high Base.tri-high = refl
bop3CellNeg Base.tri-high Base.tri-low Base.tri-low = refl
bop3CellNeg Base.tri-high Base.tri-low Base.tri-mid = refl
bop3CellNeg Base.tri-high Base.tri-low Base.tri-high = refl
bop3CellNeg Base.tri-high Base.tri-mid Base.tri-low = refl
bop3CellNeg Base.tri-high Base.tri-mid Base.tri-mid = refl
bop3CellNeg Base.tri-high Base.tri-mid Base.tri-high = refl
bop3CellNeg Base.tri-high Base.tri-high Base.tri-low = refl
bop3CellNeg Base.tri-high Base.tri-high Base.tri-mid = refl
bop3CellNeg Base.tri-high Base.tri-high Base.tri-high = refl

bop3Neg : (a : Face9) → bop3 a ≡ negFace a
bop3Neg a = faceExt
  (bop3CellNeg (Fine.q00 a) (Fine.q21 a) (Fine.q12 a))
  (bop3CellNeg (Fine.q01 a) (Fine.q22 a) (Fine.q10 a))
  (bop3CellNeg (Fine.q02 a) (Fine.q20 a) (Fine.q11 a))
  (bop3CellNeg (Fine.q10 a) (Fine.q01 a) (Fine.q22 a))
  (bop3CellNeg (Fine.q11 a) (Fine.q02 a) (Fine.q20 a))
  (bop3CellNeg (Fine.q12 a) (Fine.q00 a) (Fine.q21 a))
  (bop3CellNeg (Fine.q20 a) (Fine.q11 a) (Fine.q02 a))
  (bop3CellNeg (Fine.q21 a) (Fine.q12 a) (Fine.q00 a))
  (bop3CellNeg (Fine.q22 a) (Fine.q10 a) (Fine.q01 a))

------------------------------------------------------------------------
-- Concrete cube step and graph law.
------------------------------------------------------------------------

record CubeFaces : Set where
  constructor cube-faces
  field
    face0 face1 face2 : Face9
open CubeFaces public

cubeExt : {a b : CubeFaces} →
  face0 a ≡ face0 b → face1 a ≡ face1 b → face2 a ≡ face2 b → a ≡ b
cubeExt {cube-faces _ _ _} {cube-faces _ _ _} refl refl refl = refl

cubeStep : CubeFaces → CubeFaces
cubeStep source = cube-faces
  (addFace (bop (face0 source)) (face1 source))
  (addFace (bop (face1 source)) (face2 source))
  (addFace (bop (face2 source)) (face0 source))

graphThird : CubeFaces → Face9
graphThird output = subFace (bop (face1 output)) (bop2 (face0 output))

GraphLaw : CubeFaces → Set
GraphLaw output = face2 output ≡ graphThird output

stepGraphLaw : (source : CubeFaces) → GraphLaw (cubeStep source)
stepGraphLaw source = sym chain
  where
  u0 = face0 source
  u1 = face1 source
  u2 = face2 source

  first :
    graphThird (cubeStep source)
    ≡ subFace
        (addFace (bop2 u1) (bop u2))
        (addFace (bop3 u0) (bop2 u1))
  first =
    cong₂ subFace
      (bopAdd (bop u1) u2)
      (bop2Add (bop u0) u1)

  second :
    subFace
      (addFace (bop2 u1) (bop u2))
      (addFace (bop3 u0) (bop2 u1))
    ≡ addFace (bop u2) (negFace (bop3 u0))
  second = subRearrangeFace (bop2 u1) (bop u2) (bop3 u0)

  third :
    addFace (bop u2) (negFace (bop3 u0))
    ≡ addFace (bop u2) (negFace (negFace u0))
  third = cong (addFace (bop u2) ∘ negFace) (bop3Neg u0)

  fourth :
    addFace (bop u2) (negFace (negFace u0))
    ≡ addFace (bop u2) u0
  fourth = cong (addFace (bop u2)) (negNegFace u0)

  chain : graphThird (cubeStep source) ≡ face2 (cubeStep source)
  chain = trans first (trans second (trans third fourth))

------------------------------------------------------------------------
-- Image equality as a proof-relevant preimage iff graph-law theorem.
------------------------------------------------------------------------

record CubeStepPreimage (output : CubeFaces) : Set where
  constructor cube-step-preimage
  field
    source : CubeFaces
    stepEqualsOutput : cubeStep source ≡ output
open CubeStepPreimage public

preimageImpliesGraph : (output : CubeFaces) → CubeStepPreimage output → GraphLaw output
preimageImpliesGraph .(cubeStep source) (cube-step-preimage source refl) =
  stepGraphLaw source

canonicalSource : CubeFaces → CubeFaces
canonicalSource output = cube-faces
  zeroFace
  (face0 output)
  (subFace (face1 output) (bop (face0 output)))

canonicalFirst : (output : CubeFaces) →
  face0 (cubeStep (canonicalSource output)) ≡ face0 output
canonicalFirst output =
  trans (cong (λ t → addFace t (face0 output)) bopZero)
        (addZeroLFace (face0 output))

canonicalSecond : (output : CubeFaces) →
  face1 (cubeStep (canonicalSource output)) ≡ face1 output
canonicalSecond output =
  addSubCancelFace (bop (face0 output)) (face1 output)

canonicalThirdToGraph : (output : CubeFaces) →
  face2 (cubeStep (canonicalSource output)) ≡ graphThird output
canonicalThirdToGraph output =
  trans
    (addZeroRFace
      (bop (subFace (face1 output) (bop (face0 output)))))
    (bopSub (face1 output) (bop (face0 output)))

graphImpliesPreimage : (output : CubeFaces) → GraphLaw output → CubeStepPreimage output
graphImpliesPreimage output law =
  cube-step-preimage
    (canonicalSource output)
    (cubeExt
      (canonicalFirst output)
      (canonicalSecond output)
      (trans (canonicalThirdToGraph output) (sym law)))

record ConcreteCubeImageIffGraph (output : CubeFaces) : Set where
  constructor concrete-cube-image-iff-graph
  field
    imageToGraph : CubeStepPreimage output → GraphLaw output
    graphToImage : GraphLaw output → CubeStepPreimage output

concreteCubeImageIffGraph : (output : CubeFaces) → ConcreteCubeImageIffGraph output
concreteCubeImageIffGraph output =
  concrete-cube-image-iff-graph
    (preimageImpliesGraph output)
    (graphImpliesPreimage output)

------------------------------------------------------------------------
-- Reuse boundary: T^18 / 3^18 / 9^9 is prior art, not rederived authority.
------------------------------------------------------------------------

record ConcreteTorusImageBoundary : Set where
  constructor concrete-torus-image-boundary
  field
    existingPhaseFineTable9UsedAsFace : Bool
    actualBOperatorDefined : Bool
    bCubedIsNegativeIdentityKernelTheorem : Bool
    cubeStepImageEqualsTwoFaceGraph : Bool
    rankEighteenNumericsUsedAsProof : Bool
    existingTrialecticT18CarrierIsPriorArt : Bool
    existingSameBoundaryDifferentFaceIsPriorArt : Bool

canonicalConcreteTorusImageBoundary : ConcreteTorusImageBoundary
canonicalConcreteTorusImageBoundary =
  concrete-torus-image-boundary true true true true false true true
