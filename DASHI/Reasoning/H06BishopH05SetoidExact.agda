module DASHI.Reasoning.H06BishopH05SetoidExact where

-- Original H05 codec arrows, with actual native continuous recharting.
-- Use the existing GovernedSquare.Commutes field for the setoid relation;
-- do NOT manufacture strict CommutingSquareWitness from real equality.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Sum.Base using (inj₂)
import DASHI.Core.GovernedIndexedResidualCubeExact as Q
import DASHI.Core.GovernedDiagramCore as G
import DASHI.Reasoning.H07FrameCarryingCubeExact as Source
import DASHI.Reasoning.H06BishopAffineFrameExact as H
import DASHI.Reasoning.H06BishopAffineRechartExact as A
import DASHI.Reasoning.H06BishopAffineCocycleExact as C
import DASHI.Reasoning.H06BishopFourFrameChartsExact as F
import DASHI.Reasoning.H06BishopFrameCocycleExact as R

-- Work over one original continuous datum, in a supplied common
-- overlap. Every chart guard belongs to that actual plane or matrix.
-- The discrete source retains the original winding/time/history etc.
module At (p : A.Plane4) (r : H.Matrix3) where

  record Chart : Set where
    constructor chart
    field
      planeMark : A.Admissible p
      frameMark : F.Mark
      frameImage : R.Image frameMark r
  open Chart public

  record Charts : Set where
    field
      a b c d e f h i : Chart
  open Charts public

  -- Coefficients are the actual normalized affine rows, not a new
  -- dimension label. They are determined by the original p and mark.
  chartPlane : Chart → A.Plane4
  chartPlane k = A.rechart p (planeMark k)

  pairMove : Chart → Chart → C.Pair → C.Pair
  pairMove a b x = C.forward p (planeMark b) (C.backward p (planeMark a) x)

  pairMoveCong : (a b : Chart) {x y : C.Pair} → C.PairEq x y →
    C.PairEq (pairMove a b x) (pairMove a b y)
  pairMoveCong a b eq =
    C.forwardCong p (planeMark b) (C.backwardCong p (planeMark a) eq)

  pairTwo : (a b c : Chart) (x : C.Pair) →
    C.PairEq (pairMove b c (pairMove a b x)) (pairMove a c x)
  pairTwo a b c x =
    C.forwardCong p (planeMark c)
      (C.reopen p (planeMark b) (C.backward p (planeMark a) x))

  pairThree : (a b c d : Chart) (x : C.Pair) →
    C.PairEq (pairMove c d (pairMove b c (pairMove a b x))) (pairMove a d x)
  pairThree a b c d x = C.pairTrans
    (pairMoveCong c d (pairTwo a b c x)) (pairTwo a c d x)

  record State (X : Set) (k : Chart) : Set where
    constructor state
    field
      source : X
      point : C.Pair
      frameCoordinates : H.Frame3
      sameFrame : F.MatrixEq (F.encode (frameMark k) frameCoordinates) r
      spinSign : Bool
  open State public

  record StateEq {X : Set} {k : Chart} (u v : State X k) : Set where
    constructor stateEq
    field
      sourceEq : source u ≡ source v
      pointEq : C.PairEq (point u) (point v)
      frameEq : F.FrameEq (frameCoordinates u) (frameCoordinates v)
      signEq : spinSign u ≡ spinSign v

  -- Two actual coordinates in the same marked chart of the same frame
  -- are equivalent by the original decoder, not by proof irrelevance.
  frameUnique : (k : F.Mark) (f g : H.Frame3) →
    F.MatrixEq (F.encode k f) (F.encode k g) → F.FrameEq f g
  frameUnique k f g e = F.frameTrans (R.frameSym (F.reopens k f))
    (F.frameTrans
      (F.recoverCong (F.flipMatrix k (F.encode k f))
        (F.flipMatrix k (F.encode k g))
        (inj₂ (F.encodePositive k f)) (inj₂ (F.encodePositive k g))
        (R.flipCong k e))
      (F.reopens k g))

  compare : {X : Set} {k : Chart} (u v : State X k) →
    source u ≡ source v → C.PairEq (point u) (point v) →
    spinSign u ≡ spinSign v → StateEq u v
  compare {k = k} u v es ep sg = stateEq es ep
    (frameUnique (frameMark k) (frameCoordinates u) (frameCoordinates v)
      (R.matrixTrans (sameFrame u) (R.matrixSym (sameFrame v)))) sg

  -- Lift every literal original arrow. The new coordinates come from
  -- the CURRENT point and encoded frame; the supplied target image
  -- is only admissibility evidence. Keep the independent Spin sign.
  lift : {X Y : Set} (a b : Chart) → (X → Y) → State X a → State Y b
  lift a b g u =
    let target = R.transportImage (frameImage b) (R.matrixSym (sameFrame u))
        f = R.transition (frameMark a) (frameMark b) (frameCoordinates u) target
        e = R.transitionPreserves (frameMark a) (frameMark b) (frameCoordinates u) target
    in state (g (source u)) (pairMove a b (point u)) f
         (R.matrixTrans e (sameFrame u)) (spinSign u)

  liftSquare : {X Y Z W : Set} (a b c d : Chart)
    (f : X → Y) (g : X → Z) (h : Y → W) (i : Z → W) →
    ((x : X) → h (f x) ≡ i (g x)) → (u : State X a) →
    StateEq (lift b d h (lift a b f u)) (lift c d i (lift a c g u))
  liftSquare a b c d f g h i eq u =
    compare (lift b d h (lift a b f u)) (lift c d i (lift a c g u))
      (eq (source u))
      (C.pairTrans (pairTwo a b d (point u)) (C.pairSym (pairTwo a c d (point u))))
      refl

  module On (k : Charts) where

    cube : Q.Cube
    cube = record
      { A = State (Q.A Source.cube) (a k)
      ; B = State (Q.B Source.cube) (b k)
      ; C = State (Q.C Source.cube) (c k)
      ; D = State (Q.D Source.cube) (d k)
      ; E = State (Q.E Source.cube) (e k)
      ; F = State (Q.F Source.cube) (f k)
      ; H = State (Q.H Source.cube) (h k)
      ; I = State (Q.I Source.cube) (i k)
      ; x00 = lift (a k) (b k) (Q.x00 Source.cube)
      ; x10 = lift (c k) (d k) (Q.x10 Source.cube)
      ; x01 = lift (e k) (f k) (Q.x01 Source.cube)
      ; x11 = lift (h k) (i k) (Q.x11 Source.cube)
      ; y00 = lift (a k) (c k) (Q.y00 Source.cube)
      ; y10 = lift (b k) (d k) (Q.y10 Source.cube)
      ; y01 = lift (e k) (h k) (Q.y01 Source.cube)
      ; y11 = lift (f k) (i k) (Q.y11 Source.cube)
      ; z00 = lift (a k) (e k) (Q.z00 Source.cube)
      ; z10 = lift (b k) (f k) (Q.z10 Source.cube)
      ; z01 = lift (c k) (h k) (Q.z01 Source.cube)
      ; z11 = lift (d k) (i k) (Q.z11 Source.cube)
      }

    -- Six original governed square structures with the actual native
    -- comparison relation. Retain entire source of each face.
    xy0 : G.GovernedSquare
    xy0 = G.governedSquare (Q.A cube) (Q.B cube) (Q.C cube) (Q.D cube)
      (Q.x00 cube) (Q.y00 cube) (Q.y10 cube) (Q.x10 cube)
      (λ u → StateEq (Q.y10 cube (Q.x00 cube u)) (Q.x10 cube (Q.y00 cube u)))
      (λ _ → Q.A cube) true false

    payxy0 : (u : Q.A cube) → G.Commutes xy0 u
    payxy0 = liftSquare (a k) (b k) (c k) (d k)
      (Q.x00 Source.cube) (Q.y00 Source.cube) (Q.y10 Source.cube) (Q.x10 Source.cube)
      (G.commutes (Q.pxy0 Source.exact))

    retainxy0 : G.ResidualSquareWitness xy0
    retainxy0 = G.residualSquareWitness (λ u → u)

    xz0 : G.GovernedSquare
    xz0 = G.governedSquare (Q.A cube) (Q.B cube) (Q.E cube) (Q.F cube)
      (Q.x00 cube) (Q.z00 cube) (Q.z10 cube) (Q.x01 cube)
      (λ u → StateEq (Q.z10 cube (Q.x00 cube u)) (Q.x01 cube (Q.z00 cube u)))
      (λ _ → Q.A cube) true false

    payxz0 : (u : Q.A cube) → G.Commutes xz0 u
    payxz0 = liftSquare (a k) (b k) (e k) (f k)
      (Q.x00 Source.cube) (Q.z00 Source.cube) (Q.z10 Source.cube) (Q.x01 Source.cube)
      (G.commutes (Q.pxz0 Source.exact))

    retainxz0 : G.ResidualSquareWitness xz0
    retainxz0 = G.residualSquareWitness (λ u → u)

    yz0 : G.GovernedSquare
    yz0 = G.governedSquare (Q.A cube) (Q.C cube) (Q.E cube) (Q.H cube)
      (Q.y00 cube) (Q.z00 cube) (Q.z01 cube) (Q.y01 cube)
      (λ u → StateEq (Q.z01 cube (Q.y00 cube u)) (Q.y01 cube (Q.z00 cube u)))
      (λ _ → Q.A cube) true false

    payyz0 : (u : Q.A cube) → G.Commutes yz0 u
    payyz0 = liftSquare (a k) (c k) (e k) (h k)
      (Q.y00 Source.cube) (Q.z00 Source.cube) (Q.z01 Source.cube) (Q.y01 Source.cube)
      (G.commutes (Q.pyz0 Source.exact))

    retainyz0 : G.ResidualSquareWitness yz0
    retainyz0 = G.residualSquareWitness (λ u → u)

    xy1 : G.GovernedSquare
    xy1 = G.governedSquare (Q.E cube) (Q.F cube) (Q.H cube) (Q.I cube)
      (Q.x01 cube) (Q.y01 cube) (Q.y11 cube) (Q.x11 cube)
      (λ u → StateEq (Q.y11 cube (Q.x01 cube u)) (Q.x11 cube (Q.y01 cube u)))
      (λ _ → Q.E cube) true false

    payxy1 : (u : Q.E cube) → G.Commutes xy1 u
    payxy1 = liftSquare (e k) (f k) (h k) (i k)
      (Q.x01 Source.cube) (Q.y01 Source.cube) (Q.y11 Source.cube) (Q.x11 Source.cube)
      (G.commutes (Q.pxy1 Source.exact))

    retainxy1 : G.ResidualSquareWitness xy1
    retainxy1 = G.residualSquareWitness (λ u → u)

    xz1 : G.GovernedSquare
    xz1 = G.governedSquare (Q.C cube) (Q.D cube) (Q.H cube) (Q.I cube)
      (Q.x10 cube) (Q.z01 cube) (Q.z11 cube) (Q.x11 cube)
      (λ u → StateEq (Q.z11 cube (Q.x10 cube u)) (Q.x11 cube (Q.z01 cube u)))
      (λ _ → Q.C cube) true false

    payxz1 : (u : Q.C cube) → G.Commutes xz1 u
    payxz1 = liftSquare (c k) (d k) (h k) (i k)
      (Q.x10 Source.cube) (Q.z01 Source.cube) (Q.z11 Source.cube) (Q.x11 Source.cube)
      (G.commutes (Q.pxz1 Source.exact))

    retainxz1 : G.ResidualSquareWitness xz1
    retainxz1 = G.residualSquareWitness (λ u → u)

    yz1 : G.GovernedSquare
    yz1 = G.governedSquare (Q.B cube) (Q.D cube) (Q.F cube) (Q.I cube)
      (Q.y10 cube) (Q.z10 cube) (Q.z11 cube) (Q.y11 cube)
      (λ u → StateEq (Q.z11 cube (Q.y10 cube u)) (Q.y11 cube (Q.z10 cube u)))
      (λ _ → Q.B cube) true false

    payyz1 : (u : Q.B cube) → G.Commutes yz1 u
    payyz1 = liftSquare (b k) (d k) (f k) (i k)
      (Q.y10 Source.cube) (Q.z10 Source.cube) (Q.z11 Source.cube) (Q.y11 Source.cube)
      (G.commutes (Q.pyz1 Source.exact))

    retainyz1 : G.ResidualSquareWitness yz1
    retainyz1 = G.residualSquareWitness (λ u → u)

    -- Six endpoint paths in the original Q cube. Equality is native
    -- at the continuous coordinates, strict on discrete source/sign.
    xyz-xzy : (u : Q.A cube) → StateEq (Q.xyz cube u) (Q.xzy cube u)
    xyz-xzy u = compare (Q.xyz cube u) (Q.xzy cube u)
      (Q.xyz-xzy Source.exact (source u))
      (C.pairTrans (pairThree (a k) (b k) (d k) (i k) (point u))
        (C.pairSym (pairThree (a k) (b k) (f k) (i k) (point u)))) refl

    xyz-yxz : (u : Q.A cube) → StateEq (Q.xyz cube u) (Q.yxz cube u)
    xyz-yxz u = compare (Q.xyz cube u) (Q.yxz cube u)
      (Q.xyz-yxz Source.exact (source u))
      (C.pairTrans (pairThree (a k) (b k) (d k) (i k) (point u))
        (C.pairSym (pairThree (a k) (c k) (d k) (i k) (point u)))) refl

    xyz-yzx : (u : Q.A cube) → StateEq (Q.xyz cube u) (Q.yzx cube u)
    xyz-yzx u = compare (Q.xyz cube u) (Q.yzx cube u)
      (Q.xyz-yzx Source.exact (source u))
      (C.pairTrans (pairThree (a k) (b k) (d k) (i k) (point u))
        (C.pairSym (pairThree (a k) (c k) (h k) (i k) (point u)))) refl

    xyz-zxy : (u : Q.A cube) → StateEq (Q.xyz cube u) (Q.zxy cube u)
    xyz-zxy u = compare (Q.xyz cube u) (Q.zxy cube u)
      (Q.xyz-zxy Source.exact (source u))
      (C.pairTrans (pairThree (a k) (b k) (d k) (i k) (point u))
        (C.pairSym (pairThree (a k) (e k) (f k) (i k) (point u)))) refl

    xyz-zyx : (u : Q.A cube) → StateEq (Q.xyz cube u) (Q.zyx cube u)
    xyz-zyx u = compare (Q.xyz cube u) (Q.zyx cube u)
      (Q.xyz-zyx Source.exact (source u))
      (C.pairTrans (pairThree (a k) (b k) (d k) (i k) (point u))
        (C.pairSym (pairThree (a k) (e k) (h k) (i k) (point u)))) refl

-- This is a genuine continuous COORDINATE lift of the actual H05 arrows
-- on a certified common overlap. It does not assert a new physical
-- evolution of p or r, nor a global choice of chart across singularities.
-- A source sign is carried; no Spin lift is inferred from SO3.
-- Source-written; no kernel acceptance claimed.
