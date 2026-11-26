module DASHI.Reasoning.H07FrameCarryingCubeExact where

-- Actual H05 arrows lifted with their frame and governed winding.
-- Source-written; no Agda kernel acceptance or physical promotion.
open import DASHI.Core.Prelude
import DASHI.Core.GovernedIndexedResidualCubeExact as Q
import DASHI.Core.GovernedDiagramCore as G
import DASHI.Codec.IndexedCubeMaskSignExact as C
import DASHI.Codec.IndexedCubeMaskSignInstanceExact as I
import DASHI.Reasoning.H07FullAtlasSectionExact as H
import DASHI.Reasoning.H07AtlasCodecConsumerExact as O
import DASHI.Reasoning.H07IntegerWindingExact as W
import DASHI.Reasoning.H07AffinePairedSeamExact as S

record Frame : Set where
  constructor frame
  field
    anchor localMark targetMark : H.Pivot
    windingContext : W.GovernedWindingContext

-- Residue derived from the actual integer; quotient/history retained in
-- the frame itself. No physical time, Phase4 or Frobenius advancement.
rawFrame : Frame → O.Frame
rawFrame (frame p v q (W.governedWinding k w)) =
  O.frame p v q (W.WindingLift.residue w) k

rotateFrame : Frame → Frame
rotateFrame (frame p v q k) =
  frame p (H.rotatePivot p v) (H.rotatePivot p q) k

rawFrameRotation : (f : Frame) →
  rawFrame (rotateFrame f) ≡ O.rotateFrame (rawFrame f)
rawFrameRotation (frame p v q (W.governedWinding k w)) = refl

Framed : Set → Set
Framed X = Frame × X

keep : {X Y : Set} → (X → Y) → Framed X → Framed Y
keep f (k , x) = k , f x

move : {X Y : Set} → (X → Y) → Framed X → Framed Y
move f (k , x) = rotateFrame k , f x

cube : Q.Cube
cube = record
  { A = Framed (Q.A I.codecCube)
  ; B = Framed (Q.B I.codecCube)
  ; C = Framed (Q.C I.codecCube)
  ; D = Framed (Q.D I.codecCube)
  ; E = Framed (Q.E I.codecCube)
  ; F = Framed (Q.F I.codecCube)
  ; H = Framed (Q.H I.codecCube)
  ; I = Framed (Q.I I.codecCube)
  ; x00 = keep (Q.x00 I.codecCube)
  ; x10 = keep (Q.x10 I.codecCube)
  ; x01 = keep (Q.x01 I.codecCube)
  ; x11 = keep (Q.x11 I.codecCube)
  ; y00 = move (Q.y00 I.codecCube)
  ; y10 = move (Q.y10 I.codecCube)
  ; y01 = move (Q.y01 I.codecCube)
  ; y11 = move (Q.y11 I.codecCube)
  ; z00 = keep (Q.z00 I.codecCube)
  ; z10 = keep (Q.z10 I.codecCube)
  ; z01 = keep (Q.z01 I.codecCube)
  ; z11 = keep (Q.z11 I.codecCube)
  }

-- Retain the entire source at each face, including integer quotient,
-- zero/sign, marks and original independent context.
faces : Q.Faces cube
faces = record
  { Rxy0 = λ _ → Framed (Q.A I.codecCube)
  ; Rxz0 = λ _ → Framed (Q.A I.codecCube)
  ; Ryz0 = λ _ → Framed (Q.A I.codecCube)
  ; Rxy1 = λ _ → Framed (Q.E I.codecCube)
  ; Rxz1 = λ _ → Framed (Q.C I.codecCube)
  ; Ryz1 = λ _ → Framed (Q.B I.codecCube)
  }

exact : Q.ExactFaces cube faces
exact = record
  { pxy0 = G.commutingSquareWitness
      (λ { (k , x) → cong (λ y → rotateFrame k , y)
        (G.commutes (Q.pxy0 I.codecExactFaces) x) })
  ; pxz0 = G.commutingSquareWitness
      (λ { (k , x) → cong (λ y → k , y)
        (G.commutes (Q.pxz0 I.codecExactFaces) x) })
  ; pyz0 = G.commutingSquareWitness
      (λ { (k , x) → cong (λ y → rotateFrame k , y)
        (G.commutes (Q.pyz0 I.codecExactFaces) x) })
  ; pxy1 = G.commutingSquareWitness
      (λ { (k , x) → cong (λ y → rotateFrame k , y)
        (G.commutes (Q.pxy1 I.codecExactFaces) x) })
  ; pxz1 = G.commutingSquareWitness
      (λ { (k , x) → cong (λ y → k , y)
        (G.commutes (Q.pxz1 I.codecExactFaces) x) })
  ; pyz1 = G.commutingSquareWitness
      (λ { (k , x) → cong (λ y → rotateFrame k , y)
        (G.commutes (Q.pyz1 I.codecExactFaces) x) })
  }

residuals : Q.ResidualFaces cube faces
residuals = record
  { rxy0 = G.residualSquareWitness (λ x → x)
  ; rxz0 = G.residualSquareWitness (λ x → x)
  ; ryz0 = G.residualSquareWitness (λ x → x)
  ; rxy1 = G.residualSquareWitness (λ x → x)
  ; rxz1 = G.residualSquareWitness (λ x → x)
  ; ryz1 = G.residualSquareWitness (λ x → x)
  }

indexed : (K : Set) → Q.IndexedCube K
indexed K = record
  { cubeAt = λ _ → cube ; facesAt = λ _ → faces
  ; residualAt = λ _ → residuals }

-- The original six endpoint orders now agree on the full frame AND
-- original encoded coefficients, not only on an unframed readout.
xyz-xzy : (x : Q.A cube) → Q.xyz cube x ≡ Q.xzy cube x
xyz-xzy = Q.xyz-xzy exact

xyz-yxz : (x : Q.A cube) → Q.xyz cube x ≡ Q.yxz cube x
xyz-yxz = Q.xyz-yxz exact

xyz-yzx : (x : Q.A cube) → Q.xyz cube x ≡ Q.yzx cube x
xyz-yzx = Q.xyz-yzx exact

xyz-zxy : (x : Q.A cube) → Q.xyz cube x ≡ Q.zxy cube x
xyz-zxy = Q.xyz-zxy exact

xyz-zyx : (x : Q.A cube) → Q.xyz cube x ≡ Q.zyx cube x
xyz-zyx = Q.xyz-zyx exact

terminalReopen : (k : Frame) (x : C.Blocks _) →
  O.reopenFactSplit (proj₂ (Q.xyz cube (k , x))) ≡ C.rotate x
terminalReopen k x = I.terminalReopen x

terminalFrame : (k : Frame) (x : Q.A I.codecCube) →
  proj₁ (Q.xyz cube (k , x)) ≡ rotateFrame k
terminalFrame k x = refl

terminalObservation : (k : Frame) (x : Q.A I.codecCube) →
  O.observe (rawFrame (proj₁ (Q.xyz cube (k , x))))
    (O.reopenFactSplit (proj₂ (Q.xyz cube (k , x))))
  ≡ O.observe (O.rotateFrame (rawFrame k)) (C.rotate x)
terminalObservation k x =
  cong₂ O.observe (rawFrameRotation k) (I.terminalReopen x)

-- For actual admissible marks the geometric naturality is owned by
-- H07AtlasRotationNaturalityExact.rotateRestriction. Singular cases are
-- retained by O.observe. Frame rotation is not a physical time step.
