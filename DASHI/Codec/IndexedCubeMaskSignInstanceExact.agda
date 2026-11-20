module DASHI.Codec.IndexedCubeMaskSignInstanceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤)
open import DASHI.Algebra.Trit using (Trit)
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Codec.IndexedCubeMaskSignExact as C
import DASHI.Core.GovernedIndexedResidualCubeExact as Q
import DASHI.Core.GovernedDiagramCore as G

-- Literal diagram: x partitions (retains suffix), y rotates, z encodes.
-- All twelve arrows use existing codec operations, not endpoint aliases.
codecCube : Q.Cube
codecCube = record
  { A = C.Blocks Trit
  ; B = C.PrefixResidual Trit
  ; C = C.Blocks Trit
  ; D = C.PrefixResidual Trit
  ; E = C.Blocks M.FactorizedTrit
  ; F = C.PrefixResidual M.FactorizedTrit
  ; H = C.Blocks M.FactorizedTrit
  ; I = C.PrefixResidual M.FactorizedTrit
  ; x00 = C.partition
  ; x10 = C.partition
  ; x01 = C.partition
  ; x11 = C.partition
  ; y00 = C.rotate
  ; y10 = C.rotateSplit
  ; y01 = C.rotate
  ; y11 = C.rotateSplit
  ; z00 = C.encode
  ; z10 = C.encodeSplit
  ; z01 = C.encode
  ; z11 = C.encodeSplit
  }

-- Exact faces need no additional commutation-defect payload.
-- The actual suffix and sign residuals remain in the vertex carriers.
codecFaces : Q.Faces codecCube
codecFaces = record
  { Rxy0 = λ _ → ⊤ ; Rxz0 = λ _ → ⊤ ; Ryz0 = λ _ → ⊤
  ; Rxy1 = λ _ → ⊤ ; Rxz1 = λ _ → ⊤ ; Ryz1 = λ _ → ⊤
  }

sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

codecExactFaces : Q.ExactFaces codecCube codecFaces
codecExactFaces = record
  { pxy0 = G.commutingSquareWitness
      (λ a → sym (C.partitionRotation a))
  ; pxz0 = G.commutingSquareWitness
      (λ a → sym (C.partitionCodec a))
  ; pyz0 = G.commutingSquareWitness C.codecRotation
  ; pxy1 = G.commutingSquareWitness
      (λ a → sym (C.partitionRotation a))
  ; pxz1 = G.commutingSquareWitness
      (λ a → sym (C.partitionCodec a))
  ; pyz1 = G.commutingSquareWitness C.splitCodecRotation
  }

-- Invoke the generic six-square theorem, not a second proof by enumeration.
allPathsExample : (a : C.Blocks Trit) →
  Q.xyz codecCube a ≡ Q.zyx codecCube a
allPathsExample = Q.xyz-zyx codecExactFaces

terminalReopen : (a : C.Blocks Trit) →
  C.decode (C.join (Q.xyz codecCube a)) ≡ C.rotate a
terminalReopen (C.blocks (M.triple a b c) (M.triple d e f)
  (M.triple g h i)) =
  C.roundtrip (C.blocks (M.triple b c a) (M.triple e f d)
    (M.triple h i g))
