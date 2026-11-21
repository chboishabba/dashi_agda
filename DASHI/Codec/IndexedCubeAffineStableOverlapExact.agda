module DASHI.Codec.IndexedCubeAffineStableOverlapExact where

-- H07: actual restricted six-face cube, not the earlier unrestricted
-- codec instance with a merely external/non-persistent pivot guard.
-- The second slope has three explicitly SIGNED coefficients: no zero
-- can enter through partition, rotation, or mask/sign factorization.
-- Cardinality: 3^6 * 2^3 = 5832.  Agda kernel validation OPEN.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤)
open import DASHI.Algebra.Trit using (Trit; neg; pos)
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Codec.IndexedCubeMaskSignExact as C
import DASHI.Codec.IndexedCubeMarkedAffine9Exact as Aff
import DASHI.Codec.IndexedCubeAffinePivotOverlapExact as P
import DASHI.Core.GovernedIndexedResidualCubeExact as Q
import DASHI.Core.GovernedDiagramCore as G

-- Unlike a post-hoc boolean guard, M.Sign excludes zero by type.
record StableBlocks (A : Set) : Set where
  constructor stableBlocks
  field
    firstBlock : M.Triple A
    signedSlope : M.Triple M.Sign
    residualBlock : M.Triple A
open StableBlocks public

record StableSplit (A : Set) : Set where
  constructor stableSplit
  field
    prefixOne : M.Triple A
    signedSlopeSplit : M.Triple M.Sign
    suffix : M.Triple A
open StableSplit public

toSplit : ∀ {A} → StableBlocks A → StableSplit A
toSplit (stableBlocks u v b) = stableSplit u v b

toBlocks : ∀ {A} → StableSplit A → StableBlocks A
toBlocks (stableSplit u v b) = stableBlocks u v b

rotateBlocks : ∀ {A} → StableBlocks A → StableBlocks A
rotateBlocks (stableBlocks u v b) =
  stableBlocks (C.rotateTriple u) (C.rotateTriple v) (C.rotateTriple b)

rotateSplit : ∀ {A} → StableSplit A → StableSplit A
rotateSplit (stableSplit u v b) =
  stableSplit (C.rotateTriple u) (C.rotateTriple v) (C.rotateTriple b)

encodeBlocks : StableBlocks Trit → StableBlocks M.FactorizedTrit
encodeBlocks (stableBlocks u v b) =
  stableBlocks (M.encodeTriple u) v (M.encodeTriple b)

encodeSplit : StableSplit Trit → StableSplit M.FactorizedTrit
encodeSplit (stableSplit u v b) =
  stableSplit (M.encodeTriple u) v (M.encodeTriple b)

decodeBlocks : StableBlocks M.FactorizedTrit → StableBlocks Trit
decodeBlocks (stableBlocks u v b) =
  stableBlocks (M.decodeTriple u) v (M.decodeTriple b)

-- The original raw source/codec can be reopened including the SIGNED slope.
rawSlope : M.Sign → Trit
rawSlope M.negative = neg
rawSlope M.positive = pos

factSlope : M.Sign → M.FactorizedTrit
factSlope = M.active

forgetRaw : StableBlocks Trit → C.Blocks Trit
forgetRaw (stableBlocks u v b) =
  C.blocks u (M.mapTriple rawSlope v) b

forgetFact : StableBlocks M.FactorizedTrit →
  C.Blocks M.FactorizedTrit
forgetFact (stableBlocks u v b) =
  C.blocks u (M.mapTriple factSlope v) b

forgetRawSplit : StableSplit Trit → C.PrefixResidual Trit
forgetRawSplit (stableSplit u v b) =
  C.split u (M.mapTriple rawSlope v) b

forgetFactSplit : StableSplit M.FactorizedTrit →
  C.PrefixResidual M.FactorizedTrit
forgetFactSplit (stableSplit u v b) =
  C.split u (M.mapTriple factSlope v) b

forgetCodec : (x : StableBlocks Trit) →
  forgetFact (encodeBlocks x) ≡ C.encode (forgetRaw x)
forgetCodec (stableBlocks u (M.triple M.negative M.negative M.negative) r) = refl
forgetCodec (stableBlocks u (M.triple M.negative M.negative M.positive) r) = refl
forgetCodec (stableBlocks u (M.triple M.negative M.positive M.negative) r) = refl
forgetCodec (stableBlocks u (M.triple M.negative M.positive M.positive) r) = refl
forgetCodec (stableBlocks u (M.triple M.positive M.negative M.negative) r) = refl
forgetCodec (stableBlocks u (M.triple M.positive M.negative M.positive) r) = refl
forgetCodec (stableBlocks u (M.triple M.positive M.positive M.negative) r) = refl
forgetCodec (stableBlocks u (M.triple M.positive M.positive M.positive) r) = refl

-- This exact commuting cube contains the selected rotation-stable
-- affine slope domain AT EVERY VERTEX, including factorized vertices.
stableCube : Q.Cube
stableCube = record
  { A = StableBlocks Trit
  ; B = StableSplit Trit
  ; C = StableBlocks Trit
  ; D = StableSplit Trit
  ; E = StableBlocks M.FactorizedTrit
  ; F = StableSplit M.FactorizedTrit
  ; H = StableBlocks M.FactorizedTrit
  ; I = StableSplit M.FactorizedTrit
  ; x00 = toSplit ; x10 = toSplit ; x01 = toSplit ; x11 = toSplit
  ; y00 = rotateBlocks ; y10 = rotateSplit
  ; y01 = rotateBlocks ; y11 = rotateSplit
  ; z00 = encodeBlocks ; z10 = encodeSplit
  ; z01 = encodeBlocks ; z11 = encodeSplit
  }

stableFaces : Q.Faces stableCube
stableFaces = record
  { Rxy0 = λ _ → ⊤ ; Rxz0 = λ _ → ⊤ ; Ryz0 = λ _ → ⊤
  ; Rxy1 = λ _ → ⊤ ; Rxz1 = λ _ → ⊤ ; Ryz1 = λ _ → ⊤
  }

stableExact : Q.ExactFaces stableCube stableFaces
stableExact = record
  { pxy0 = G.commutingSquareWitness
      (λ { (stableBlocks u v b) → refl })
  ; pxz0 = G.commutingSquareWitness
      (λ { (stableBlocks u v b) → refl })
  ; pyz0 = G.commutingSquareWitness
      (λ { (stableBlocks (M.triple a b c)
          (M.triple p q r) (M.triple d e f)) → refl })
  ; pxy1 = G.commutingSquareWitness
      (λ { (stableBlocks u v b) → refl })
  ; pxz1 = G.commutingSquareWitness
      (λ { (stableBlocks u v b) → refl })
  ; pyz1 = G.commutingSquareWitness
      (λ { (stableSplit (M.triple a b c)
          (M.triple p q r) (M.triple d e f)) → refl })
  }

allSixPaths : (x : StableBlocks Trit) →
  Q.xyz stableCube x ≡ Q.zyx stableCube x
allSixPaths = Q.xyz-zyx stableExact

-- Pivot is now available for every original slope position.
-- The witness is extracted from M.Sign, never a partial postcondition.
signNonzero : (s : M.Sign) → P.Nonzero (rawSlope s)
signNonzero M.negative = P.negative
signNonzero M.positive = P.positive

toAffine : StableBlocks Trit → Aff.Affine9 Trit
toAffine x = Aff.fromBlocks (forgetRaw x)

pivotWitness : (x : StableBlocks Trit) →
  P.Overlap01to02 (toAffine x)
pivotWitness (stableBlocks u (M.triple a b c) r) = signNonzero a

pivotUnderRotation : (x : StableBlocks Trit) →
  P.Overlap01to02 (toAffine (rotateBlocks x))
pivotUnderRotation (stableBlocks u (M.triple a b c) r) = signNonzero b

pivotUnderDoubleRotation : (x : StableBlocks Trit) →
  P.Overlap01to02 (toAffine (rotateBlocks (rotateBlocks x)))
pivotUnderDoubleRotation (stableBlocks u (M.triple a b c) r) = signNonzero c

-- Selected pivot change is total ON this restricted original source,
-- but this alone is not a global coordinate-wise commuting naturality
-- law. It changes the affine mark, not the original spatial source.
pivotAt : StableBlocks Trit → Aff.Affine9 Trit
pivotAt x = P.swapPivot (toAffine x) (pivotWitness x)
