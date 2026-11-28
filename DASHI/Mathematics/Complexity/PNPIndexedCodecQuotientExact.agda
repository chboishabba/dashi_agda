module DASHI.Mathematics.Complexity.PNPIndexedCodecQuotientExact where

open import DASHI.Core.Prelude
import DASHI.Codec.IndexedCubeHyperfibreExact as H
import DASHI.Codec.IndexedCubeMaskSignExact as C
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Mathematics.Complexity.RecursiveHyperfabricQuotientExact as Q

-- The actual cube carries all three blocks. The resolution label 6
-- does not itself erase the residual triple. Use the owner's BIDI map.
reopenOriginal : H.State H.i → H.State H.a
reopenOriginal y = C.rotate (C.rotate (C.decode (C.join y)))

reopenWalk : ∀ x → reopenOriginal (H.walk H.xyzPath x) ≡ x
reopenWalk x =
  trans (cong (λ z → C.rotate (C.rotate z)) (H.reopenTerminal x))
    (C.rotationOrderThree x)

decodeEncodeBlock : ∀ y → C.encode (C.decode y) ≡ y
decodeEncodeBlock (C.blocks a b c)
  rewrite M.encodeTriple-decodeTriple a | M.encodeTriple-decodeTriple b
        | M.encodeTriple-decodeTriple c = refl

walkAsPartition : ∀ x → H.walk H.xyzPath x ≡ C.partition (C.encode (C.rotate x))
walkAsPartition x =
  trans (cong C.encodeSplit (sym (C.partitionRotation x)))
    (sym (C.partitionCodec (C.rotate x)))

walkReopen : ∀ y → H.walk H.xyzPath (reopenOriginal y) ≡ y
walkReopen y =
  trans (walkAsPartition (reopenOriginal y))
    (trans (cong (λ z → C.partition (C.encode z))
      (C.rotationOrderThree (C.decode (C.join y))))
      (trans (cong C.partition (decodeEncodeBlock (C.join y)))
        (C.partitionJoin y)))

-- Actual codec transport is a lossless change of chart. It is NOT a
-- cardinality reduction until a consumer licenses erasing a fibre.
codecStep : ∀ {Y : Set} (f : H.State H.a → Y) →
  Q.QuotientStep (H.State H.a) (H.State H.i) Y f (λ y → f (reopenOriginal y))
codecStep f = record
  { contract = H.walk H.xyzPath
  ; lift = reopenOriginal
  ; section = walkReopen
  ; closed = λ x → cong f (reopenWalk x)
  }

-- A genuine 9 -> 3 contraction may discard the first two blocks only
-- after proving the actual consumer depends on the suffix.
suffixStep : ∀ {A Y : Set} (a b : M.Triple A)
  (f : C.PrefixResidual A → Y)
  (closed : ∀ x → f (C.split a b (C.suffix x)) ≡ f x) →
  Q.QuotientStep (C.PrefixResidual A) (M.Triple A) Y f
    (λ s → f (C.split a b s))
suffixStep a b f closed = record
  { contract = C.suffix
  ; lift = C.split a b
  ; section = λ s → refl
  ; closed = closed
  }
