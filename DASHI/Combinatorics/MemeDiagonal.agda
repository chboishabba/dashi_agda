module DASHI.Combinatorics.MemeDiagonal where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- A finite-codomain Cantor diagonal theorem for infinite meme streams.
--
-- Finite meme strings remain countable.  The theorem concerns streams
-- Nat -> Four and refutes each proposed Nat-indexed enumeration by a
-- fixed-point-free coordinate rotation.
------------------------------------------------------------------------

data Four : Set where
  colour0 colour1 colour2 colour3 : Four

rotate : Four → Four
rotate colour0 = colour1
rotate colour1 = colour2
rotate colour2 = colour3
rotate colour3 = colour0

rotateHasNoFixedPoint : ∀ colour → ¬ (rotate colour ≡ colour)
rotateHasNoFixedPoint colour0 ()
rotateHasNoFixedPoint colour1 ()
rotateHasNoFixedPoint colour2 ()
rotateHasNoFixedPoint colour3 ()

MemeStream : Set
MemeStream = Nat → Four

MemeEnumeration : Set
MemeEnumeration = Nat → MemeStream

neoDiagonal : MemeEnumeration → MemeStream
neoDiagonal enumeration index =
  rotate (enumeration index index)

neoDiffersAtDiagonal :
  ∀ enumeration index →
  ¬ (neoDiagonal enumeration index ≡ enumeration index index)
neoDiffersAtDiagonal enumeration index =
  rotateHasNoFixedPoint (enumeration index index)

neoNotEnumerated :
  ∀ enumeration index →
  ¬ (neoDiagonal enumeration ≡ enumeration index)
neoNotEnumerated enumeration index equality =
  neoDiffersAtDiagonal enumeration index
    (cong (λ stream → stream index) equality)

noMemeStreamEnumeration :
  ∀ enumeration →
  ¬ ((stream : MemeStream) → Σ Nat λ index → enumeration index ≡ stream)
noMemeStreamEnumeration enumeration surjective =
  neoNotEnumerated enumeration
    (fst diagonalPreimage)
    (sym (snd diagonalPreimage))
  where
  diagonalPreimage :
    Σ Nat λ index → enumeration index ≡ neoDiagonal enumeration
  diagonalPreimage = surjective (neoDiagonal enumeration)

record MemeDiagonalReceipt : Set where
  field
    proposedEnumeration : MemeEnumeration
    omittedStream : MemeStream
    omittedStreamIsNeoDiagonal :
      omittedStream ≡ neoDiagonal proposedEnumeration
    omittedAtEveryIndex :
      ∀ index → ¬ (omittedStream ≡ proposedEnumeration index)

canonicalMemeDiagonalReceipt :
  (enumeration : MemeEnumeration) →
  MemeDiagonalReceipt
canonicalMemeDiagonalReceipt enumeration = record
  { proposedEnumeration = enumeration
  ; omittedStream = neoDiagonal enumeration
  ; omittedStreamIsNeoDiagonal = refl
  ; omittedAtEveryIndex = neoNotEnumerated enumeration
  }

record MemeDiagonalAuthorityBoundary : Set where
  field
    infiniteStreamsNotNatEnumerable : Bool
    finiteStringsAlsoProvedUncountable : Bool
    omittedStreamGuaranteedInteresting : Bool
    socialEmergenceLawPromoted : Bool
    theoremScope : String

canonicalMemeDiagonalAuthorityBoundary :
  MemeDiagonalAuthorityBoundary
canonicalMemeDiagonalAuthorityBoundary = record
  { infiniteStreamsNotNatEnumerable = true
  ; finiteStringsAlsoProvedUncountable = false
  ; omittedStreamGuaranteedInteresting = false
  ; socialEmergenceLawPromoted = false
  ; theoremScope =
      "For each Nat-indexed enumeration of Nat-to-Four streams, coordinate rotation constructs one omitted stream."
  }
