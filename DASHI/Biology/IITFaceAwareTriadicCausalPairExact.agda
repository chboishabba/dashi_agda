module DASHI.Biology.IITFaceAwareTriadicCausalPairExact where

------------------------------------------------------------------------
-- FACE-AWARE MATCHED CAUSAL PAIR
--
-- The older triadic non-descent theorem correctly says that no output which
-- sees only the shared pairwise boundary can reconstruct a hidden triadic face.
-- That is an observer theorem, not yet an IIT discrimination experiment.
--
-- Here the higher-order face is placed in the transition law itself.  The two
-- deterministic three-bit systems agree on every coordinate face (whenever
-- any one of A,B,C is false), but differ at the genuine three-way interior
-- state 111 by the pure cubic term A*B*C.
--
-- This is the matched TPM pair consumed by numerical IIT experiments.  The
-- Agda authority here is only the exact same-face / different-interior causal
-- statement; numerical phi values remain Python/PyPhi receipts.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

xorB : Bool → Bool → Bool
xorB false false = false
xorB false true  = true
xorB true  false = true
xorB true  true  = false

and3 : Bool → Bool → Bool → Bool
and3 false b c = false
and3 true false c = false
and3 true true c = c

record BitTriple : Set where
  constructor bits
  field
    bitA bitB bitC : Bool
open BitTriple public

pairwiseStep : BitTriple → BitTriple
pairwiseStep s = bits
  (xorB (bitB s) (bitC s))
  (xorB (bitA s) (bitC s))
  (xorB (bitA s) (bitB s))

triadicStep : BitTriple → BitTriple
triadicStep s = bits
  (xorB (bitB s) (bitC s))
  (xorB (bitA s) (bitC s))
  (xorB
    (xorB (bitA s) (bitB s))
    (and3 (bitA s) (bitB s) (bitC s)))

-- Coordinate-face agreements: setting any one input to false annihilates the
-- pure three-way term, so the transition laws become literally identical.
faceA0Agreement : (b c : Bool) →
  pairwiseStep (bits false b c) ≡ triadicStep (bits false b c)
faceA0Agreement b c = refl

faceB0Agreement : (a c : Bool) →
  pairwiseStep (bits a false c) ≡ triadicStep (bits a false c)
faceB0Agreement false c = refl
faceB0Agreement true c = refl

faceC0Agreement : (a b : Bool) →
  pairwiseStep (bits a b false) ≡ triadicStep (bits a b false)
faceC0Agreement false b = refl
faceC0Agreement true false = refl
faceC0Agreement true true = refl

ones : BitTriple
ones = bits true true true

zeros : BitTriple
zeros = bits false false false

triadicInteriorOutput : BitTriple
triadicInteriorOutput = bits false false true

pairwise111 : pairwiseStep ones ≡ zeros
pairwise111 = refl

triadic111 : triadicStep ones ≡ triadicInteriorOutput
triadic111 = refl

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

interiorOutputsDiffer : pairwiseStep ones ≡ triadicStep ones → ⊥
interiorOutputsDiffer equality =
  falseNotTrue (cong bitC equality)

record FaceMatchedTriadicCausalPair : Set where
  constructor face-matched-triadic-causal-pair
  field
    agreeWhenAZero : (b c : Bool) →
      pairwiseStep (bits false b c) ≡ triadicStep (bits false b c)
    agreeWhenBZero : (a c : Bool) →
      pairwiseStep (bits a false c) ≡ triadicStep (bits a false c)
    agreeWhenCZero : (a b : Bool) →
      pairwiseStep (bits a b false) ≡ triadicStep (bits a b false)
    differAtThreeWayInterior : pairwiseStep ones ≡ triadicStep ones → ⊥
open FaceMatchedTriadicCausalPair public

canonicalFaceMatchedTriadicCausalPair : FaceMatchedTriadicCausalPair
canonicalFaceMatchedTriadicCausalPair =
  face-matched-triadic-causal-pair
    faceA0Agreement
    faceB0Agreement
    faceC0Agreement
    interiorOutputsDiffer
