module DASHI.Crypto.TransformLocalFibreGeometryExact where

------------------------------------------------------------------------
-- EXACT COORDINATE TRANSFORMS / NTT-CRT BOUNDARY
--
-- An invertible representation change can expose useful local coordinates but
-- cannot, by itself, quotient away search states. Any search reduction must
-- come from verifier/reconciliation structure in those coordinates.
--
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- No theorem below asserts that the concrete ML-KEM NTT is an independent CRT
-- field decomposition. That same-object bridge remains an explicit obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record ExactCoordinateTransform : Set₁ where
  constructor exactCoordinateTransform
  field
    Carrier Coordinates : Set
    encode : Carrier → Coordinates
    decode : Coordinates → Carrier
    decodeEncode : ∀ x → decode (encode x) ≡ x
    encodeDecode : ∀ y → encode (decode y) ≡ y

open ExactCoordinateTransform public

encodeInjective :
  ∀ {transform : ExactCoordinateTransform} {x y : Carrier transform} →
  encode transform x ≡ encode transform y → x ≡ y
encodeInjective {transform} {x} {y} sameEncoded =
  trans (sym (decodeEncode transform x))
        (trans (cong (decode transform) sameEncoded)
               (decodeEncode transform y))

exactTransformPreservesDistinctness :
  ∀ {transform : ExactCoordinateTransform} {x y : Carrier transform} →
  (x ≡ y → ⊥) → encode transform x ≡ encode transform y → ⊥
exactTransformPreservesDistinctness different sameEncoded =
  different (encodeInjective sameEncoded)

decodeInjective :
  ∀ {transform : ExactCoordinateTransform} {x y : Coordinates transform} →
  decode transform x ≡ decode transform y → x ≡ y
decodeInjective {transform} {x} {y} sameDecoded =
  trans (sym (encodeDecode transform x))
        (trans (cong (encode transform) sameDecoded)
               (encodeDecode transform y))

record CandidateGeometry (transform : ExactCoordinateTransform) : Set₁ where
  constructor candidateGeometry
  field
    Candidate : Carrier transform → Set

open CandidateGeometry public

TransformedCandidate :
  ∀ {transform} → CandidateGeometry transform → Coordinates transform → Set
TransformedCandidate {transform} geometry coordinates =
  Candidate geometry (decode transform coordinates)

candidateBackwardPreserved :
  ∀ {transform}
    (geometry : CandidateGeometry transform)
    (y : Coordinates transform) →
  TransformedCandidate geometry y → Candidate geometry (decode transform y)
candidateBackwardPreserved geometry y candidate = candidate

record TwoCoordinateSearchGeometry
    (transform : ExactCoordinateTransform) : Set₁ where
  constructor twoCoordinateSearchGeometry
  field
    Local₀ Local₁ : Set
    split : Coordinates transform → Local₀ × Local₁
    join : Local₀ × Local₁ → Coordinates transform
    joinSplit : ∀ y → join (split y) ≡ y
    splitJoin : ∀ p → split (join p) ≡ p
    LocalPlausible₀ : Local₀ → Set
    LocalPlausible₁ : Local₁ → Set
    Coupling : Local₀ → Local₁ → Set

open TwoCoordinateSearchGeometry public

record SearchFactorisationEvidence
    {transform : ExactCoordinateTransform}
    (geometry : TwoCoordinateSearchGeometry transform) : Set₁ where
  constructor searchFactorisationEvidence
  field
    solve₀ : Local₀ geometry
    solve₁ : Local₁ geometry
    local₀Valid : LocalPlausible₀ geometry solve₀
    local₁Valid : LocalPlausible₁ geometry solve₁
    couplingValid : Coupling geometry solve₀ solve₁
