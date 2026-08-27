module DASHI.Core.BinaryInteractionNonseparabilityExact where

------------------------------------------------------------------------
-- GENERIC BINARY INTERACTION / NONSEPARABILITY
--
-- MATHEMATICAL NEIGHBOURHOOD
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", 2nd ed., Cambridge University Press, 2013.
-- DOI: 10.1017/CBO9781139020411.
--
-- INTERNAL THEOREM-PATTERN PROVENANCE
--
-- This owner extracts the domain-neutral algebraic seam independently reached
-- on draft PR #621 (`TransitionActionNonseparabilityExact`) and draft PR #622
-- (`RiemannG21PrimePairKernelExact`).  Those branches are inspiration/provenance
-- only: this module imports neither draft and creates no cyclic ancestry.
--
-- SOURCE SCOPE
--
-- Horn--Johnson is background for matrix/rank-one language.  The additive
-- endpoint-separability interface and rectangle obstruction below are elementary
-- DASHI constructions and are not attributed as theorems of that source.
--
-- CENTRAL DISTINCTIONS
--
--   two-argument surface != genuine interaction
--   additive endpoint separability != arbitrary pair dependence
--   additive rectangle obstruction != rank-one multiplicative obstruction
--   structural nonseparability != empirical/physical causal interaction
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- A finite/discrete response surface with Nat-valued code.
------------------------------------------------------------------------

record BinaryNatSurface : Set₁ where
  constructor binary-nat-surface
  field
    Left Right : Set
    response : Left → Right → Nat
    surfaceReading : String

open BinaryNatSurface public

------------------------------------------------------------------------
-- Endpoint-additive separability.
------------------------------------------------------------------------

record EndpointAdditivelySeparable (surface : BinaryNatSurface) : Set₁ where
  constructor endpoint-additively-separable
  field
    leftPotential : Left surface → Nat
    rightPotential : Right surface → Nat
    decomposition :
      (left : Left surface) →
      (right : Right surface) →
      response surface left right
      ≡ leftPotential left + rightPotential right

open EndpointAdditivelySeparable public

NonseparableAdditiveInteraction : BinaryNatSurface → Set₁
NonseparableAdditiveInteraction surface =
  EndpointAdditivelySeparable surface → ⊥

------------------------------------------------------------------------
-- Rectangle identity forced by every additive endpoint decomposition.
------------------------------------------------------------------------

natRectangleRearrange :
  (a b c d : Nat) →
  (a + c) + (b + d) ≡ (a + d) + (b + c)
natRectangleRearrange a b c d =
  trans
    (trans
      (sym (+-assoc a c (b + d)))
      (trans
        (cong (λ z → a + z)
          (trans
            (+-assoc c b d)
            (trans
              (cong (λ z → z + d) (+-comm c b))
              (sym (+-assoc b c d)))))
        (+-assoc a b (c + d))))
    (sym
      (trans
        (trans
          (sym (+-assoc a d (b + c)))
          (trans
            (cong (λ z → a + z)
              (trans
                (+-assoc d b c)
                (trans
                  (cong (λ z → z + c) (+-comm d b))
                  (sym (+-assoc b d c)))))
            (+-assoc a b (d + c))))
        (cong (λ z → (a + b) + z) (+-comm d c))))

endpointSeparableImpliesRectangle :
  (surface : BinaryNatSurface) →
  EndpointAdditivelySeparable surface →
  (a b : Left surface) →
  (c d : Right surface) →
  response surface a c + response surface b d
  ≡ response surface a d + response surface b c
endpointSeparableImpliesRectangle surface separable a b c d =
  trans
    (cong
      (λ z → z + response surface b d)
      (decomposition separable a c))
    (trans
      (cong
        (λ z →
          (leftPotential separable a + rightPotential separable c) + z)
        (decomposition separable b d))
      (trans
        (natRectangleRearrange
          (leftPotential separable a)
          (leftPotential separable b)
          (rightPotential separable c)
          (rightPotential separable d))
        (trans
          (cong
            (λ z → z +
              (leftPotential separable b + rightPotential separable c))
            (sym (decomposition separable a d)))
          (cong
            (λ z → response surface a d + z)
            (sym (decomposition separable b c))))))

record RectangleObstruction (surface : BinaryNatSurface) : Set where
  constructor rectangle-obstruction
  field
    a b : Left surface
    c d : Right surface
    rectangleEqualityImpossible :
      response surface a c + response surface b d
      ≡ response surface a d + response surface b c
      → ⊥

open RectangleObstruction public

rectangleObstructionBlocksEndpointSeparation :
  {surface : BinaryNatSurface} →
  RectangleObstruction surface →
  NonseparableAdditiveInteraction surface
rectangleObstructionBlocksEndpointSeparation obstruction separable =
  rectangleEqualityImpossible obstruction
    (endpointSeparableImpliesRectangle
      _ separable
      (a obstruction) (b obstruction)
      (c obstruction) (d obstruction))

------------------------------------------------------------------------
-- Independent rank-one/minor obstruction.
--
-- This is deliberately separate: failure of additive endpoint separation and
-- failure of multiplicative rank-one factorisation are different predicates.
------------------------------------------------------------------------

record RankOneMinorObstruction (surface : BinaryNatSurface) : Set where
  constructor rank-one-minor-obstruction
  field
    a b : Left surface
    c d : Right surface
    minorEqualityImpossible :
      response surface a c * response surface b d
      ≡ response surface a d * response surface b c
      → ⊥

open RankOneMinorObstruction public

record StrongBinaryInteractionAdmission (surface : BinaryNatSurface) : Set where
  constructor strong-binary-interaction-admission
  field
    additiveRectangleObstruction : RectangleObstruction surface
    multiplicativeRankOneObstruction : RankOneMinorObstruction surface

open StrongBinaryInteractionAdmission public

strongAdmissionImpliesAdditiveNonseparability :
  {surface : BinaryNatSurface} →
  StrongBinaryInteractionAdmission surface →
  NonseparableAdditiveInteraction surface
strongAdmissionImpliesAdditiveNonseparability admission =
  rectangleObstructionBlocksEndpointSeparation
    (additiveRectangleObstruction admission)

------------------------------------------------------------------------
-- Exact two-point regression: mismatch relation.
------------------------------------------------------------------------

data BitPoint : Set where
  bit0 bit1 : BitPoint

mismatchCode : BitPoint → BitPoint → Nat
mismatchCode bit0 bit0 = 0
mismatchCode bit0 bit1 = 1
mismatchCode bit1 bit0 = 1
mismatchCode bit1 bit1 = 0

mismatchSurface : BinaryNatSurface
mismatchSurface =
  binary-nat-surface
    BitPoint BitPoint mismatchCode
    "Two-point mismatch regression: diagonal zero and off-diagonal one."

mismatchRectangleObstruction : RectangleObstruction mismatchSurface
mismatchRectangleObstruction =
  rectangle-obstruction bit0 bit1 bit0 bit1 (λ ())

mismatchRankOneObstruction : RankOneMinorObstruction mismatchSurface
mismatchRankOneObstruction =
  rank-one-minor-obstruction bit0 bit1 bit0 bit1 (λ ())

mismatchStrongInteraction : StrongBinaryInteractionAdmission mismatchSurface
mismatchStrongInteraction =
  strong-binary-interaction-admission
    mismatchRectangleObstruction
    mismatchRankOneObstruction

mismatchIsNotEndpointAdditive :
  NonseparableAdditiveInteraction mismatchSurface
mismatchIsNotEndpointAdditive =
  strongAdmissionImpliesAdditiveNonseparability mismatchStrongInteraction

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record BinaryInteractionNonseparabilityBoundary : Set where
  constructor binary-interaction-nonseparability-boundary
  field
    pairValuedImpliesInteraction : Bool
    pairValuedImpliesInteractionIsFalse : pairValuedImpliesInteraction ≡ false
    rectangleObstructionBlocksAdditiveEndpointModel : Bool
    rectangleObstructionBlocksAdditiveEndpointModelIsTrue :
      rectangleObstructionBlocksAdditiveEndpointModel ≡ true
    additiveNonseparabilityEqualsRankOneFailure : Bool
    additiveNonseparabilityEqualsRankOneFailureIsFalse :
      additiveNonseparabilityEqualsRankOneFailure ≡ false
    structuralInteractionProvesEmpiricalCausation : Bool
    structuralInteractionProvesEmpiricalCausationIsFalse :
      structuralInteractionProvesEmpiricalCausation ≡ false

canonicalBinaryInteractionNonseparabilityBoundary :
  BinaryInteractionNonseparabilityBoundary
canonicalBinaryInteractionNonseparabilityBoundary =
  binary-interaction-nonseparability-boundary
    false refl
    true refl
    false refl
    false refl
