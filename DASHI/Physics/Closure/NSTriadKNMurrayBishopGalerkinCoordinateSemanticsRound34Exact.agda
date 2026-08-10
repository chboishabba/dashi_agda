module DASHI.Physics.Closure.NSTriadKNMurrayBishopGalerkinCoordinateSemanticsRound34Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Errett Bishop; Douglas Bridges.
-- Title: "Constructive Analysis".
-- Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Author: Zachary Murray.
-- Title: "Constructive Analysis in the Agda Proof Assistant".
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354; persistent identifier: 10.48550/arXiv.2205.08354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Correct the scalar mismatch in the old Round-26/30 ODE bridge.  The syntax
-- of a Galerkin coordinate equation has rational coefficients, but the state
-- variables of the physical ODE must live in a complete real carrier.  Using
-- Q itself as the trajectory carrier would therefore be wrong.
--
-- This module keeps the existing exact rational atom syntax and gives it a
-- literal semantics in the repository's pinned Murray--Bishop constructive
-- reals.  Rational coefficients are embedded by Bishop's constant-sequence
-- embedding, while state variables are genuine Bishop reals.
--
-- The key algebraic theorem is proved again on that real carrier:
--
--   c x y - c u v
--     = c ((x-u)y + u(y-v)),
--
-- together with the linear case and arbitrary finite sums.  Equality is
-- Bishop's extensional setoid equality, not Agda propositional equality.
-- Thus the degree-two finite Galerkin Lipschitz algebra is no longer tied to
-- an incomplete rational state space.
--
-- This is a real semantic producer, not yet Picard--Lindelof: local existence
-- still requires a finite-dimensional norm/contraction theorem on this
-- Bishop-real assignment carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as Rational using (ℚ; toℚᵘ)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial

BishopAssignment : Set
BishopAssignment = Polynomial.CoordinateVariable → BishopReal.ℝ

bishopRationalEmbed : ℚ → BishopReal.ℝ
bishopRationalEmbed rational = BishopReal._⋆ (toℚᵘ rational)

bishopEvaluateAtom :
  Polynomial.GalerkinCoordinateAtom →
  BishopAssignment → BishopReal.ℝ
bishopEvaluateAtom
    (Polynomial.viscousLinear output component coefficient) state =
  BishopReal._*_
    (bishopRationalEmbed coefficient)
    (state component)
bishopEvaluateAtom
    (Polynomial.resonantBilinear triad left right coefficient) state =
  BishopReal._*_
    (BishopReal._*_
      (bishopRationalEmbed coefficient)
      (state left))
    (state right)

bishopEvaluateAtoms :
  List Polynomial.GalerkinCoordinateAtom →
  BishopAssignment → BishopReal.ℝ
bishopEvaluateAtoms [] state = BishopReal.0ℝ
bishopEvaluateAtoms (atom ∷ rest) state =
  BishopReal._+_
    (bishopEvaluateAtom atom state)
    (bishopEvaluateAtoms rest state)

bishopDifferenceAtom :
  Polynomial.GalerkinCoordinateAtom →
  BishopAssignment → BishopAssignment → BishopReal.ℝ
bishopDifferenceAtom
    (Polynomial.viscousLinear output component coefficient)
    state reference =
  BishopReal._*_
    (bishopRationalEmbed coefficient)
    (BishopReal._-_ (state component) (reference component))
bishopDifferenceAtom
    (Polynomial.resonantBilinear triad left right coefficient)
    state reference =
  BishopReal._*_
    (bishopRationalEmbed coefficient)
    (BishopReal._+_
      (BishopReal._*_
        (BishopReal._-_ (state left) (reference left))
        (state right))
      (BishopReal._*_
        (reference left)
        (BishopReal._-_ (state right) (reference right))))

bishopDifferenceAtoms :
  List Polynomial.GalerkinCoordinateAtom →
  BishopAssignment → BishopAssignment → BishopReal.ℝ
bishopDifferenceAtoms [] state reference = BishopReal.0ℝ
bishopDifferenceAtoms (atom ∷ rest) state reference =
  BishopReal._+_
    (bishopDifferenceAtom atom state reference)
    (bishopDifferenceAtoms rest state reference)

bishopLinearAtomDifferenceFactorisation :
  ∀ output component coefficient state reference →
  BishopReal._≃_
    (BishopReal._-_
      (bishopEvaluateAtom
        (Polynomial.viscousLinear output component coefficient) state)
      (bishopEvaluateAtom
        (Polynomial.viscousLinear output component coefficient) reference))
    (bishopDifferenceAtom
      (Polynomial.viscousLinear output component coefficient)
      state reference)
bishopLinearAtomDifferenceFactorisation
    output component coefficient state reference =
  let open BishopProperties.ℝ-Solver
  in solve 3
      (λ c x u →
        (c ⊗ x) ⊖ (c ⊗ u)
        ⊜ c ⊗ (x ⊖ u))
      BishopProperties.≃-refl
      (bishopRationalEmbed coefficient)
      (state component)
      (reference component)

bishopBilinearAtomDifferenceFactorisation :
  ∀ triad left right coefficient state reference →
  BishopReal._≃_
    (BishopReal._-_
      (bishopEvaluateAtom
        (Polynomial.resonantBilinear triad left right coefficient) state)
      (bishopEvaluateAtom
        (Polynomial.resonantBilinear triad left right coefficient) reference))
    (bishopDifferenceAtom
      (Polynomial.resonantBilinear triad left right coefficient)
      state reference)
bishopBilinearAtomDifferenceFactorisation
    triad left right coefficient state reference =
  let open BishopProperties.ℝ-Solver
  in solve 5
      (λ c x u y v →
        ((c ⊗ x) ⊗ y) ⊖ ((c ⊗ u) ⊗ v)
        ⊜ c ⊗ (((x ⊖ u) ⊗ y) ⊕ (u ⊗ (y ⊖ v))))
      BishopProperties.≃-refl
      (bishopRationalEmbed coefficient)
      (state left)
      (reference left)
      (state right)
      (reference right)

bishopAtomDifferenceFactorisation :
  (atom : Polynomial.GalerkinCoordinateAtom) →
  (state reference : BishopAssignment) →
  BishopReal._≃_
    (BishopReal._-_
      (bishopEvaluateAtom atom state)
      (bishopEvaluateAtom atom reference))
    (bishopDifferenceAtom atom state reference)
bishopAtomDifferenceFactorisation
    (Polynomial.viscousLinear output component coefficient) =
  bishopLinearAtomDifferenceFactorisation output component coefficient
bishopAtomDifferenceFactorisation
    (Polynomial.resonantBilinear triad left right coefficient) =
  bishopBilinearAtomDifferenceFactorisation triad left right coefficient

bishopFiniteGalerkinDifferenceFactorisation :
  (atoms : List Polynomial.GalerkinCoordinateAtom) →
  (state reference : BishopAssignment) →
  BishopReal._≃_
    (BishopReal._-_
      (bishopEvaluateAtoms atoms state)
      (bishopEvaluateAtoms atoms reference))
    (bishopDifferenceAtoms atoms state reference)
bishopFiniteGalerkinDifferenceFactorisation [] state reference =
  let open BishopProperties.ℝ-Solver
  in solve 0
      (Κ Data.Rational.Unnormalised.0ℚᵘ
       ⊖ Κ Data.Rational.Unnormalised.0ℚᵘ
       ⊜ Κ Data.Rational.Unnormalised.0ℚᵘ)
      BishopProperties.≃-refl
bishopFiniteGalerkinDifferenceFactorisation (atom ∷ rest) state reference =
  BishopProperties.≃-trans
    (let open BishopProperties.ℝ-Solver
     in solve 4
        (λ a b c d →
          (a ⊕ b) ⊖ (c ⊕ d)
          ⊜ (a ⊖ c) ⊕ (b ⊖ d))
        BishopProperties.≃-refl
        (bishopEvaluateAtom atom state)
        (bishopEvaluateAtoms rest state)
        (bishopEvaluateAtom atom reference)
        (bishopEvaluateAtoms rest reference))
    (BishopProperties.+-cong
      (bishopAtomDifferenceFactorisation atom state reference)
      (bishopFiniteGalerkinDifferenceFactorisation rest state reference))

bishopCoordinateRightHandSide :
  Polynomial.LiteralGalerkinCoordinateEquation →
  BishopAssignment → BishopReal.ℝ
bishopCoordinateRightHandSide equation =
  bishopEvaluateAtoms (Polynomial.rightHandSideAtoms equation)

bishopCoordinateRightHandSideDifference :
  (equation : Polynomial.LiteralGalerkinCoordinateEquation) →
  (state reference : BishopAssignment) →
  BishopReal._≃_
    (BishopReal._-_
      (bishopCoordinateRightHandSide equation state)
      (bishopCoordinateRightHandSide equation reference))
    (bishopDifferenceAtoms
      (Polynomial.rightHandSideAtoms equation) state reference)
bishopCoordinateRightHandSideDifference equation =
  bishopFiniteGalerkinDifferenceFactorisation
    (Polynomial.rightHandSideAtoms equation)

record BishopLiteralFiniteGalerkinCoordinateEquation : Set where
  constructor bishop-literal-finite-galerkin-coordinate-equation
  field
    rationalEquation : Polynomial.LiteralGalerkinCoordinateEquation
    realRightHandSide : BishopAssignment → BishopReal.ℝ
    realRightHandSideExact : ∀ assignment →
      BishopReal._≃_
        (realRightHandSide assignment)
        (bishopCoordinateRightHandSide rationalEquation assignment)

open BishopLiteralFiniteGalerkinCoordinateEquation public

canonicalBishopLiteralEquation :
  Polynomial.LiteralGalerkinCoordinateEquation →
  BishopLiteralFiniteGalerkinCoordinateEquation
canonicalBishopLiteralEquation equation =
  bishop-literal-finite-galerkin-coordinate-equation
    equation
    (bishopCoordinateRightHandSide equation)
    (λ assignment → BishopProperties.≃-refl)

murrayBishopGalerkinPolynomialSemanticsClosed : Bool
murrayBishopGalerkinPolynomialSemanticsClosed = true

physicalBishopCoordinateEquivalenceConstructed : Bool
physicalBishopCoordinateEquivalenceConstructed = false

murrayBishopGalerkinPolynomialSemanticsClosedIsTrue :
  murrayBishopGalerkinPolynomialSemanticsClosed ≡ true
murrayBishopGalerkinPolynomialSemanticsClosedIsTrue = refl

physicalBishopCoordinateEquivalenceConstructedIsFalse :
  physicalBishopCoordinateEquivalenceConstructed ≡ false
physicalBishopCoordinateEquivalenceConstructedIsFalse = refl
