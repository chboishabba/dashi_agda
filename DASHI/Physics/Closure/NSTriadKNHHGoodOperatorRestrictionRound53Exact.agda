module DASHI.Physics.Closure.NSTriadKNHHGoodOperatorRestrictionRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- DOI: 10.1007/BF01240221.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 49 stated continuum restriction pointwise after supplying one omega.
-- The physical object is an operator-valued Fourier multiplier.  This file
-- freezes that stronger theorem surface: for every embedded lattice mode the
-- continuum operator agrees extensionally, on every lattice vorticity vector,
-- with the literal annular strain operator.  Thus no proof may identify only a
-- single test vector and silently promote it to operator equality.
--
-- This is still a same-object interface, not an assertion that the required
-- R^3 smooth compactly supported extension has already been constructed.  The
-- latter remains the substantive physical/analytic producer.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNHHGoodLiteralAnnularStrainSymbolRound48Exact as Literal

infix 4 _≗_
_≗_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → (A → B) → Set (a ⊔ b)
f ≗ g = ∀ x → f x ≡ g x

literalAnnularStrainOperator :
  Literal.LiteralAnnularStrainCutoff →
  V.ProjectionMode →
  V.Vector3 → Matrix.Matrix3
literalAnnularStrainOperator cutoff modeData =
  Literal.literalAnnularStrainSymbol cutoff modeData

record PhysicalHHGoodContinuumOperatorRestriction
    {c : Level}
    (ContinuumMode : Set c)
    (cutoff : Literal.LiteralAnnularStrainCutoff) : Set (lsuc c) where
  field
    ContinuumVorticity : Set c
    embedProjectionMode : V.ProjectionMode → ContinuumMode
    embedVorticity : V.Vector3 → ContinuumVorticity

    continuumAnnularStrainOperator :
      ContinuumMode → ContinuumVorticity → Matrix.Matrix3

    physicalHHGoodContinuumOperatorRestriction :
      ∀ modeData →
      (λ omega →
        continuumAnnularStrainOperator
          (embedProjectionMode modeData)
          (embedVorticity omega))
      ≗ literalAnnularStrainOperator cutoff modeData

open PhysicalHHGoodContinuumOperatorRestriction public

operatorRestrictionImpliesPointwiseRestriction :
  ∀ {c} {ContinuumMode : Set c} {cutoff}
    (physical : PhysicalHHGoodContinuumOperatorRestriction ContinuumMode cutoff)
    modeData omega →
  continuumAnnularStrainOperator physical
      (embedProjectionMode physical modeData)
      (embedVorticity physical omega)
  ≡ Literal.literalAnnularStrainSymbol cutoff modeData omega
operatorRestrictionImpliesPointwiseRestriction physical modeData omega =
  physicalHHGoodContinuumOperatorRestriction physical modeData omega

operatorValuedRestrictionSurfaceConstructed : Bool
operatorValuedRestrictionSurfaceConstructed = true

physicalSmoothR3OperatorExtensionConstructed : Bool
physicalSmoothR3OperatorExtensionConstructed = false

operatorValuedRestrictionSurfaceConstructedIsTrue :
  operatorValuedRestrictionSurfaceConstructed ≡ true
operatorValuedRestrictionSurfaceConstructedIsTrue = refl

physicalSmoothR3OperatorExtensionConstructedIsFalse :
  physicalSmoothR3OperatorExtensionConstructed ≡ false
physicalSmoothR3OperatorExtensionConstructedIsFalse = refl
