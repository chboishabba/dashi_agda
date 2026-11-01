module DASHI.Physics.Closure.NSTriadKNLiteralAdvectivePressureRHSSplitRound84Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND84 / SOURCE-NATIVE ADVECTIVE--PRESSURE SPLIT
--
-- The literal Galerkin interaction already used by the repository is
--
--   -i P_k w,
--
-- where
--
--   w = (u_p dot q) u_q,
--   P_k w = w - |k|^{-2} (k dot w) k.
--
-- This module opens that exact definition and proves
--
--   -i P_k w
--     = (-i w) + i |k|^{-2} (k dot w) k.
--
-- The second summand is therefore not a post-hoc observational residual: it
-- is exactly the longitudinal Leray correction, i.e. the Fourier pressure-
-- gradient contribution carried by the same ordered triad and the same mode.
-- We then lift the identity through the literal finite physical-output fibre:
--
--   projectedNonlinearity(u)(k)
--     = advectiveNonlinearity(u)(k) + pressureNonlinearity(u)(k).
--
-- No sign estimate, pressure-Hessian identification, continuum limit, or
-- function-extensionality axiom is used here.  The next seam is explicitly the
-- same-mode gradient-to-Hessian bridge required by the Round78 pressure /
-- stretching budget.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as First

------------------------------------------------------------------------
-- Coordinatewise C3 scaling laws needed to expose the Leray subtraction.
------------------------------------------------------------------------

complex3ScaleAdd :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (left right : C3.Complex3 F) →
  C3.complex3Scale scalar (C3.complex3Add left right)
  ≡ C3.complex3Add
      (C3.complex3Scale scalar left)
      (C3.complex3Scale scalar right)
complex3ScaleAdd scalar
    (C3.complex3 lx ly lz) (C3.complex3 rx ry rz)
  rewrite Algebra.complexMultiplyDistributesLeft scalar lx rx
        | Algebra.complexMultiplyDistributesLeft scalar ly ry
        | Algebra.complexMultiplyDistributesLeft scalar lz rz = refl

complex3ScaleNegate :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (value : C3.Complex3 F) →
  C3.complex3Scale scalar (C3.complex3Negate value)
  ≡ C3.complex3Negate (C3.complex3Scale scalar value)
complex3ScaleNegate scalar (C3.complex3 vx vy vz)
  rewrite Field.complexNegateMultiplyRight scalar vx
        | Field.complexNegateMultiplyRight scalar vy
        | Field.complexNegateMultiplyRight scalar vz = refl

complex3ScaleSubtract :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (left right : C3.Complex3 F) →
  C3.complex3Scale scalar (C3.complex3Subtract left right)
  ≡ C3.complex3Subtract
      (C3.complex3Scale scalar left)
      (C3.complex3Scale scalar right)
complex3ScaleSubtract scalar left right =
  trans
    (complex3ScaleAdd scalar left (C3.complex3Negate right))
    (cong (C3.complex3Add (C3.complex3Scale scalar left))
      (complex3ScaleNegate scalar right))

complex3AddZeroLeft :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex3 F) →
  C3.complex3Add (C3.complex3Zero F) value ≡ value
complex3AddZeroLeft (C3.complex3 vx vy vz)
  rewrite Field.complexAddZeroLeft vx
        | Field.complexAddZeroLeft vy
        | Field.complexAddZeroLeft vz = refl

------------------------------------------------------------------------
-- The actual rank-one term already present in P_k.
------------------------------------------------------------------------

minusImaginary :
  ∀ {r} (F : C3.RealField r) → C3.Complex F
minusImaginary F = C3.complexNegate (C3.complexI F)

rawOrderedValue :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
rawOrderedValue {F = F} {E = E} system incidence =
  C3.complex3Scale
    (C3.bilinearDot3
      (Audit.velocity system (Physical.p incidence))
      (C3.modeVector E (Physical.q incidence)))
    (Audit.velocity system (Physical.q incidence))

lerayRankOneCorrection :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
lerayRankOneCorrection {F = F} {E = E} {I = I} system incidence =
  let
    output = Physical.k incidence
    value = rawOrderedValue system incidence
  in
  C3.complex3Scale
    (C3.complexMultiply
      (C3.realEmbed F (C3.inverseNormSquared I output))
      (C3.bilinearDot3 (C3.modeVector E output) value))
    (C3.modeVector E output)

advectiveOrderedTerm :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
advectiveOrderedTerm {F = F} system incidence =
  C3.complex3Scale (minusImaginary F) (rawOrderedValue system incidence)

pressureOrderedTerm :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
pressureOrderedTerm {F = F} system incidence =
  C3.complex3Negate
    (C3.complex3Scale
      (minusImaginary F)
      (lerayRankOneCorrection system incidence))

-- The pressure term is literally +i times the longitudinal rank-one
-- correction.  Keeping the preceding definition as a negated -i term makes
-- the P_k subtraction split definitionally transparent; this theorem records
-- the usual Fourier pressure-gradient form explicitly.
pressureOrderedTermIsPlusImaginaryRankOne :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  pressureOrderedTerm system incidence
  ≡ C3.complex3Scale
      (C3.complexI F)
      (lerayRankOneCorrection system incidence)
pressureOrderedTermIsPlusImaginaryRankOne {F = F} system incidence =
  trans
    (Field.complex3NegateScale
      (minusImaginary F)
      (lerayRankOneCorrection system incidence))
    (cong
      (λ scalar → C3.complex3Scale scalar
        (lerayRankOneCorrection system incidence))
      (Field.complexNegateInvolutive (C3.complexI F)))

projectedOrderedTermSplitsExactly :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  Audit.projectedOrderedTerm system incidence
  ≡ C3.complex3Add
      (advectiveOrderedTerm system incidence)
      (pressureOrderedTerm system incidence)
projectedOrderedTermSplitsExactly {F = F} system incidence =
  complex3ScaleSubtract
    (minusImaginary F)
    (rawOrderedValue system incidence)
    (lerayRankOneCorrection system incidence)

------------------------------------------------------------------------
-- Lift the local identity through exactly the physical output fibre used by N.
------------------------------------------------------------------------

mapAdvectiveTerms :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
mapAdvectiveTerms system [] = []
mapAdvectiveTerms system (incidence ∷ rest) =
  advectiveOrderedTerm system incidence ∷ mapAdvectiveTerms system rest

mapPressureTerms :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
mapPressureTerms system [] = []
mapPressureTerms system (incidence ∷ rest) =
  pressureOrderedTerm system incidence ∷ mapPressureTerms system rest

sumTriadTermsSplitsExactly :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidences : List Physical.PhysicalTriadIncidence) →
  Audit.sumVectors (Audit.mapTriadTerms system incidences)
  ≡ C3.complex3Add
      (Audit.sumVectors (mapAdvectiveTerms system incidences))
      (Audit.sumVectors (mapPressureTerms system incidences))
sumTriadTermsSplitsExactly {F = F} system [] =
  sym (complex3AddZeroLeft (C3.complex3Zero F))
sumTriadTermsSplitsExactly system (incidence ∷ rest) =
  let
    adv = advectiveOrderedTerm system incidence
    pres = pressureOrderedTerm system incidence
    advRest = Audit.sumVectors (mapAdvectiveTerms system rest)
    presRest = Audit.sumVectors (mapPressureTerms system rest)
  in
  trans
    (cong₂ C3.complex3Add
      (projectedOrderedTermSplitsExactly system incidence)
      (sumTriadTermsSplitsExactly system rest))
    (First.complex3Interchange adv pres advRest presRest)

advectiveNonlinearity :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
advectiveNonlinearity system output =
  Audit.sumVectors
    (mapAdvectiveTerms system (Audit.concreteTriadsAt system output))

pressureNonlinearity :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → C3.Complex3 F
pressureNonlinearity system output =
  Audit.sumVectors
    (mapPressureTerms system (Audit.concreteTriadsAt system output))

projectedNonlinearitySplitsAdvectivePressurePointwise :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  Audit.projectedNonlinearity system output
  ≡ C3.complex3Add
      (advectiveNonlinearity system output)
      (pressureNonlinearity system output)
projectedNonlinearitySplitsAdvectivePressurePointwise system output =
  sumTriadTermsSplitsExactly system (Audit.concreteTriadsAt system output)

round84LiteralOrderedAdvectivePressureSplitConstructed : Bool
round84LiteralOrderedAdvectivePressureSplitConstructed = true

round84LiteralSummedAdvectivePressureSplitConstructed : Bool
round84LiteralSummedAdvectivePressureSplitConstructed = true

round84PressureTermIsLiteralLerayRankOneCorrection : Bool
round84PressureTermIsLiteralLerayRankOneCorrection = true

round84PressureGradientToHessianSameModeBridgeConstructed : Bool
round84PressureGradientToHessianSameModeBridgeConstructed = false

round84LiteralSummedAdvectivePressureSplitConstructedIsTrue :
  round84LiteralSummedAdvectivePressureSplitConstructed ≡ true
round84LiteralSummedAdvectivePressureSplitConstructedIsTrue = refl

round84PressureGradientToHessianSameModeBridgeConstructedIsFalse :
  round84PressureGradientToHessianSameModeBridgeConstructed ≡ false
round84PressureGradientToHessianSameModeBridgeConstructedIsFalse = refl
