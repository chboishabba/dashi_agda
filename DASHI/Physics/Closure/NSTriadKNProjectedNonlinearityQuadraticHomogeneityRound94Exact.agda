module DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityQuadraticHomogeneityRound94Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes Equations
-- in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- ROUND94 / EXACT HOMOGENEITY AUDIT
--
-- The literal projected Fourier nonlinearity is quadratic in the velocity.
-- This file proves on the actual finite output fibre that, for a scalar a,
--
--   projectedNonlinearity(a u)(k)
--     = a^2 projectedNonlinearity(u)(k).
--
-- The proof passes through the exact ordered coefficient, linearity of the
-- literal Leray projector, and the finite output-fibre sum.  This is used by
-- the Round94 phase programme to audit homogeneity before attempting a
-- damping/coercivity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit

squareScalar :
  ∀ {r} {F : C3.RealField r} → C3.Complex F → C3.Complex F
squareScalar scalar = C3.complexMultiply scalar scalar

scaleSubtract :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F) (u v : C3.Complex3 F) →
  C3.complex3Scale scalar (C3.complex3Subtract u v)
  ≡
  C3.complex3Subtract
    (C3.complex3Scale scalar u)
    (C3.complex3Scale scalar v)
scaleSubtract {F = F} scalar
  (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (R.solve 3
      (λ s u v → s R.⊗ (u R.⊕ (R.⊝ v))
        R.⊜ (s R.⊗ u) R.⊕ (R.⊝ (s R.⊗ v)))
      refl scalar ux vx)
    (R.solve 3
      (λ s u v → s R.⊗ (u R.⊕ (R.⊝ v))
        R.⊜ (s R.⊗ u) R.⊕ (R.⊝ (s R.⊗ v)))
      refl scalar uy vy)
    (R.solve 3
      (λ s u v → s R.⊗ (u R.⊕ (R.⊝ v))
        R.⊜ (s R.⊗ u) R.⊕ (R.⊝ (s R.⊗ v)))
      refl scalar uz vz)
  where module R = Ring.Solver F

nestedScale :
  ∀ {r} {F : C3.RealField r}
    (outer inner : C3.Complex F) (v : C3.Complex3 F) →
  C3.complex3Scale outer (C3.complex3Scale inner v)
  ≡ C3.complex3Scale (C3.complexMultiply outer inner) v
nestedScale {F = F} outer inner (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (Scaling.complexMultiplyAssociative outer inner vx)
    (Scaling.complexMultiplyAssociative outer inner vy)
    (Scaling.complexMultiplyAssociative outer inner vz)

scaleAdd :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F) (u v : C3.Complex3 F) →
  C3.complex3Scale scalar (C3.complex3Add u v)
  ≡ C3.complex3Add
      (C3.complex3Scale scalar u)
      (C3.complex3Scale scalar v)
scaleAdd {F = F} scalar
  (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (Ring.complexDistributeLeft scalar ux vx)
    (Ring.complexDistributeLeft scalar uy vy)
    (Ring.complexDistributeLeft scalar uz vz)

scaleZero :
  ∀ {r} {F : C3.RealField r} (scalar : C3.Complex F) →
  C3.complex3Scale scalar (C3.complex3Zero F) ≡ C3.complex3Zero F
scaleZero {F = F} scalar =
  Algebra.complex3Ext
    (Algebra.complexMultiplyZeroRight scalar)
    (Algebra.complexMultiplyZeroRight scalar)
    (Algebra.complexMultiplyZeroRight scalar)

lerayScale :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (scalar : C3.Complex F)
    (value : C3.Complex3 F) →
  C3.lerayProject3 E I k (C3.complex3Scale scalar value)
  ≡ C3.complex3Scale scalar (C3.lerayProject3 E I k value)
lerayScale {F = F} E I k scalar value =
  trans
    (cong
      (C3.complex3Subtract (C3.complex3Scale scalar value))
      correctionScale)
    (sym (scaleSubtract scalar value correction))
  where
  wave = C3.modeVector E k
  inv = C3.realEmbed F (C3.inverseNormSquared I k)
  dot = C3.bilinearDot3 wave value
  correction =
    C3.complex3Scale (C3.complexMultiply inv dot) wave

  correctionScale :
    C3.complex3Scale
      (C3.complexMultiply inv
        (C3.bilinearDot3 wave (C3.complex3Scale scalar value)))
      wave
    ≡ C3.complex3Scale scalar correction
  correctionScale =
    trans
      (cong
        (λ selected → C3.complex3Scale
          (C3.complexMultiply inv selected) wave)
        (Scaling.bilinearDot3ScaleRight scalar wave value))
      (trans
        (cong
          (λ coefficient → C3.complex3Scale coefficient wave)
          (R.solve 3
            (λ inv scalar dot → inv R.⊗ (scalar R.⊗ dot)
              R.⊜ scalar R.⊗ (inv R.⊗ dot))
            refl inv scalar dot))
        (sym (nestedScale scalar (C3.complexMultiply inv dot) wave)))
    where module R = Ring.Solver F

scaleSystem :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  C3.Complex F →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Audit.FiniteComplex3GalerkinSystem F E I
scaleSystem scalar system = record
  { Audit.cutoff = Audit.cutoff system
  ; Audit.modes = Audit.modes system
  ; Audit.triads = Audit.triads system
  ; Audit.velocity = λ mode → C3.complex3Scale scalar (Audit.velocity system mode)
  ; Audit.viscosity = Audit.viscosity system
  ; Audit.modeListed = Audit.modeListed system
  ; Audit.triadListed = Audit.triadListed system
  ; Audit.modesAreLiteralCutoff = Audit.modesAreLiteralCutoff system
  ; Audit.triadsAreLiteralEnumeration = Audit.triadsAreLiteralEnumeration system
  ; Audit.zeroModeExcluded = Audit.zeroModeExcluded system
  ; Audit.realityClosed = Audit.realityClosed system
  }

projectedOrderedTermQuadratic :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (scalar : C3.Complex F)
    (tau : Physical.PhysicalTriadIncidence) →
  Audit.projectedOrderedTerm (scaleSystem scalar system) tau
  ≡ C3.complex3Scale (squareScalar scalar)
      (Audit.projectedOrderedTerm system tau)
projectedOrderedTermQuadratic {F = F} {E = E} {I = I}
    system scalar tau =
  trans
    (cong
      (C3.complex3Scale
        (C3.complexNegate (C3.complexI F)))
      projectedInner)
    outerCommute
  where
  p = Physical.p tau
  q = Physical.q tau
  k = Physical.k tau
  uP = Audit.velocity system p
  uQ = Audit.velocity system q
  waveQ = C3.modeVector E q
  dot = C3.bilinearDot3 uP waveQ
  s2 = squareScalar scalar
  baseInner = C3.complex3Scale dot uQ

  scaledInner :
    C3.complex3Scale
      (C3.bilinearDot3 (C3.complex3Scale scalar uP) waveQ)
      (C3.complex3Scale scalar uQ)
    ≡ C3.complex3Scale s2 baseInner
  scaledInner =
    trans
      (cong
        (λ selected →
          C3.complex3Scale selected (C3.complex3Scale scalar uQ))
        (Scaling.bilinearDot3ScaleLeft scalar uP waveQ))
      (Algebra.complex3Ext
        (R.solve 4
          (λ s d u z → (s R.⊗ d) R.⊗ (s R.⊗ u)
            R.⊜ (s R.⊗ s) R.⊗ (d R.⊗ u))
          refl scalar dot (C3.x uQ) (C3.complexZero F))
        (R.solve 4
          (λ s d u z → (s R.⊗ d) R.⊗ (s R.⊗ u)
            R.⊜ (s R.⊗ s) R.⊗ (d R.⊗ u))
          refl scalar dot (C3.y uQ) (C3.complexZero F))
        (R.solve 4
          (λ s d u z → (s R.⊗ d) R.⊗ (s R.⊗ u)
            R.⊜ (s R.⊗ s) R.⊗ (d R.⊗ u))
          refl scalar dot (C3.z uQ) (C3.complexZero F)))
    where module R = Ring.Solver F

  projectedInner :
    C3.lerayProject3 E I k
      (C3.complex3Scale
        (C3.bilinearDot3 (C3.complex3Scale scalar uP) waveQ)
        (C3.complex3Scale scalar uQ))
    ≡ C3.complex3Scale s2 (C3.lerayProject3 E I k baseInner)
  projectedInner =
    trans
      (cong (C3.lerayProject3 E I k) scaledInner)
      (lerayScale E I k s2 baseInner)

  outerCommute :
    C3.complex3Scale (C3.complexNegate (C3.complexI F))
      (C3.complex3Scale s2 (C3.lerayProject3 E I k baseInner))
    ≡ C3.complex3Scale s2
      (C3.complex3Scale (C3.complexNegate (C3.complexI F))
        (C3.lerayProject3 E I k baseInner))
  outerCommute =
    Algebra.complex3Ext
      (R.solve 3
        (λ minusI s2 x → minusI R.⊗ (s2 R.⊗ x)
          R.⊜ s2 R.⊗ (minusI R.⊗ x))
        refl (C3.complexNegate (C3.complexI F)) s2
          (C3.x (C3.lerayProject3 E I k baseInner)))
      (R.solve 3
        (λ minusI s2 y → minusI R.⊗ (s2 R.⊗ y)
          R.⊜ s2 R.⊗ (minusI R.⊗ y))
        refl (C3.complexNegate (C3.complexI F)) s2
          (C3.y (C3.lerayProject3 E I k baseInner)))
      (R.solve 3
        (λ minusI s2 z → minusI R.⊗ (s2 R.⊗ z)
          R.⊜ s2 R.⊗ (minusI R.⊗ z))
        refl (C3.complexNegate (C3.complexI F)) s2
          (C3.z (C3.lerayProject3 E I k baseInner)))
    where module R = Ring.Solver F

sumMappedTermsQuadratic :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (scalar : C3.Complex F)
    (triads : List Physical.PhysicalTriadIncidence) →
  Audit.sumVectors (Audit.mapTriadTerms (scaleSystem scalar system) triads)
  ≡ C3.complex3Scale (squareScalar scalar)
      (Audit.sumVectors (Audit.mapTriadTerms system triads))
sumMappedTermsQuadratic {F = F} system scalar [] =
  sym (scaleZero (squareScalar scalar))
sumMappedTermsQuadratic system scalar (tau ∷ rest) =
  trans
    (cong₂ C3.complex3Add
      (projectedOrderedTermQuadratic system scalar tau)
      (sumMappedTermsQuadratic system scalar rest))
    (sym
      (scaleAdd (squareScalar scalar)
        (Audit.projectedOrderedTerm system tau)
        (Audit.sumVectors (Audit.mapTriadTerms system rest))))

projectedNonlinearityQuadraticHomogeneous :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (scalar : C3.Complex F)
    (output : Z3.FourierMode) →
  Audit.projectedNonlinearity (scaleSystem scalar system) output
  ≡ C3.complex3Scale (squareScalar scalar)
      (Audit.projectedNonlinearity system output)
projectedNonlinearityQuadraticHomogeneous system scalar output =
  sumMappedTermsQuadratic system scalar
    (Audit.concreteTriadsAt system output)

round94LiteralProjectedNonlinearityQuadraticHomogeneityClosed : Bool
round94LiteralProjectedNonlinearityQuadraticHomogeneityClosed = true

round94LiteralProjectedNonlinearityQuadraticHomogeneityClosedIsTrue :
  round94LiteralProjectedNonlinearityQuadraticHomogeneityClosed ≡ true
round94LiteralProjectedNonlinearityQuadraticHomogeneityClosedIsTrue = refl
