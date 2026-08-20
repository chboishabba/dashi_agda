module DASHI.Physics.Closure.NSTriadKNEigenpacketCrossRadiusRecombinationRound101Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND101 / CROSS-RADIUS RECOMBINATION AUDIT
--
-- Round100 proved that on ONE exact Laplacian eigenspace, with eigenvalue
-- lambda, the nonlinear relative-growth numerator collapses to
--
--   lambda (E qdot - 2 q^2).
--
-- It is tempting to prove this on every eigenspace and then say that dyadic
-- recombination is only Parseval.  That is false for the relative-growth
-- numerator, because it is bilinear in (qdot,D) and (q,Ddot).
--
-- For two exact radii lambda1,lambda2 define
--
--   E = E1+E2,
--   q = q1+q2,
--   qdot = qdot1+qdot2,
--   D = lambda1 E1 + lambda2 E2,
--   Ddot = 2(lambda1 q1 + lambda2 q2).
--
-- Then the exact recombined numerator is the two diagonal eigenpacket
-- numerators PLUS the cross-radius defect
--
--   lambda2 E2 qdot1 + lambda1 E1 qdot2
--     - 2(lambda1+lambda2) q1 q2.
--
-- Equivalently, taking lambda1 as reference, the whole numerator is
--
--   lambda1 ((E1+E2)(qdot1+qdot2) - 2(q1+q2)^2)
--   + (lambda2-lambda1)
--       (E2(qdot1+qdot2) - 2(q1+q2)q2).
--
-- Thus exact-radius scalar viscosity removes radial dispersion only BEFORE
-- recombination.  Merging distinct radii recreates an explicit multiplier
-- commutator proportional to lambda2-lambda1.  When lambda1=lambda2 the defect
-- collapses exactly, as it must.
--
-- This is an exact RealField polynomial identity; no estimate, positivity,
-- cardinality bound, or analytic receipt is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

private
  two : ∀ {r} (F : C3.RealField r) → C3.Carrier F
  two F = C3.add F (C3.one F) (C3.one F)

  square : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F
  square {F = F} x = C3.multiply F x x

  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

recombinedRelativeGrowth :
  ∀ {r} (F : C3.RealField r) →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F
recombinedRelativeGrowth F lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2 =
  sub
    (C3.multiply F
      (C3.add F qdot1 qdot2)
      (C3.add F
        (C3.multiply F lambda1 E1)
        (C3.multiply F lambda2 E2)))
    (C3.multiply F
      (C3.add F q1 q2)
      (C3.multiply F (two F)
        (C3.add F
          (C3.multiply F lambda1 q1)
          (C3.multiply F lambda2 q2))))

diagonalEigenpacketRelativeGrowth :
  ∀ {r} (F : C3.RealField r) →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F
diagonalEigenpacketRelativeGrowth F lambda E q qdot =
  C3.multiply F lambda
    (sub
      (C3.multiply F E qdot)
      (C3.multiply F (two F) (square q)))

crossRadiusDefect :
  ∀ {r} (F : C3.RealField r) →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F
crossRadiusDefect F lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2 =
  sub
    (C3.add F
      (C3.multiply F (C3.multiply F lambda2 E2) qdot1)
      (C3.multiply F (C3.multiply F lambda1 E1) qdot2))
    (C3.multiply F
      (C3.multiply F (two F) (C3.add F lambda1 lambda2))
      (C3.multiply F q1 q2))

recombinedIsDiagonalPlusCrossRadiusDefect :
  ∀ {r} (F : C3.RealField r)
    (lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2 : C3.Carrier F) →
  recombinedRelativeGrowth F lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2
  ≡ C3.add F
      (C3.add F
        (diagonalEigenpacketRelativeGrowth F lambda1 E1 q1 qdot1)
        (diagonalEigenpacketRelativeGrowth F lambda2 E2 q2 qdot2))
      (crossRadiusDefect F lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2)
recombinedIsDiagonalPlusCrossRadiusDefect F
    lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2 =
  P.R.solve 8
    (λ l1 l2 e1 e2 a b da db →
      (((da P.R.⊕ db)
          P.R.⊗ ((l1 P.R.⊗ e1) P.R.⊕ (l2 P.R.⊗ e2)))
        P.R.⊕ P.R.⊝
          ((a P.R.⊕ b)
            P.R.⊗
              ((P.R.K (two F))
                P.R.⊗ ((l1 P.R.⊗ a) P.R.⊕ (l2 P.R.⊗ b)))))
      P.R.⊜
      (((l1 P.R.⊗
          ((e1 P.R.⊗ da)
            P.R.⊕ P.R.⊝ ((P.R.K (two F)) P.R.⊗ (a P.R.⊗ a))))
        P.R.⊕
        (l2 P.R.⊗
          ((e2 P.R.⊗ db)
            P.R.⊕ P.R.⊝ ((P.R.K (two F)) P.R.⊗ (b P.R.⊗ b)))))
        P.R.⊕
        ((((l2 P.R.⊗ e2) P.R.⊗ da)
          P.R.⊕ ((l1 P.R.⊗ e1) P.R.⊗ db))
          P.R.⊕ P.R.⊝
            (((P.R.K (two F)) P.R.⊗ (l1 P.R.⊕ l2))
              P.R.⊗ (a P.R.⊗ b)))))
    refl lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2
  where module P = Field.Polynomial F

referenceRadiusDefect :
  ∀ {r} (F : C3.RealField r) →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F →
  C3.Carrier F
referenceRadiusDefect F lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2 =
  C3.multiply F (sub lambda2 lambda1)
    (sub
      (C3.multiply F E2 (C3.add F qdot1 qdot2))
      (C3.multiply F (two F)
        (C3.multiply F (C3.add F q1 q2) q2)))

recombinedIsReferenceRadiusPlusDifferenceDefect :
  ∀ {r} (F : C3.RealField r)
    (lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2 : C3.Carrier F) →
  recombinedRelativeGrowth F lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2
  ≡ C3.add F
      (diagonalEigenpacketRelativeGrowth F lambda1
        (C3.add F E1 E2)
        (C3.add F q1 q2)
        (C3.add F qdot1 qdot2))
      (referenceRadiusDefect F lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2)
recombinedIsReferenceRadiusPlusDifferenceDefect F
    lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2 =
  P.R.solve 8
    (λ l1 l2 e1 e2 a b da db →
      (((da P.R.⊕ db)
          P.R.⊗ ((l1 P.R.⊗ e1) P.R.⊕ (l2 P.R.⊗ e2)))
        P.R.⊕ P.R.⊝
          ((a P.R.⊕ b)
            P.R.⊗
              ((P.R.K (two F))
                P.R.⊗ ((l1 P.R.⊗ a) P.R.⊕ (l2 P.R.⊗ b)))))
      P.R.⊜
      ((l1 P.R.⊗
          (((e1 P.R.⊕ e2) P.R.⊗ (da P.R.⊕ db))
            P.R.⊕ P.R.⊝
              ((P.R.K (two F))
                P.R.⊗ ((a P.R.⊕ b) P.R.⊗ (a P.R.⊕ b)))))
        P.R.⊕
        ((l2 P.R.⊕ P.R.⊝ l1)
          P.R.⊗
            ((e2 P.R.⊗ (da P.R.⊕ db))
              P.R.⊕ P.R.⊝
                ((P.R.K (two F)) P.R.⊗ ((a P.R.⊕ b) P.R.⊗ b)))))
    refl lambda1 lambda2 E1 E2 q1 q2 qdot1 qdot2
  where module P = Field.Polynomial F

sameRadiusRecombinesExactly :
  ∀ {r} (F : C3.RealField r)
    (lambda E1 E2 q1 q2 qdot1 qdot2 : C3.Carrier F) →
  recombinedRelativeGrowth F lambda lambda E1 E2 q1 q2 qdot1 qdot2
  ≡ diagonalEigenpacketRelativeGrowth F lambda
      (C3.add F E1 E2)
      (C3.add F q1 q2)
      (C3.add F qdot1 qdot2)
sameRadiusRecombinesExactly F lambda E1 E2 q1 q2 qdot1 qdot2 =
  P.R.solve 7
    (λ l e1 e2 a b da db →
      (((da P.R.⊕ db)
          P.R.⊗ ((l P.R.⊗ e1) P.R.⊕ (l P.R.⊗ e2)))
        P.R.⊕ P.R.⊝
          ((a P.R.⊕ b)
            P.R.⊗
              ((P.R.K (two F))
                P.R.⊗ ((l P.R.⊗ a) P.R.⊕ (l P.R.⊗ b)))))
      P.R.⊜
      (l P.R.⊗
        (((e1 P.R.⊕ e2) P.R.⊗ (da P.R.⊕ db))
          P.R.⊕ P.R.⊝
            ((P.R.K (two F))
              P.R.⊗ ((a P.R.⊕ b) P.R.⊗ (a P.R.⊕ b))))))
    refl lambda E1 E2 q1 q2 qdot1 qdot2
  where module P = Field.Polynomial F

round101DistinctEigenpacketRecombinationHasCrossRadiusDefect : Bool
round101DistinctEigenpacketRecombinationHasCrossRadiusDefect = true

round101DyadicRecombinationIsPureParseval : Bool
round101DyadicRecombinationIsPureParseval = false

round101SameEigenvalueRecombinationClosesExactly : Bool
round101SameEigenvalueRecombinationClosesExactly = true

round101DyadicRecombinationIsPureParsevalIsFalse :
  round101DyadicRecombinationIsPureParseval ≡ false
round101DyadicRecombinationIsPureParsevalIsFalse = refl
