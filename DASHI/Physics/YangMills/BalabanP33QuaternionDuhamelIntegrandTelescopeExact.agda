module DASHI.Physics.YangMills.BalabanP33QuaternionDuhamelIntegrandTelescopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Joseph Diestel and John J. Uhl, Jr.,
-- "Vector Measures", Mathematical Surveys 15, American Mathematical Society,
-- 1977. DOI: 10.1090/SURV/015.
--
-- Jan Mikusinski,
-- "The Bochner Integral", Birkhaeuser, 1978.
-- DOI: 10.1007/978-3-0348-5567-9.
--
-- TERMINOLOGY
--
-- The later analytic step is a Bochner-integral Duhamel formula.  It is not
-- the unrelated differential-geometric "Bochner identity" involving a
-- Laplacian and Ricci curvature.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact noncommutative telescope for one ordered-simplex integrand
-- on the repository's literal quaternion carrier:
--
--   E0 H E1 K E2 - H K
--     = (E0-1) H E1 K E2
--       + H (E1-1) K E2
--       + H K (E2-1).
--
-- This is the algebraic identity underneath the norm coefficients
--
--   (1-s), (s-r), r.
--
-- It is certified coordinatewise by the repository's computed polynomial
-- normalizer.  Thus the remaining Bochner-integral producer cannot hide a
-- noncommutative reordering or an omitted exponential factor.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver; zeroCoefficient; oneCoefficient)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using
  (Polynomial; con; _:=_; _:+_; :-_)
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  (q0P; q1P; q2P; q3P)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (Quaternion; quat; oneQ; _+q_; negQ; _*q_; quaternionExt)

------------------------------------------------------------------------
-- Polynomial quaternion syntax used only for the computed certificate.
------------------------------------------------------------------------

record QPolynomial (variables : Nat) : Set where
  constructor qpoly
  field
    p0 p1 p2 p3 : Polynomial variables

open QPolynomial public

zeroPoly onePoly : ∀ {variables} → Polynomial variables
zeroPoly = con zeroCoefficient
onePoly = con oneCoefficient

oneQPolynomial : ∀ {variables} → QPolynomial variables
oneQPolynomial = qpoly onePoly zeroPoly zeroPoly zeroPoly

addQPolynomial : ∀ {variables} →
  QPolynomial variables → QPolynomial variables → QPolynomial variables
addQPolynomial left right = qpoly
  (p0 left :+ p0 right)
  (p1 left :+ p1 right)
  (p2 left :+ p2 right)
  (p3 left :+ p3 right)

negQPolynomial : ∀ {variables} →
  QPolynomial variables → QPolynomial variables
negQPolynomial value = qpoly
  (:- p0 value) (:- p1 value) (:- p2 value) (:- p3 value)

subQPolynomial : ∀ {variables} →
  QPolynomial variables → QPolynomial variables → QPolynomial variables
subQPolynomial left right = addQPolynomial left (negQPolynomial right)

mulQPolynomial : ∀ {variables} →
  QPolynomial variables → QPolynomial variables → QPolynomial variables
mulQPolynomial left right = qpoly
  (q0P
    (p0 left) (p1 left) (p2 left) (p3 left)
    (p0 right) (p1 right) (p2 right) (p3 right))
  (q1P
    (p0 left) (p1 left) (p2 left) (p3 left)
    (p0 right) (p1 right) (p2 right) (p3 right))
  (q2P
    (p0 left) (p1 left) (p2 left) (p3 left)
    (p0 right) (p1 right) (p2 right) (p3 right))
  (q3P
    (p0 left) (p1 left) (p2 left) (p3 left)
    (p0 right) (p1 right) (p2 right) (p3 right))

mul3P : ∀ {variables} →
  QPolynomial variables → QPolynomial variables → QPolynomial variables →
  QPolynomial variables
mul3P a b c = mulQPolynomial (mulQPolynomial a b) c

mul4P : ∀ {variables} →
  QPolynomial variables → QPolynomial variables → QPolynomial variables →
  QPolynomial variables → QPolynomial variables
mul4P a b c d = mulQPolynomial (mul3P a b c) d

mul5P : ∀ {variables} →
  QPolynomial variables → QPolynomial variables → QPolynomial variables →
  QPolynomial variables → QPolynomial variables → QPolynomial variables
mul5P a b c d e = mulQPolynomial (mul4P a b c d) e

orderedIntegrandP : ∀ {variables} →
  QPolynomial variables → QPolynomial variables → QPolynomial variables →
  QPolynomial variables → QPolynomial variables → QPolynomial variables
orderedIntegrandP e0 h e1 k e2 = mul5P e0 h e1 k e2

orderedDefectSumP : ∀ {variables} →
  QPolynomial variables → QPolynomial variables → QPolynomial variables →
  QPolynomial variables → QPolynomial variables → QPolynomial variables
orderedDefectSumP e0 h e1 k e2 =
  addQPolynomial
    (mul5P (subQPolynomial e0 oneQPolynomial) h e1 k e2)
    (addQPolynomial
      (mul4P h (subQPolynomial e1 oneQPolynomial) k e2)
      (mul3P h k (subQPolynomial e2 oneQPolynomial)))

orderedReferenceP : ∀ {variables} →
  QPolynomial variables → QPolynomial variables → QPolynomial variables
orderedReferenceP h k = mulQPolynomial h k

------------------------------------------------------------------------
-- Four coordinate certificates.  Twenty scalar variables represent
-- E0,H,E1,K,E2.
------------------------------------------------------------------------

telescopeCoordinate0 :
  ∀ e00 e01 e02 e03 h0 h1 h2 h3 e10 e11 e12 e13
    k0 k1 k2 k3 e20 e21 e22 e23 →
  let e0 = qpoly e00 e01 e02 e03
      h = qpoly h0 h1 h2 h3
      e1 = qpoly e10 e11 e12 e13
      k = qpoly k0 k1 k2 k3
      e2 = qpoly e20 e21 e22 e23
  in
  p0 (subQPolynomial (orderedIntegrandP e0 h e1 k e2)
        (orderedReferenceP h k))
  ≡ p0 (orderedDefectSumP e0 h e1 k e2)
telescopeCoordinate0 =
  solveComputed 20
    (λ e00 e01 e02 e03 h0 h1 h2 h3 e10 e11 e12 e13
       k0 k1 k2 k3 e20 e21 e22 e23 →
      let e0 = qpoly e00 e01 e02 e03
          h = qpoly h0 h1 h2 h3
          e1 = qpoly e10 e11 e12 e13
          k = qpoly k0 k1 k2 k3
          e2 = qpoly e20 e21 e22 e23
      in
      p0 (subQPolynomial (orderedIntegrandP e0 h e1 k e2)
            (orderedReferenceP h k))
      := p0 (orderedDefectSumP e0 h e1 k e2))
    computed

telescopeCoordinate1 :
  ∀ e00 e01 e02 e03 h0 h1 h2 h3 e10 e11 e12 e13
    k0 k1 k2 k3 e20 e21 e22 e23 →
  let e0 = qpoly e00 e01 e02 e03
      h = qpoly h0 h1 h2 h3
      e1 = qpoly e10 e11 e12 e13
      k = qpoly k0 k1 k2 k3
      e2 = qpoly e20 e21 e22 e23
  in
  p1 (subQPolynomial (orderedIntegrandP e0 h e1 k e2)
        (orderedReferenceP h k))
  ≡ p1 (orderedDefectSumP e0 h e1 k e2)
telescopeCoordinate1 =
  solveComputed 20
    (λ e00 e01 e02 e03 h0 h1 h2 h3 e10 e11 e12 e13
       k0 k1 k2 k3 e20 e21 e22 e23 →
      let e0 = qpoly e00 e01 e02 e03
          h = qpoly h0 h1 h2 h3
          e1 = qpoly e10 e11 e12 e13
          k = qpoly k0 k1 k2 k3
          e2 = qpoly e20 e21 e22 e23
      in
      p1 (subQPolynomial (orderedIntegrandP e0 h e1 k e2)
            (orderedReferenceP h k))
      := p1 (orderedDefectSumP e0 h e1 k e2))
    computed

telescopeCoordinate2 :
  ∀ e00 e01 e02 e03 h0 h1 h2 h3 e10 e11 e12 e13
    k0 k1 k2 k3 e20 e21 e22 e23 →
  let e0 = qpoly e00 e01 e02 e03
      h = qpoly h0 h1 h2 h3
      e1 = qpoly e10 e11 e12 e13
      k = qpoly k0 k1 k2 k3
      e2 = qpoly e20 e21 e22 e23
  in
  p2 (subQPolynomial (orderedIntegrandP e0 h e1 k e2)
        (orderedReferenceP h k))
  ≡ p2 (orderedDefectSumP e0 h e1 k e2)
telescopeCoordinate2 =
  solveComputed 20
    (λ e00 e01 e02 e03 h0 h1 h2 h3 e10 e11 e12 e13
       k0 k1 k2 k3 e20 e21 e22 e23 →
      let e0 = qpoly e00 e01 e02 e03
          h = qpoly h0 h1 h2 h3
          e1 = qpoly e10 e11 e12 e13
          k = qpoly k0 k1 k2 k3
          e2 = qpoly e20 e21 e22 e23
      in
      p2 (subQPolynomial (orderedIntegrandP e0 h e1 k e2)
            (orderedReferenceP h k))
      := p2 (orderedDefectSumP e0 h e1 k e2))
    computed

telescopeCoordinate3 :
  ∀ e00 e01 e02 e03 h0 h1 h2 h3 e10 e11 e12 e13
    k0 k1 k2 k3 e20 e21 e22 e23 →
  let e0 = qpoly e00 e01 e02 e03
      h = qpoly h0 h1 h2 h3
      e1 = qpoly e10 e11 e12 e13
      k = qpoly k0 k1 k2 k3
      e2 = qpoly e20 e21 e22 e23
  in
  p3 (subQPolynomial (orderedIntegrandP e0 h e1 k e2)
        (orderedReferenceP h k))
  ≡ p3 (orderedDefectSumP e0 h e1 k e2)
telescopeCoordinate3 =
  solveComputed 20
    (λ e00 e01 e02 e03 h0 h1 h2 h3 e10 e11 e12 e13
       k0 k1 k2 k3 e20 e21 e22 e23 →
      let e0 = qpoly e00 e01 e02 e03
          h = qpoly h0 h1 h2 h3
          e1 = qpoly e10 e11 e12 e13
          k = qpoly k0 k1 k2 k3
          e2 = qpoly e20 e21 e22 e23
      in
      p3 (subQPolynomial (orderedIntegrandP e0 h e1 k e2)
            (orderedReferenceP h k))
      := p3 (orderedDefectSumP e0 h e1 k e2))
    computed

------------------------------------------------------------------------
-- Literal quaternion formula.
------------------------------------------------------------------------

subQ : Quaternion → Quaternion → Quaternion
subQ left right = left +q negQ right

mul3 : Quaternion → Quaternion → Quaternion → Quaternion
mul3 a b c = (a *q b) *q c

mul4 : Quaternion → Quaternion → Quaternion → Quaternion → Quaternion
mul4 a b c d = mul3 a b c *q d

mul5 : Quaternion → Quaternion → Quaternion → Quaternion → Quaternion → Quaternion
mul5 a b c d e = mul4 a b c d *q e

orderedIntegrand :
  Quaternion → Quaternion → Quaternion → Quaternion → Quaternion → Quaternion
orderedIntegrand e0 h e1 k e2 = mul5 e0 h e1 k e2

orderedDefectSum :
  Quaternion → Quaternion → Quaternion → Quaternion → Quaternion → Quaternion
orderedDefectSum e0 h e1 k e2 =
  (mul5 (subQ e0 oneQ) h e1 k e2)
  +q ((mul4 h (subQ e1 oneQ) k e2)
    +q (mul3 h k (subQ e2 oneQ)))

orderedReference : Quaternion → Quaternion → Quaternion
orderedReference h k = h *q k

orderedDuhamelIntegrandTelescopeExact :
  ∀ e0 h e1 k e2 →
  subQ (orderedIntegrand e0 h e1 k e2) (orderedReference h k)
  ≡ orderedDefectSum e0 h e1 k e2
orderedDuhamelIntegrandTelescopeExact
    (quat e00 e01 e02 e03)
    (quat h0 h1 h2 h3)
    (quat e10 e11 e12 e13)
    (quat k0 k1 k2 k3)
    (quat e20 e21 e22 e23) =
  quaternionExt
    (telescopeCoordinate0
      e00 e01 e02 e03 h0 h1 h2 h3 e10 e11 e12 e13
      k0 k1 k2 k3 e20 e21 e22 e23)
    (telescopeCoordinate1
      e00 e01 e02 e03 h0 h1 h2 h3 e10 e11 e12 e13
      k0 k1 k2 k3 e20 e21 e22 e23)
    (telescopeCoordinate2
      e00 e01 e02 e03 h0 h1 h2 h3 e10 e11 e12 e13
      k0 k1 k2 k3 e20 e21 e22 e23)
    (telescopeCoordinate3
      e00 e01 e02 e03 h0 h1 h2 h3 e10 e11 e12 e13
      k0 k1 k2 k3 e20 e21 e22 e23)

orderedDuhamelQuaternionTelescopeLevel : ProofLevel
orderedDuhamelQuaternionTelescopeLevel = machineChecked

physicalBochnerIntegralDuhamelIdentificationLevel : ProofLevel
physicalBochnerIntegralDuhamelIdentificationLevel = conditional
