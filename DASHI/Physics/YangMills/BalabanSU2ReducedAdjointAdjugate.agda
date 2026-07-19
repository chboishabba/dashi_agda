module DASHI.Physics.YangMills.BalabanSU2ReducedAdjointAdjugate where

------------------------------------------------------------------------
-- Polynomial adjugate in the reduced su(2) adjoint algebra.
--
-- For P = a I + b A + c A^2 and A^3 = k A, define
--
--   adj(P) = p I + q A + r A^2
--
-- with
--
--   p = a^2 + 2ack - b^2k + c^2k^2,
--   q = -ab,
--   r = b^2 - ac - c^2k.
--
-- Then
--
--   P adj(P) = det(P) I.
--
-- The three coefficient identities are exposed as polynomial syntax and
-- discharged by the canonical computed solver.  No composite Y-dependent
-- coefficient is passed to the reflective tactic as a free variable.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver; zeroCoefficient; oneCoefficient )
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  ( solveComputed; computed )
open RealPolynomialSolver using
  ( Polynomial; con; _:=_; _:+_; _:*_; :-_ )
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_
  ; _*R_
  ; -R_
  ; zeroR
  ; oneR
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; lieScale
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  ( adCubicCoefficient )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( ReducedAdjointOperator
  ; reducedAd
  ; reducedAdjointExt
  ; applyReducedAdjoint
  ; composeReducedAdjoint
  ; applyReducedComposition
  ; composeAP; composeBP; composeCP
  ; apply1P; apply2P; apply3P
  )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointDeterminantProduct using
  ( reducedAdjointDeterminantValue
  ; reducedAdjointDeterminantValueP
  )

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient

oneP : ∀ {n} → Polynomial n
oneP = con oneCoefficient

twoP : ∀ {n} → Polynomial n
twoP = oneP :+ oneP

twoR : ℝ
twoR = oneR +R oneR

scaleIdentityReduced : ℝ → ReducedAdjointOperator
scaleIdentityReduced scalar = reducedAd scalar zeroR zeroR

adjugateAP :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
adjugateAP k a b c =
  ((((a :* a) :+ (twoP :* ((a :* c) :* k)))
    :+ (:- ((b :* b) :* k)))
    :+ ((c :* c) :* (k :* k)))

adjugateBP :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n
adjugateBP a b c = :- (a :* b)

adjugateCP :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
adjugateCP k a b c =
  ((b :* b) :+ (:- (a :* c))) :+ (:- ((c :* c) :* k))

reducedAdjointAdjugate :
  SU2LieAlgebra →
  ReducedAdjointOperator →
  ReducedAdjointOperator
reducedAdjointAdjugate Y (reducedAd a b c) =
  reducedAd
    ((((a *R a) +R (twoR *R ((a *R c) *R k)))
      +R (-R ((b *R b) *R k)))
      +R ((c *R c) *R (k *R k)))
    (-R (a *R b))
    (((b *R b) +R (-R (a *R c)))
      +R (-R ((c *R c) *R k)))
  where
    k : ℝ
    k = adCubicCoefficient Y

reducedAdjointAdjugateProduct :
  ∀ Y operator →
  composeReducedAdjoint Y operator
    (reducedAdjointAdjugate Y operator)
  ≡
  scaleIdentityReduced
    (reducedAdjointDeterminantValue Y operator)
reducedAdjointAdjugateProduct Y (reducedAd a b c) =
  reducedAdjointExt
    (solveComputed 4
      (λ a b c k →
        composeAP a (adjugateAP k a b c)
          := reducedAdjointDeterminantValueP k a b c)
      computed a b c (adCubicCoefficient Y))
    (solveComputed 4
      (λ a b c k →
        composeBP k a b c
          (adjugateAP k a b c)
          (adjugateBP a b c)
          (adjugateCP k a b c)
          := zeroP)
      computed a b c (adCubicCoefficient Y))
    (solveComputed 4
      (λ a b c k →
        composeCP k a b c
          (adjugateAP k a b c)
          (adjugateBP a b c)
          (adjugateCP k a b c)
          := zeroP)
      computed a b c (adCubicCoefficient Y))

reducedAdjointAdjugateProductRight :
  ∀ Y operator →
  composeReducedAdjoint Y
    (reducedAdjointAdjugate Y operator)
    operator
  ≡
  scaleIdentityReduced
    (reducedAdjointDeterminantValue Y operator)
reducedAdjointAdjugateProductRight Y (reducedAd a b c) =
  reducedAdjointExt
    (solveComputed 4
      (λ a b c k →
        composeAP (adjugateAP k a b c) a
          := reducedAdjointDeterminantValueP k a b c)
      computed a b c (adCubicCoefficient Y))
    (solveComputed 4
      (λ a b c k →
        composeBP k
          (adjugateAP k a b c)
          (adjugateBP a b c)
          (adjugateCP k a b c)
          a b c
          := zeroP)
      computed a b c (adCubicCoefficient Y))
    (solveComputed 4
      (λ a b c k →
        composeCP k
          (adjugateAP k a b c)
          (adjugateBP a b c)
          (adjugateCP k a b c)
          a b c
          := zeroP)
      computed a b c (adCubicCoefficient Y))

applyScaleIdentityReduced :
  ∀ Y scalar X →
  applyReducedAdjoint Y (scaleIdentityReduced scalar) X
    ≡ lieScale scalar X
applyScaleIdentityReduced
  (su2Lie y₁ y₂ y₃) scalar (su2Lie x₁ x₂ x₃) =
  su2LieExt
    (solveComputed 7
      (λ y₁ y₂ y₃ scalar x₁ x₂ x₃ →
        apply1P y₁ y₂ y₃ scalar zeroP zeroP x₁ x₂ x₃
          := scalar :* x₁)
      computed y₁ y₂ y₃ scalar x₁ x₂ x₃)
    (solveComputed 7
      (λ y₁ y₂ y₃ scalar x₁ x₂ x₃ →
        apply2P y₁ y₂ y₃ scalar zeroP zeroP x₁ x₂ x₃
          := scalar :* x₂)
      computed y₁ y₂ y₃ scalar x₁ x₂ x₃)
    (solveComputed 7
      (λ y₁ y₂ y₃ scalar x₁ x₂ x₃ →
        apply3P y₁ y₂ y₃ scalar zeroP zeroP x₁ x₂ x₃
          := scalar :* x₃)
      computed y₁ y₂ y₃ scalar x₁ x₂ x₃)

applyReducedAdjugateProduct :
  ∀ Y operator X →
  applyReducedAdjoint Y operator
    (applyReducedAdjoint Y
      (reducedAdjointAdjugate Y operator) X)
  ≡
  lieScale
    (reducedAdjointDeterminantValue Y operator)
    X
applyReducedAdjugateProduct Y operator X =
  trans
    (applyReducedComposition Y operator
      (reducedAdjointAdjugate Y operator) X)
    (trans
      (cong
        (λ composed → applyReducedAdjoint Y composed X)
        (reducedAdjointAdjugateProduct Y operator))
      (applyScaleIdentityReduced Y
        (reducedAdjointDeterminantValue Y operator) X))
