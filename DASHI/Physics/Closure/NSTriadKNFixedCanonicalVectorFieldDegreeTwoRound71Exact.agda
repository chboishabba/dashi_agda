module DASHI.Physics.Closure.NSTriadKNFixedCanonicalVectorFieldDegreeTwoRound71Exact where

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
-- ROUND 71 / EXACT DEGREE-TWO SHAPE OF THE FIXED VECTOR FIELD
--
-- The fixed-canonical Round71 field is already defined on arbitrary finite
-- reality states.  This module records its exact algebraic degree before adding
-- any analytic norm authority.
--
-- We use a tiny expression language whose evaluator is tied directly to the
-- same literal fixed system:
--
--   velocity(k)                         degree 1
--   projected ordered triad tau         degree 2
--   scalar multiple                     preserves degree
--   finite sum / addition               max degree
--
-- The mode-k RHS expression is exactly the viscous velocity term plus the
-- finite sum of the SAME projected ordered triad terms used by
-- Audit.projectedNonlinearity.  Evaluation is proved equal to the existing
-- rawCanonicalRHSAt.  Every such expression has degree <=2.
--
-- Thus the remaining trajectory-analysis seam is not polynomiality.  It is the
-- standard finite-dimensional real analytic theorem turning this exact
-- degree-two coordinate map into a locally-Lipschitz real vector field and then
-- applying Picard-Lindelof/energy continuation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact as Fixed

maxDegree : Nat → Nat → Nat
maxDegree zero right = right
maxDegree left zero = left
maxDegree (suc left) (suc right) = suc (maxDegree left right)

data CanonicalRHSExpression {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E) : Set r where
  velocityLeaf : Z3.FourierMode → CanonicalRHSExpression geometry
  projectedTriadLeaf :
    Physical.PhysicalTriadIncidence → CanonicalRHSExpression geometry
  scalarScale :
    C3.Complex F → CanonicalRHSExpression geometry →
    CanonicalRHSExpression geometry
  addExpression :
    CanonicalRHSExpression geometry → CanonicalRHSExpression geometry →
    CanonicalRHSExpression geometry
  zeroExpression : CanonicalRHSExpression geometry

expressionDegree :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {geometry : Fixed.FixedCanonicalGeometry F E} →
  CanonicalRHSExpression geometry → Nat
expressionDegree (velocityLeaf mode) = suc zero
expressionDegree (projectedTriadLeaf triad) = suc (suc zero)
expressionDegree (scalarScale scalar expression) = expressionDegree expression
expressionDegree (addExpression left right) =
  maxDegree (expressionDegree left) (expressionDegree right)
expressionDegree zeroExpression = zero

evaluateExpression :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {geometry : Fixed.FixedCanonicalGeometry F E} →
  Fixed.CanonicalRealityState F (Fixed.cutoff geometry) →
  CanonicalRHSExpression geometry → C3.Complex3 F
evaluateExpression {F = F} {geometry = geometry} state
    (velocityLeaf mode) = Fixed.realityVelocity state mode
evaluateExpression {geometry = geometry} state
    (projectedTriadLeaf triad) =
  Audit.projectedOrderedTerm (Fixed.fixedAuditSystem geometry state) triad
evaluateExpression state (scalarScale scalar expression) =
  C3.complex3Scale scalar (evaluateExpression state expression)
evaluateExpression state (addExpression left right) =
  C3.complex3Add
    (evaluateExpression state left)
    (evaluateExpression state right)
evaluateExpression {F = F} state zeroExpression = C3.complex3Zero F

triadExpressionSum :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {geometry : Fixed.FixedCanonicalGeometry F E} →
  List Physical.PhysicalTriadIncidence → CanonicalRHSExpression geometry
triadExpressionSum [] = zeroExpression
triadExpressionSum (triad ∷ rest) =
  addExpression (projectedTriadLeaf triad) (triadExpressionSum rest)

triadExpressionSumEvaluatesExactly :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {geometry : Fixed.FixedCanonicalGeometry F E}
    (state : Fixed.CanonicalRealityState F (Fixed.cutoff geometry))
    (triads : List Physical.PhysicalTriadIncidence) →
  evaluateExpression state (triadExpressionSum triads)
  ≡ Audit.sumVectors
      (Audit.mapTriadTerms (Fixed.fixedAuditSystem geometry state) triads)
triadExpressionSumEvaluatesExactly state [] = refl
triadExpressionSumEvaluatesExactly state (triad ∷ rest) =
  cong
    (C3.complex3Add
      (Audit.projectedOrderedTerm
        (Fixed.fixedAuditSystem _ state) triad))
    (triadExpressionSumEvaluatesExactly state rest)

maxDegreeOneTwoBound : ∀ left right →
  left ≤ suc (suc zero) →
  right ≤ suc (suc zero) →
  maxDegree left right ≤ suc (suc zero)
maxDegreeOneTwoBound zero right leftBound rightBound = rightBound
maxDegreeOneTwoBound left zero leftBound rightBound = leftBound
maxDegreeOneTwoBound (suc left) (suc right)
    (s≤s leftBound) (s≤s rightBound) =
  s≤s (maxDegreeOneTwoBound left right leftBound rightBound)

triadExpressionSumDegreeAtMostTwo :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {geometry : Fixed.FixedCanonicalGeometry F E}
    (triads : List Physical.PhysicalTriadIncidence) →
  expressionDegree (triadExpressionSum {geometry = geometry} triads)
  ≤ suc (suc zero)
triadExpressionSumDegreeAtMostTwo [] = z≤n
triadExpressionSumDegreeAtMostTwo (triad ∷ rest) =
  maxDegreeOneTwoBound
    (suc (suc zero))
    (expressionDegree (triadExpressionSum rest))
    (s≤s (s≤s z≤n))
    (triadExpressionSumDegreeAtMostTwo rest)

modeRHSExpression :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E) →
  Z3.FourierMode → CanonicalRHSExpression geometry
modeRHSExpression geometry mode =
  addExpression
    (scalarScale (Fixed.viscousScalar geometry mode) (velocityLeaf mode))
    (triadExpressionSum
      (Audit.concreteTriadsAt
        (Fixed.fixedAuditSystem geometry
          (Fixed.zeroCanonicalRealityState _ (Fixed.cutoff geometry)))
        mode))

-- concreteTriadsAt depends only on the fixed cutoff, not on velocity.  Hence the
-- triad list in modeRHSExpression is the same list used by every state-specific
-- projectedNonlinearity at this geometry.
concreteTriadsStateIndependent :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E)
    (left right : Fixed.CanonicalRealityState F (Fixed.cutoff geometry))
    mode →
  Audit.concreteTriadsAt (Fixed.fixedAuditSystem geometry left) mode
  ≡ Audit.concreteTriadsAt (Fixed.fixedAuditSystem geometry right) mode
concreteTriadsStateIndependent geometry left right mode = refl

modeRHSExpressionEvaluatesExactly :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E)
    (state : Fixed.CanonicalRealityState F (Fixed.cutoff geometry))
    mode →
  evaluateExpression state (modeRHSExpression geometry mode)
  ≡ Fixed.rawCanonicalRHSAt geometry state mode
modeRHSExpressionEvaluatesExactly geometry state mode =
  let
    zeroState = Fixed.zeroCanonicalRealityState _ (Fixed.cutoff geometry)
    triads = Audit.concreteTriadsAt (Fixed.fixedAuditSystem geometry zeroState) mode
    sameTriads = concreteTriadsStateIndependent geometry zeroState state mode
  in
  trans
    (cong
      (λ nonlinear →
        C3.complex3Add
          (C3.complex3Scale
            (Fixed.viscousScalar geometry mode)
            (Fixed.realityVelocity state mode))
          nonlinear)
      (triadExpressionSumEvaluatesExactly state triads))
    (cong
      (λ selectedTriads →
        C3.complex3Add
          (C3.complex3Scale
            (Fixed.viscousScalar geometry mode)
            (Fixed.realityVelocity state mode))
          (Audit.sumVectors
            (Audit.mapTriadTerms
              (Fixed.fixedAuditSystem geometry state) selectedTriads)))
      sameTriads)

modeRHSExpressionDegreeAtMostTwo :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E)
    mode →
  expressionDegree (modeRHSExpression geometry mode) ≤ suc (suc zero)
modeRHSExpressionDegreeAtMostTwo geometry mode =
  maxDegreeOneTwoBound
    (suc zero)
    (expressionDegree
      (triadExpressionSum
        (Audit.concreteTriadsAt
          (Fixed.fixedAuditSystem geometry
            (Fixed.zeroCanonicalRealityState _ (Fixed.cutoff geometry))) mode)))
    (s≤s z≤n)
    (triadExpressionSumDegreeAtMostTwo
      (Audit.concreteTriadsAt
        (Fixed.fixedAuditSystem geometry
          (Fixed.zeroCanonicalRealityState _ (Fixed.cutoff geometry))) mode))

round71FixedCanonicalVectorFieldDegreeAtMostTwo : Bool
round71FixedCanonicalVectorFieldDegreeAtMostTwo = true

round71DegreeTwoExpressionEvaluatesToLiteralRHS : Bool
round71DegreeTwoExpressionEvaluatesToLiteralRHS = true

round71RealLocalLipschitzAuthorityApplied : Bool
round71RealLocalLipschitzAuthorityApplied = false

round71FixedCanonicalVectorFieldDegreeAtMostTwoIsTrue :
  round71FixedCanonicalVectorFieldDegreeAtMostTwo ≡ true
round71FixedCanonicalVectorFieldDegreeAtMostTwoIsTrue = refl

round71RealLocalLipschitzAuthorityAppliedIsFalse :
  round71RealLocalLipschitzAuthorityApplied ≡ false
round71RealLocalLipschitzAuthorityAppliedIsFalse = refl
