module DASHI.Mathematics.Topology.QuaternionHopfUnitOrbitExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Heinz Hopf,
-- "Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche".
-- DOI: 10.1007/BF01457962.
--
-- John C. Baez,
-- "The Octonions".
-- DOI: 10.1090/S0273-0979-01-00934-X.
--
-- DASHI CONTRIBUTION
--
-- Close the finite algebraic orbit theorem behind the quaternionic Hopf map.
-- Simultaneous right multiplication sends
--
--   (a,b) |-> (a u,b u).
--
-- The quaternionic and scalar Hopf coordinates scale by N(u).  Therefore they
-- are exactly invariant when N(u)=1.  Unit quaternions are packaged as a
-- proof-bearing carrier, closed under multiplication by the previously proved
-- norm-composition theorem, and their right action is instantiated in the
-- generic Klein action interface.
--
-- This proves invariance on every witnessed unit-quaternion orbit.  It does
-- not prove that every geometric fibre is exactly one such orbit, construct
-- smooth local trivializations, or establish a principal-bundle theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Mathematics.Topology.QuaternionHopfRadiusExact as H
import DASHI.Mathematics.Symmetry.KleinGroupActionInvariantExact as K

open K.GroupAction

record QuaternionPair : Set where
  constructor quaternionPair
  field
    pairFirst pairSecond : Q.RationalQuaternion

open QuaternionPair public

quaternionPairExt : ∀ {left right} →
  pairFirst left ≡ pairFirst right →
  pairSecond left ≡ pairSecond right →
  left ≡ right
quaternionPairExt {quaternionPair _ _} {quaternionPair _ _}
  refl refl = refl

rightMultiplyPair :
  QuaternionPair → Q.RationalQuaternion → QuaternionPair
rightMultiplyPair (quaternionPair a b) u =
  quaternionPair (Q._*q_ a u) (Q._*q_ b u)

pairHopfQuaternion : QuaternionPair → Q.RationalQuaternion
pairHopfQuaternion (quaternionPair a b) = H.hopfQuaternion a b

pairHopfScalar : QuaternionPair → ℚ
pairHopfScalar (quaternionPair a b) = H.hopfScalar a b

scaleQuaternionOne : ∀ value →
  H.scaleQuaternion 1ℚ value ≡ value
scaleQuaternionOne (Q.quat a0 a1 a2 a3) =
  Q.quaternionExt
    (ℚRing.solve-∀ a0) (ℚRing.solve-∀ a1)
    (ℚRing.solve-∀ a2) (ℚRing.solve-∀ a3)

oneMultiplyRational : ∀ value → 1ℚ * value ≡ value
oneMultiplyRational value = ℚRing.solve-∀ value

hopfQuaternionRightScales : ∀ pair u →
  pairHopfQuaternion (rightMultiplyPair pair u)
  ≡ H.scaleQuaternion (CD.quaternionNormSq u)
      (pairHopfQuaternion pair)
hopfQuaternionRightScales
    (quaternionPair
      (Q.quat a0 a1 a2 a3)
      (Q.quat b0 b1 b2 b3))
    (Q.quat u0 u1 u2 u3) =
  Q.quaternionExt
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3 u0 u1 u2 u3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3 u0 u1 u2 u3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3 u0 u1 u2 u3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3 u0 u1 u2 u3)

hopfScalarRightScales : ∀ pair u →
  pairHopfScalar (rightMultiplyPair pair u)
  ≡ CD.quaternionNormSq u * pairHopfScalar pair
hopfScalarRightScales
    (quaternionPair
      (Q.quat a0 a1 a2 a3)
      (Q.quat b0 b1 b2 b3))
    (Q.quat u0 u1 u2 u3) =
  ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3 u0 u1 u2 u3

hopfQuaternionRightUnitInvariant : ∀ pair u →
  CD.quaternionNormSq u ≡ 1ℚ →
  pairHopfQuaternion (rightMultiplyPair pair u)
  ≡ pairHopfQuaternion pair
hopfQuaternionRightUnitInvariant pair u unitNormProof =
  trans
    (hopfQuaternionRightScales pair u)
    (trans
      (cong
        (λ scalar → H.scaleQuaternion scalar (pairHopfQuaternion pair))
        unitNormProof)
      (scaleQuaternionOne (pairHopfQuaternion pair)))

hopfScalarRightUnitInvariant : ∀ pair u →
  CD.quaternionNormSq u ≡ 1ℚ →
  pairHopfScalar (rightMultiplyPair pair u)
  ≡ pairHopfScalar pair
hopfScalarRightUnitInvariant pair u unitNormProof =
  trans
    (hopfScalarRightScales pair u)
    (trans
      (cong (λ scalar → scalar * pairHopfScalar pair) unitNormProof)
      (oneMultiplyRational (pairHopfScalar pair)))

------------------------------------------------------------------------
-- Proof-bearing unit-quaternion action.
------------------------------------------------------------------------

record UnitQuaternion : Set where
  constructor unitQuaternion
  field
    quaternionValue : Q.RationalQuaternion
    unitNorm : CD.quaternionNormSq quaternionValue ≡ 1ℚ

open UnitQuaternion public

unitQuaternionIdentity : UnitQuaternion
unitQuaternionIdentity =
  unitQuaternion Q.oneQ (ℚRing.solve-∀)

unitQuaternionCompose : UnitQuaternion → UnitQuaternion → UnitQuaternion
unitQuaternionCompose
    (unitQuaternion left leftUnit)
    (unitQuaternion right rightUnit) =
  unitQuaternion
    (Q._*q_ left right)
    (CD.quaternionUnitNormProduct left right leftUnit rightUnit)

rightIdentityPair : ∀ pair →
  rightMultiplyPair pair Q.oneQ ≡ pair
rightIdentityPair
    (quaternionPair
      (Q.quat a0 a1 a2 a3)
      (Q.quat b0 b1 b2 b3)) =
  quaternionPairExt
    (Q.quaternionExt
      (ℚRing.solve-∀ a0 a1 a2 a3)
      (ℚRing.solve-∀ a0 a1 a2 a3)
      (ℚRing.solve-∀ a0 a1 a2 a3)
      (ℚRing.solve-∀ a0 a1 a2 a3))
    (Q.quaternionExt
      (ℚRing.solve-∀ b0 b1 b2 b3)
      (ℚRing.solve-∀ b0 b1 b2 b3)
      (ℚRing.solve-∀ b0 b1 b2 b3)
      (ℚRing.solve-∀ b0 b1 b2 b3))

rightActionComposition : ∀ first second pair →
  rightMultiplyPair pair
    (Q._*q_ (quaternionValue first) (quaternionValue second))
  ≡ rightMultiplyPair
      (rightMultiplyPair pair (quaternionValue first))
      (quaternionValue second)
rightActionComposition first second (quaternionPair a b) =
  quaternionPairExt
    (sym (Q.quaternionMultiplyAssociative
      a (quaternionValue first) (quaternionValue second)))
    (sym (Q.quaternionMultiplyAssociative
      b (quaternionValue first) (quaternionValue second)))

unitQuaternionRightAction : K.GroupAction
unitQuaternionRightAction = record
  { G = UnitQuaternion
  ; X = QuaternionPair
  ; identity = unitQuaternionIdentity
  ; compose = λ first second → unitQuaternionCompose second first
  ; act = λ unit pair →
      rightMultiplyPair pair (quaternionValue unit)
  ; identityActs = rightIdentityPair
  ; composeActs = λ first second pair →
      rightActionComposition second first pair
  }

hopfScalarKleinInvariant :
  K.Invariant unitQuaternionRightAction pairHopfScalar
hopfScalarKleinInvariant unit pair =
  hopfScalarRightUnitInvariant
    pair (quaternionValue unit) (unitNorm unit)

hopfQ0KleinInvariant :
  K.Invariant unitQuaternionRightAction
    (λ pair → Q.q0 (pairHopfQuaternion pair))
hopfQ0KleinInvariant unit pair =
  cong Q.q0
    (hopfQuaternionRightUnitInvariant
      pair (quaternionValue unit) (unitNorm unit))

hopfQ1KleinInvariant :
  K.Invariant unitQuaternionRightAction
    (λ pair → Q.q1 (pairHopfQuaternion pair))
hopfQ1KleinInvariant unit pair =
  cong Q.q1
    (hopfQuaternionRightUnitInvariant
      pair (quaternionValue unit) (unitNorm unit))

hopfQ2KleinInvariant :
  K.Invariant unitQuaternionRightAction
    (λ pair → Q.q2 (pairHopfQuaternion pair))
hopfQ2KleinInvariant unit pair =
  cong Q.q2
    (hopfQuaternionRightUnitInvariant
      pair (quaternionValue unit) (unitNorm unit))

hopfQ3KleinInvariant :
  K.Invariant unitQuaternionRightAction
    (λ pair → Q.q3 (pairHopfQuaternion pair))
hopfQ3KleinInvariant unit pair =
  cong Q.q3
    (hopfQuaternionRightUnitInvariant
      pair (quaternionValue unit) (unitNorm unit))
