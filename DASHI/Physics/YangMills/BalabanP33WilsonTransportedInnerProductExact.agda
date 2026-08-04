module DASHI.Physics.YangMills.BalabanP33WilsonTransportedInnerProductExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- The scalar part of a pure-imaginary quaternion multiplied by an arbitrary
-- quaternion depends only on the latter's imaginary part:
--
--   -q0(X Q) = <X, Im(Q)>.
--
-- Hence every ordered first/first Wilson atom
--
--   -q0(P X M Y S)
--
-- is, after exact five-factor cyclicity, the concrete bilinear form
--
--   <X, Im(M Y S P)>.
--
-- The familiar transported identity
--
--   -q0(X (u Y u^-1)) = <X, Ad_u Y>
--
-- is recovered as a special case.  This closes the trace-to-factorised-form
-- step for all twelve ordered cross placements without assuming a matrix trace
-- or an abstract atom factorisation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using (-R_)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver; zeroCoefficient)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using
  (Polynomial; con; _:=_; :-_)
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  (q0P)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (Quaternion; quat; quaternion; conjugateQ; _*q_; q0)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; su2Lie; lieQuaternion; su2Adjoint; lieQuaternionAdjoint)
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  (su2Dot)
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using (dotP)
import DASHI.Physics.YangMills.BalabanP33QuaternionScalarCyclicityExact as Cyclic

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient

quaternionImaginaryPart : Quaternion → SU2LieAlgebra
quaternionImaginaryPart (quat scalar x y z) = su2Lie x y z

pureImaginaryArbitraryRightScalarProduct : ∀ X value →
  -R (q0 (lieQuaternion X *q value))
  ≡ su2Dot X (quaternionImaginaryPart value)
pureImaginaryArbitraryRightScalarProduct
    (su2Lie x₁ y₁ z₁) (quat scalar x₂ y₂ z₂) =
  solveComputed 7
    (λ x₁ y₁ z₁ scalar x₂ y₂ z₂ →
      :- (q0P zeroP x₁ y₁ z₁ scalar x₂ y₂ z₂)
      := dotP x₁ y₁ z₁ x₂ y₂ z₂)
    computed x₁ y₁ z₁ scalar x₂ y₂ z₂

pureImaginaryScalarProduct : ∀ X Y →
  -R (q0 (lieQuaternion X *q lieQuaternion Y))
  ≡ su2Dot X Y
pureImaginaryScalarProduct X Y =
  pureImaginaryArbitraryRightScalarProduct X (lieQuaternion Y)

transportedPureImaginaryScalarProduct :
  ∀ X u Y →
  -R (q0 (lieQuaternion X *q lieQuaternion (su2Adjoint u Y)))
  ≡ su2Dot X (su2Adjoint u Y)
transportedPureImaginaryScalarProduct X u Y =
  pureImaginaryScalarProduct X (su2Adjoint u Y)

explicitConjugationScalarProduct :
  ∀ X u Y →
  -R (q0
    (lieQuaternion X *q
      ((quaternion u *q lieQuaternion Y) *q
        conjugateQ (quaternion u))))
  ≡ su2Dot X (su2Adjoint u Y)
explicitConjugationScalarProduct X u Y =
  trans
    (cong
      (λ selected → -R (q0 (lieQuaternion X *q selected)))
      (sym (lieQuaternionAdjoint u Y)))
    (transportedPureImaginaryScalarProduct X u Y)

orderedWilsonCrossAtomOperator :
  Quaternion → Quaternion → Quaternion →
  SU2LieAlgebra → SU2LieAlgebra
orderedWilsonCrossAtomOperator prefix middle suffix Y =
  quaternionImaginaryPart
    (((middle *q lieQuaternion Y) *q suffix) *q prefix)

orderedWilsonCrossAtomFactorisation :
  ∀ prefix X middle Y suffix →
  -R (q0
    ((((prefix *q lieQuaternion X) *q middle)
      *q lieQuaternion Y) *q suffix))
  ≡ su2Dot X
      (orderedWilsonCrossAtomOperator prefix middle suffix Y)
orderedWilsonCrossAtomFactorisation prefix X middle Y suffix =
  trans
    (cong -R_
      (Cyclic.scalarPartFiveFactorCyclic
        prefix (lieQuaternion X) middle (lieQuaternion Y) suffix))
    (pureImaginaryArbitraryRightScalarProduct X
      (((middle *q lieQuaternion Y) *q suffix) *q prefix))

wilsonPureImaginaryTracePairingLevel : ProofLevel
wilsonPureImaginaryTracePairingLevel = machineChecked

wilsonArbitraryRightFactorisationLevel : ProofLevel
wilsonArbitraryRightFactorisationLevel = machineChecked

wilsonTransportedAdjointPairingLevel : ProofLevel
wilsonTransportedAdjointPairingLevel = machineChecked

wilsonExplicitConjugationFactorisationLevel : ProofLevel
wilsonExplicitConjugationFactorisationLevel = machineChecked

wilsonOrderedCrossAtomFactorisationLevel : ProofLevel
wilsonOrderedCrossAtomFactorisationLevel = machineChecked
