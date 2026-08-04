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
-- Identify the scalar part of a product of two pure-imaginary quaternions with
-- the negative Euclidean su(2) inner product:
--
--   -q0(X Y) = <X,Y>.
--
-- Combining this polynomial identity with the repository's literal
-- quaternion-conjugation definition of Ad proves the transported Wilson atom
-- factorisation
--
--   -q0(X (u Y u^-1)) = <X, Ad_u Y>.
--
-- This is the concrete trace/inner-product step needed to turn the ordered
-- first/first quaternion atoms in the nonzero-background Wilson Hessian into
-- factorised adjoint-transport quadratic forms.  No trace pairing or
-- factorisation premise remains at this leaf.
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
  (Polynomial; con; _:=_; _:+_; _:*_; :-_)
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  (q0P)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (quaternion; conjugateQ; _*q_; q0)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (su2Lie; lieQuaternion; su2Adjoint; lieQuaternionAdjoint)
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  (su2Dot)
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using (dotP)

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient

pureImaginaryScalarProduct : ∀ X Y →
  -R (q0 (lieQuaternion X *q lieQuaternion Y))
  ≡ su2Dot X Y
pureImaginaryScalarProduct
    (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  solveComputed 6
    (λ x₁ y₁ z₁ x₂ y₂ z₂ →
      :- (q0P zeroP x₁ y₁ z₁ zeroP x₂ y₂ z₂)
      := dotP x₁ y₁ z₁ x₂ y₂ z₂)
    computed x₁ y₁ z₁ x₂ y₂ z₂

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

wilsonPureImaginaryTracePairingLevel : ProofLevel
wilsonPureImaginaryTracePairingLevel = machineChecked

wilsonTransportedAdjointPairingLevel : ProofLevel
wilsonTransportedAdjointPairingLevel = machineChecked

wilsonExplicitConjugationFactorisationLevel : ProofLevel
wilsonExplicitConjugationFactorisationLevel = machineChecked
