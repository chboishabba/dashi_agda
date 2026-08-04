module DASHI.Physics.YangMills.BalabanP33QuaternionScalarCyclicityExact where

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
-- Prove the concrete quaternion form of trace cyclicity used by every Wilson
-- plaquette atom:
--
--   q0(a b)       = q0(b a),
--   q0(a b c)     = q0(b c a),
--   q0(a b c d)   = q0(b c d a).
--
-- The two-factor identity is a checked polynomial equality on all eight real
-- coordinates.  The three- and four-factor rotations follow from the existing
-- quaternion associativity theorem.  For a unit quaternion u, cyclicity and
-- the proved inverse law also give
--
--   q0(u a u^-1) = q0(a).
--
-- Thus Wilson atoms may be cyclically transported and conjugated without a
-- matrix trace axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using (_:=_)
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  (q0P)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( Quaternion; quat; SU2Quaternion; quaternion; conjugateQ
  ; _*q_; q0; oneQ
  ; quaternionMultiplyAssociative; quaternionMultiplyConjugateLeft
  ; scaleOneQ; quaternionOneRight
  ; unitNormSquared; scaleRealQ
  )

scalarPartTwoFactorCyclic : ∀ a b →
  q0 (a *q b) ≡ q0 (b *q a)
scalarPartTwoFactorCyclic
    (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) =
  solveComputed 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      q0P a0 a1 a2 a3 b0 b1 b2 b3
      := q0P b0 b1 b2 b3 a0 a1 a2 a3)
    computed a0 a1 a2 a3 b0 b1 b2 b3

scalarPartThreeFactorCyclic : ∀ a b c →
  q0 ((a *q b) *q c) ≡ q0 ((b *q c) *q a)
scalarPartThreeFactorCyclic a b c =
  trans
    (cong q0 (quaternionMultiplyAssociative a b c))
    (scalarPartTwoFactorCyclic a (b *q c))

scalarPartFourFactorCyclic : ∀ a b c d →
  q0 (((a *q b) *q c) *q d)
  ≡ q0 (((b *q c) *q d) *q a)
scalarPartFourFactorCyclic a b c d =
  trans
    (cong
      (λ selected → q0 (selected *q d))
      (quaternionMultiplyAssociative a b c))
    (trans
      (cong q0 (quaternionMultiplyAssociative a (b *q c) d))
      (scalarPartTwoFactorCyclic a ((b *q c) *q d)))

unitConjugateProductIsOne : ∀ u →
  conjugateQ (quaternion u) *q quaternion u ≡ oneQ
unitConjugateProductIsOne u =
  trans
    (quaternionMultiplyConjugateLeft (quaternion u))
    (trans
      (cong (λ norm → scaleRealQ norm oneQ)
        (unitNormSquared u))
      scaleOneQ)

scalarPartUnitConjugationInvariant : ∀ u value →
  q0 ((quaternion u *q value) *q conjugateQ (quaternion u))
  ≡ q0 value
scalarPartUnitConjugationInvariant u value =
  trans
    (scalarPartThreeFactorCyclic
      (quaternion u) value (conjugateQ (quaternion u)))
    (trans
      (cong q0
        (quaternionMultiplyAssociative
          value (conjugateQ (quaternion u)) (quaternion u)))
      (trans
        (cong (λ selected → q0 (value *q selected))
          (unitConjugateProductIsOne u))
        (cong q0 (quaternionOneRight value))))

scalarPartTwoFactorCyclicityLevel : ProofLevel
scalarPartTwoFactorCyclicityLevel = machineChecked

scalarPartThreeFactorCyclicityLevel : ProofLevel
scalarPartThreeFactorCyclicityLevel = machineChecked

scalarPartFourFactorCyclicityLevel : ProofLevel
scalarPartFourFactorCyclicityLevel = machineChecked

scalarPartUnitConjugationInvarianceLevel : ProofLevel
scalarPartUnitConjugationInvarianceLevel = machineChecked
