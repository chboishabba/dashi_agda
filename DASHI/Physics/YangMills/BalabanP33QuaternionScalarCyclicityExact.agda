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
-- quaternion associativity theorem.  This allows prefixes and suffixes in the
-- sixteen ordered Wilson atoms to be rotated without introducing a matrix
-- trace axiom.
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
  (Quaternion; quat; _*q_; q0; quaternionMultiplyAssociative)

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

scalarPartTwoFactorCyclicityLevel : ProofLevel
scalarPartTwoFactorCyclicityLevel = machineChecked

scalarPartThreeFactorCyclicityLevel : ProofLevel
scalarPartThreeFactorCyclicityLevel = machineChecked

scalarPartFourFactorCyclicityLevel : ProofLevel
scalarPartFourFactorCyclicityLevel = machineChecked
