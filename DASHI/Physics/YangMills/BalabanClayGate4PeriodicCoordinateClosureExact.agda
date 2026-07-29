module DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using
    ( CyclicIndex; zeroᵢ; sucᵢ; pair
    ; Empty; yes; no
    ; cyclicIndexDecidableEquality; sucNotZero
    )

import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Adjacency
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact as Covariance
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette

------------------------------------------------------------------------
-- Repository-specific finite geometry.
--
-- The standard periodic-link and plaquette conventions are documented in:
-- Michael Creutz, "Quarks, Gluons and Lattices", Cambridge University Press,
-- open-access reissue (2022). DOI: 10.1017/9781009290395.
--
-- The proofs below are not imported from the literature: they are literal
-- induction over DASHI's kernel-visible CyclicIndex implementation.
------------------------------------------------------------------------

emptyEliminate : ∀ {A : Set} → Empty → A
emptyEliminate ()

successorLastIsZero : ∀ {n} →
  Adjacency.cyclicSuccessor (Adjacency.lastCyclic {n}) ≡ zeroᵢ
successorLastIsZero {zero} = refl
successorLastIsZero {suc n}
  with cyclicIndexDecidableEquality
    (Adjacency.lastCyclic {n}) (Adjacency.lastCyclic {n})
... | yes equality = refl
... | no notEqual = emptyEliminate (notEqual refl)

predecessorZeroIsLast : ∀ {n} →
  Adjacency.cyclicPredecessor {n} zeroᵢ ≡ Adjacency.lastCyclic
predecessorZeroIsLast {zero} = refl
predecessorZeroIsLast {suc n} = refl

mutual
  successorAfterPredecessor : ∀ {n} (index : CyclicIndex (suc n)) →
    Adjacency.cyclicSuccessor (Adjacency.cyclicPredecessor index) ≡ index
  successorAfterPredecessor {zero} zeroᵢ = refl
  successorAfterPredecessor {suc n} zeroᵢ = successorLastIsZero {suc n}
  successorAfterPredecessor {suc n} (sucᵢ zeroᵢ) = refl
  successorAfterPredecessor {suc n} (sucᵢ (sucᵢ index))
    with cyclicIndexDecidableEquality
      (Adjacency.cyclicPredecessor (sucᵢ index))
      (Adjacency.lastCyclic {n})
  ... | yes predecessorIsLast = emptyEliminate
      (sucNotZero
        (trans
          (sym (successorAfterPredecessor (sucᵢ index)))
          (trans
            (cong Adjacency.cyclicSuccessor predecessorIsLast)
            (successorLastIsZero {n}))))
  ... | no predecessorIsNotLast =
      cong sucᵢ (successorAfterPredecessor (sucᵢ index))

  predecessorAfterSuccessor : ∀ {n} (index : CyclicIndex (suc n)) →
    Adjacency.cyclicPredecessor (Adjacency.cyclicSuccessor index) ≡ index
  predecessorAfterSuccessor {zero} zeroᵢ = refl
  predecessorAfterSuccessor {suc n} zeroᵢ = refl
  predecessorAfterSuccessor {suc n} (sucᵢ index)
    with cyclicIndexDecidableEquality index (Adjacency.lastCyclic {n})
  ... | yes indexIsLast = cong sucᵢ (sym indexIsLast)
  ... | no indexIsNotLast = finish
      (Adjacency.cyclicSuccessor index) refl
    where
    finish : ∀ result →
      Adjacency.cyclicSuccessor index ≡ result →
      Adjacency.cyclicPredecessor (sucᵢ result) ≡ sucᵢ index
    finish zeroᵢ successorIsZero = emptyEliminate
      (indexIsNotLast
        (trans
          (sym (predecessorAfterSuccessor index))
          (trans
            (cong Adjacency.cyclicPredecessor successorIsZero)
            (predecessorZeroIsLast {n}))))
    finish (sucᵢ result) successorIsSuc =
      cong sucᵢ
        (subst
          (λ value → Adjacency.cyclicPredecessor value ≡ index)
          successorIsSuc
          (predecessorAfterSuccessor index))

blockExtensionality :
  ∀ {n}
    {a0 a1 a2 a3 b0 b1 b2 b3 : CyclicIndex (suc n)} →
  a0 ≡ b0 → a1 ≡ b1 → a2 ≡ b2 → a3 ≡ b3 →
  pair (pair a0 a1) (pair a2 a3)
  ≡ pair (pair b0 b1) (pair b2 b3)
blockExtensionality refl refl refl refl = refl

positiveAfterNegativeBlock :
  ∀ {n} (block : Periodic.PeriodicBlock n) axis →
  Bond.positiveStep (Bond.negativeStep block axis) axis ≡ block
positiveAfterNegativeBlock (pair (pair c0 c1) (pair c2 c3)) zeroᵢ =
  blockExtensionality (successorAfterPredecessor c0) refl refl refl
positiveAfterNegativeBlock (pair (pair c0 c1) (pair c2 c3))
  (sucᵢ zeroᵢ) =
  blockExtensionality refl (successorAfterPredecessor c1) refl refl
positiveAfterNegativeBlock (pair (pair c0 c1) (pair c2 c3))
  (sucᵢ (sucᵢ zeroᵢ)) =
  blockExtensionality refl refl (successorAfterPredecessor c2) refl
positiveAfterNegativeBlock (pair (pair c0 c1) (pair c2 c3))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) =
  blockExtensionality refl refl refl (successorAfterPredecessor c3)

negativeAfterPositiveBlock :
  ∀ {n} (block : Periodic.PeriodicBlock n) axis →
  Bond.negativeStep (Bond.positiveStep block axis) axis ≡ block
negativeAfterPositiveBlock (pair (pair c0 c1) (pair c2 c3)) zeroᵢ =
  blockExtensionality (predecessorAfterSuccessor c0) refl refl refl
negativeAfterPositiveBlock (pair (pair c0 c1) (pair c2 c3))
  (sucᵢ zeroᵢ) =
  blockExtensionality refl (predecessorAfterSuccessor c1) refl refl
negativeAfterPositiveBlock (pair (pair c0 c1) (pair c2 c3))
  (sucᵢ (sucᵢ zeroᵢ)) =
  blockExtensionality refl refl (predecessorAfterSuccessor c2) refl
negativeAfterPositiveBlock (pair (pair c0 c1) (pair c2 c3))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) =
  blockExtensionality refl refl refl (predecessorAfterSuccessor c3)

periodicStepInverseLaws : ∀ n → Covariance.PeriodicStepInverseLaws n
periodicStepInverseLaws n = record
  { Covariance.PeriodicStepInverseLaws.positiveAfterNegative =
      positiveAfterNegativeBlock
  ; Covariance.PeriodicStepInverseLaws.negativeAfterPositive =
      negativeAfterPositiveBlock
  }

literalPlaquetteCloses :
  ∀ {n} (block : Periodic.PeriodicBlock n) plane →
  Bond.walk block (Bond.plaquetteBoundaryDirections plane) ≡ block
literalPlaquetteCloses (pair (pair c0 c1) (pair c2 c3)) zeroᵢ =
  blockExtensionality
    (predecessorAfterSuccessor c0)
    (predecessorAfterSuccessor c1) refl refl
literalPlaquetteCloses (pair (pair c0 c1) (pair c2 c3))
  (sucᵢ zeroᵢ) =
  blockExtensionality
    (predecessorAfterSuccessor c0) refl
    (predecessorAfterSuccessor c2) refl
literalPlaquetteCloses (pair (pair c0 c1) (pair c2 c3))
  (sucᵢ (sucᵢ zeroᵢ)) =
  blockExtensionality
    (predecessorAfterSuccessor c0) refl refl
    (predecessorAfterSuccessor c3)
literalPlaquetteCloses (pair (pair c0 c1) (pair c2 c3))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) =
  blockExtensionality refl
    (predecessorAfterSuccessor c1)
    (predecessorAfterSuccessor c2) refl
literalPlaquetteCloses (pair (pair c0 c1) (pair c2 c3))
  (sucᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))) =
  blockExtensionality refl
    (predecessorAfterSuccessor c1) refl
    (predecessorAfterSuccessor c3)
literalPlaquetteCloses (pair (pair c0 c1) (pair c2 c3))
  (sucᵢ (sucᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))))) =
  blockExtensionality refl refl
    (predecessorAfterSuccessor c2)
    (predecessorAfterSuccessor c3)

periodicPlaquetteClosure : ∀ n → Bond.PeriodicPlaquetteClosure n
periodicPlaquetteClosure n = record
  { Bond.PeriodicPlaquetteClosure.plaquetteCloses = literalPlaquetteCloses }

cyclicSuccessorPredecessorInverseLevel : ProofLevel
cyclicSuccessorPredecessorInverseLevel = machineChecked

periodicStepInverseLawsLevel : ProofLevel
periodicStepInverseLawsLevel = machineChecked

literalPeriodicPlaquetteClosureLevel : ProofLevel
literalPeriodicPlaquetteClosureLevel = machineChecked
