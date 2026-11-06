{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalForwardCyclicCrossGramExact where

------------------------------------------------------------------------
-- HIL01 / HIL02 / HIL07: ORIGINAL TSVF cyclic CROSS-GRAM producer.
--
-- This is the SAME original forward ket of the source TSVF ensemble,
-- not an arbitrary "observer inner product" record and not the
-- backward-conditioned ABL functional.
--
-- The existing TSVFOriginalForwardPositiveFunctionalExact supplies
-- the selected source Hilbert/adjoint laws and originalForwardFunctional.
-- We derive the *complete cyclic pair form* for all operators A,B:
--
--   omega_E (A^dagger B) = < A psi_E , B psi_E >.
--
-- From the source's actual operator action, we also derive equality
-- of all cyclic pairings when two operators have the same selected
-- image ket, and null-equivalence under that same-action relation.
--
-- No second Gram kernel, no chosen free oscillator, no all-word OS
-- state equality premise, no assumed positive-complex Hilbert or
-- dense completion. The source's Hilbert laws remain actual
-- physical producer inputs; a positive Weight is not a C*-state.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (cong; sym; trans)
import DASHI.Quantum.TSVF as TSVF
import DASHI.Physics.Foundations.TSVFOriginalForwardPositiveFunctionalExact
  as Forward

module _
  {Q : TSVF.QuantumSurface}
  (E : TSVF.TSVFEnsemble Q)
  (laws : Forward.OriginalPhysicalInnerProductLaws E)
  where

  open TSVF.QuantumSurface Q
  open Forward.OriginalPhysicalInnerProductLaws laws

  originalForwardKet : Ket
  originalForwardKet = TSVF.forwardState E

  originalCyclicVector : Operator → Ket
  originalCyclicVector op = apply op originalForwardKet

  originalForwardState : Operator → Scalar
  originalForwardState = Forward.originalForwardFunctional E laws

  -- Original preselected one-boundary operator functional.
  originalObserverCrossGram : Operator → Operator → Scalar
  originalObserverCrossGram a b =
    originalForwardState (operatorCompose (operatorAdjoint a) b)

  originalSelectedCyclicPair : Operator → Operator → Scalar
  originalSelectedCyclicPair a b =
    pair (braOfKet (originalCyclicVector a))
      (originalCyclicVector b)

  -- This is the all-operator off-diagonal cyclic Gram identity,
  -- not just the A=B positivity statement from the earlier module.
  originalCyclicCrossGramIsActualOperatorPair :
    ∀ a b →
    originalObserverCrossGram a b
      ≡ originalSelectedCyclicPair a b
  originalCyclicCrossGramIsActualOperatorPair a b =
    trans
      (cong (pair (braOfKet originalForwardKet))
        (selectedComposition (operatorAdjoint a) b originalForwardKet))
      (adjointLaw a originalForwardKet (originalCyclicVector b))

  -- The equivalence relation is genuinely produced by the original
  -- selected operator representation, not postulated by a Gram field.
  OriginalSelectedSameCyclicKet : Operator → Operator → Set
  OriginalSelectedSameCyclicKet a b =
    originalCyclicVector a ≡ originalCyclicVector b

  originalCyclicKetReflexive :
    ∀ a → OriginalSelectedSameCyclicKet a a
  originalCyclicKetReflexive a = refl

  originalCyclicKetSymmetric :
    ∀ a b → OriginalSelectedSameCyclicKet a b →
      OriginalSelectedSameCyclicKet b a
  originalCyclicKetSymmetric a b = sym

  originalCyclicKetTransitive :
    ∀ a b c →
    OriginalSelectedSameCyclicKet a b →
    OriginalSelectedSameCyclicKet b c →
    OriginalSelectedSameCyclicKet a c
  originalCyclicKetTransitive a b c = trans

  originalCyclicKetSameImpliesAllRightGrams :
    ∀ a b →
    OriginalSelectedSameCyclicKet a b →
    ∀ test →
    originalObserverCrossGram test a
      ≡ originalObserverCrossGram test b
  originalCyclicKetSameImpliesAllRightGrams a b same test =
    trans
      (originalCyclicCrossGramIsActualOperatorPair test a)
      (trans
        (cong (pair (braOfKet (originalCyclicVector test))) same)
        (sym (originalCyclicCrossGramIsActualOperatorPair test b)))

  originalCyclicKetSameImpliesAllLeftGrams :
    ∀ a b →
    OriginalSelectedSameCyclicKet a b →
    ∀ test →
    originalObserverCrossGram a test
      ≡ originalObserverCrossGram b test
  originalCyclicKetSameImpliesAllLeftGrams a b same test =
    trans
      (originalCyclicCrossGramIsActualOperatorPair a test)
      (trans
        (cong
          (λ ket → pair (braOfKet ket) (originalCyclicVector test))
          same)
        (sym (originalCyclicCrossGramIsActualOperatorPair b test)))

  -- The actual source operator identity supplies the source cyclic
  -- vector. No separate "cyclic vacuum" witness is chosen.
  originalIdentityProducesSelectedForwardKet :
    originalCyclicVector operatorIdentity ≡ originalForwardKet
  originalIdentityProducesSelectedForwardKet =
    identityActs originalForwardKet

  -- Source-native operator-composition action on the selected cyclic
  -- carrier. This is the algebraic precursor to the eventual
  -- GNS representation on its null quotient.
  originalCyclicRepresentationAction :
    ∀ a b →
    originalCyclicVector (operatorCompose a b)
      ≡ apply a (originalCyclicVector b)
  originalCyclicRepresentationAction a b =
    selectedComposition a b originalForwardKet

  -- The positive norm is exactly the same previously selected
  -- forward-state Weight, not postselected ABL normalization.
  originalAllCyclicDiagonalsWeightPositive :
    ∀ a →
    Positive (normSquared (originalObserverCrossGram a a))
  originalAllCyclicDiagonalsWeightPositive a =
    Forward.originalPositiveQuadraticHasPositiveWeight E laws a

-- Full HIL02 needs a faithful scalar positivity order, star-algebra,
-- null-ideal proof, nonzero completed complex Hilbert, and a dense
-- domain. HIL07 additionally needs physical original observer/OS
-- source equality rather than only internal TSVF cyclic Gram.
