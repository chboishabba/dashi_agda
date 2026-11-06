{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalForwardCyclicActionQuotientExact where

------------------------------------------------------------------------
-- HIL01/HIL02: CONCRETE ORIGINAL GNS ACTION KERNEL CONGRUENCE.
--
-- Start with exactly the original TSVF.forwardState E, and declare
-- A ~_E B when their actual selected cyclic kets A psi_E, B psi_E
-- coincide. The previous source theorem constructs this relation,
-- proves it an equivalence and maps it into ALL cyclic cross Grams.
--
-- This module proves the original operator action, sums and scalar
-- action RESPECT this quotient relation, so a representation
-- descends to the algebraic image of the original cyclic ket.
-- The cyclic vector is the original forward ket.
--
-- Does NOT equate equality of vectors with zero norm in a complete
-- complex Hilbert; that demands positive definiteness, genuine
-- scalar laws and actual Hilbert completion from the source.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)
import DASHI.Quantum.TSVF as TSVF
import DASHI.Physics.Foundations.TSVFOriginalForwardPositiveFunctionalExact
  as Forward
import DASHI.Physics.Foundations.TSVFOriginalForwardCyclicCrossGramExact
  as Cyclic

module _
  {Q : TSVF.QuantumSurface}
  (E : TSVF.TSVFEnsemble Q)
  (laws : Forward.OriginalPhysicalInnerProductLaws E)
  where

  open TSVF.QuantumSurface Q
  open Forward.OriginalPhysicalInnerProductLaws laws

  psi : Ket
  psi = TSVF.forwardState E

  originalCyclic : Operator → Ket
  originalCyclic =
    Cyclic.originalCyclicVector E laws

  _≈E_ : Operator → Operator → Set
  a ≈E b = originalCyclic a ≡ originalCyclic b

  -- A single fixed left action preserves original selected
  -- equivalence: there is NO independent representation carrier.
  originalLeftActionPreservesCyclicKernel :
    ∀ left a b → a ≈E b →
    (operatorCompose left a) ≈E (operatorCompose left b)
  originalLeftActionPreservesCyclicKernel left a b same =
    trans
      (selectedComposition left a psi)
      (trans
        (cong (apply left) same)
        (sym (selectedComposition left b psi)))

  -- Original SOURCE addition and scalar operators have well-defined
  -- actions on the same quotient of selected observable insertions.
  originalAdditionPreservesCyclicKernel :
    ∀ a b c d → a ≈E b → c ≈E d →
    (operatorAdd a c) ≈E (operatorAdd b d)
  originalAdditionPreservesCyclicKernel a b c d same1 same2 =
    trans
      (addActs a c psi)
      (trans
        (cong₂ ketAdd same1 same2)
        (sym (addActs b d psi)))

  originalScalarActionPreservesCyclicKernel :
    ∀ scalar a b → a ≈E b →
    (operatorScale scalar a) ≈E (operatorScale scalar b)
  originalScalarActionPreservesCyclicKernel scalar a b same =
    trans
      (scaleActs scalar a psi)
      (trans
        (cong (ketScale scalar) same)
        (sym (scaleActs scalar b psi)))

  originalIdentityActsOnCyclicImage :
    ∀ a → originalCyclic (operatorCompose operatorIdentity a)
      ≡ originalCyclic a
  originalIdentityActsOnCyclicImage a =
    trans
      (selectedComposition operatorIdentity a psi)
      (identityActs (originalCyclic a))

  originalCyclicImageClosedUnderLeftAction :
    ∀ left right →
    apply left (originalCyclic right)
      ≡ originalCyclic (operatorCompose left right)
  originalCyclicImageClosedUnderLeftAction left right =
    sym (selectedComposition left right psi)

  -- A right source kernel is *not* automatically a two-sided
  -- ideal: A psi_E = B psi_E does not imply A C psi_E = B C psi_E.
  -- HIL02's actual GNS null-left-ideal and complex Cauchy Hilbert
  -- structure are further physically selected theorems.
