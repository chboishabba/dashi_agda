module DASHI.Physics.YangMills.BalabanP33AbsoluteFiniteAtomAdapterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the repository's fixed 18/8/4/16/16 atom expansions from one-sided
-- majorization to the signed form required by coercivity.  The only additional
-- local fact is the standard absolute estimate
--
--   |r_a| <= m_a.
--
-- The two inequalities for every atom and both inequalities for the complete
-- finite atom sum are then derived rather than supplied independently.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _*_; ∣_∣; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3LiteralPointwiseHessianEstimatesExact as Pointwise
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredFiniteAtomListsExact as Atoms
import DASHI.Physics.YangMills.BalabanP33SignedFiniteAtomExpansionExact as SignedAtoms
import DASHI.Physics.YangMills.BalabanP33PrimitiveAbsoluteOperatorAdapterExact as Absolute

mapAgreement :
  ∀ {A B : Set} (function : A → B) (values : List A) →
  SignedAtoms.map function values ≡ Atoms.map function values
mapAgreement function [] = refl
mapAgreement function (value ∷ values)
  rewrite mapAgreement function values = refl

sumMappedAgreement :
  ∀ {Atom : Set} (atoms : List Atom) (value : Atom → ℚ) →
  SignedAtoms.sumMapped atoms value
  ≡ Pointwise.sumℚ (Atoms.map value atoms)
sumMappedAgreement atoms value =
  cong Pointwise.sumℚ (mapAgreement value atoms)

fromAbsoluteFixedAtomExpansion :
  ∀ {Background State Cell Atom fixedAtoms fixedCoefficient}
    (dataSet : Atoms.FixedAtomExpansionInput
      Background State Cell Atom fixedAtoms fixedCoefficient) →
  (∀ background state cell atom →
    ∣ Atoms.atomValue dataSet background state cell atom ∣
    ≤ Atoms.atomMajorant dataSet background state cell atom) →
  SignedAtoms.SignedFixedAtomExpansion
    Background State Cell Atom fixedAtoms fixedCoefficient
fromAbsoluteFixedAtomExpansion
    {fixedAtoms = fixedAtoms} dataSet absoluteBound = record
  { SignedAtoms.SignedFixedAtomExpansion.atomValue =
      Atoms.atomValue dataSet
  ; SignedAtoms.SignedFixedAtomExpansion.atomMajorant =
      Atoms.atomMajorant dataSet
  ; SignedAtoms.SignedFixedAtomExpansion.localRemainder =
      Atoms.localRemainder dataSet
  ; SignedAtoms.SignedFixedAtomExpansion.localCharge =
      Atoms.localCharge dataSet
  ; SignedAtoms.SignedFixedAtomExpansion.radius =
      Atoms.radius dataSet
  ; SignedAtoms.SignedFixedAtomExpansion.expansionExact =
      λ background state cell →
        trans
          (Atoms.expansionExact dataSet background state cell)
          (sym
            (sumMappedAgreement fixedAtoms
              (Atoms.atomValue dataSet background state cell)))
  ; SignedAtoms.SignedFixedAtomExpansion.atomTwoSided =
      λ background state cell atom →
        Absolute.operatorNormDominatesCoordinate
          (Atoms.atomValue dataSet background state cell atom)
          (Atoms.atomMajorant dataSet background state cell atom)
          (absoluteBound background state cell atom)
  ; SignedAtoms.SignedFixedAtomExpansion.majorantSumBelowConfiguredCharge =
      λ background state cell →
        subst
          (λ lower → lower
            ≤ fixedCoefficient * Atoms.radius dataSet background state cell
              * Atoms.localCharge dataSet background state cell)
          (sym
            (sumMappedAgreement fixedAtoms
              (Atoms.atomMajorant dataSet background state cell)))
          (Atoms.majorantSumBelowConfiguredCharge
            dataSet background state cell)
  }

absoluteAtomToSignedAtomLevel : ProofLevel
absoluteAtomToSignedAtomLevel = machineChecked

fixedPhysicalAtomSignUpgradeLevel : ProofLevel
fixedPhysicalAtomSignUpgradeLevel = machineChecked
