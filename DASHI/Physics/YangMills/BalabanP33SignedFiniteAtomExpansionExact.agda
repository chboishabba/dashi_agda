module DASHI.Physics.YangMills.BalabanP33SignedFiniteAtomExpansionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- The older atom expansion reduced only the upper Hessian estimate and accepted
-- the finite atom sum inequality as a field.  This module proves both signs by
-- induction over the exact atom list:
--
--   -m_a <= r_a <= m_a  for every atom a
--       implies
--   -sum_a m_a <= sum_a r_a <= sum_a m_a.
--
-- Combining this with the configured majorant budget yields the local bound
-- required by coercivity, not merely an upper estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3LiteralPointwiseHessianEstimatesExact as Pointwise
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PrimitiveOperatorNormLocalBoundsExact as Primitive
import DASHI.Physics.YangMills.BalabanP33FiniteSignedRemainderSummationExact as Signed

map : ∀ {A B : Set} → (A → B) → List A → List B
map function [] = []
map function (value ∷ values) = function value ∷ map function values

sumMapped :
  ∀ {Atom : Set} → List Atom → (Atom → ℚ) → ℚ
sumMapped atoms value = Pointwise.sumℚ (map value atoms)

sumMappedTwoSided :
  ∀ {Atom : Set}
    (atoms : List Atom)
    (value majorant : Atom → ℚ) →
  (∀ atom → Primitive.TwoSided (value atom) (majorant atom)) →
  Primitive.TwoSided
    (sumMapped atoms value)
    (sumMapped atoms majorant)
sumMappedTwoSided [] value majorant atomBound = record
  { Primitive.TwoSided.lower = ℚP.≤-refl
  ; Primitive.TwoSided.upper = ℚP.≤-refl
  }
sumMappedTwoSided (atom ∷ atoms) value majorant atomBound =
  Primitive.addTwoSided
    (value atom)
    (sumMapped atoms value)
    (majorant atom)
    (sumMapped atoms majorant)
    (atomBound atom)
    (sumMappedTwoSided atoms value majorant atomBound)

mappedSumEqualsLiteralSum :
  ∀ {Cell : Set} (cells : List Cell) (charge : Cell → ℚ) →
  Pointwise.sumℚ (map charge cells)
  ≡ Sums.sumRational cells charge
mappedSumEqualsLiteralSum [] charge = refl
mappedSumEqualsLiteralSum (cell ∷ cells) charge
  rewrite mappedSumEqualsLiteralSum cells charge = refl

record SignedFixedAtomExpansion
    (Background State Cell Atom : Set)
    (fixedAtoms : List Atom)
    (fixedCoefficient : ℚ) : Set₁ where
  field
    atomValue atomMajorant : Background → State → Cell → Atom → ℚ
    localRemainder localCharge radius : Background → State → Cell → ℚ

    expansionExact : ∀ background state cell →
      localRemainder background state cell
      ≡ sumMapped fixedAtoms (atomValue background state cell)

    atomTwoSided : ∀ background state cell atom →
      Primitive.TwoSided
        (atomValue background state cell atom)
        (atomMajorant background state cell atom)

    majorantSumBelowConfiguredCharge : ∀ background state cell →
      sumMapped fixedAtoms (atomMajorant background state cell)
      ≤ fixedCoefficient * radius background state cell
        * localCharge background state cell

open SignedFixedAtomExpansion public

signedFiniteAtomExpansionBound :
  ∀ {Background State Cell Atom fixedAtoms fixedCoefficient}
    (dataSet : SignedFixedAtomExpansion
      Background State Cell Atom fixedAtoms fixedCoefficient)
    background state cell →
  Primitive.TwoSided
    (localRemainder dataSet background state cell)
    (fixedCoefficient * radius dataSet background state cell
      * localCharge dataSet background state cell)
signedFiniteAtomExpansionBound
    {fixedAtoms = fixedAtoms}
    {fixedCoefficient = fixedCoefficient}
    dataSet background state cell =
  subst
    (λ selected → Primitive.TwoSided selected
      (fixedCoefficient * radius dataSet background state cell
        * localCharge dataSet background state cell))
    (sym (expansionExact dataSet background state cell))
    (Primitive.tightenTwoSided
      (sumMapped fixedAtoms (atomValue dataSet background state cell))
      (sumMapped fixedAtoms (atomMajorant dataSet background state cell))
      (fixedCoefficient * radius dataSet background state cell
        * localCharge dataSet background state cell)
      (majorantSumBelowConfiguredCharge dataSet background state cell)
      (sumMappedTwoSided
        fixedAtoms
        (atomValue dataSet background state cell)
        (atomMajorant dataSet background state cell)
        (atomTwoSided dataSet background state cell)))

record SignedAtomFamilyGlobalization
    (Background State Cell Atom : Set)
    (fixedAtoms : List Atom)
    (fixedCoefficient : ℚ)
    (local : SignedFixedAtomExpansion
      Background State Cell Atom fixedAtoms fixedCoefficient) : Set₁ where
  field
    cells : Background → List Cell
    commonRadius globalNormSq : Background → State → ℚ

    fixedCoefficientNonnegative : NonNegative fixedCoefficient
    commonRadiusNonnegative : ∀ background state →
      0ℚ ≤ commonRadius background state

    radiusExact : ∀ background state cell →
      radius local background state cell ≡ commonRadius background state

    incidenceNormBound : ∀ background state →
      Pointwise.sumℚ
        (map (localCharge local background state) (cells background))
      ≤ globalNormSq background state

open SignedAtomFamilyGlobalization public

asFiniteSignedRemainderFamily :
  ∀ {Background State Cell Atom fixedAtoms fixedCoefficient}
    {local : SignedFixedAtomExpansion
      Background State Cell Atom fixedAtoms fixedCoefficient} →
  SignedAtomFamilyGlobalization
    Background State Cell Atom fixedAtoms fixedCoefficient local →
  Signed.FiniteSignedRemainderFamily Background State Cell
asFiniteSignedRemainderFamily
    {fixedCoefficient = fixedCoefficient}
    {local = local} globalization = record
  { Signed.FiniteSignedRemainderFamily.cells = cells globalization
  ; Signed.FiniteSignedRemainderFamily.localRemainder =
      localRemainder local
  ; Signed.FiniteSignedRemainderFamily.localNormCharge =
      localCharge local
  ; Signed.FiniteSignedRemainderFamily.weight =
      λ background state → fixedCoefficient * commonRadius globalization background state
  ; Signed.FiniteSignedRemainderFamily.globalNormSq =
      globalNormSq globalization
  ; Signed.FiniteSignedRemainderFamily.weightNonnegative =
      λ background state →
        let
          instance
            coefficientNN : NonNegative fixedCoefficient
            coefficientNN = fixedCoefficientNonnegative globalization

            radiusNN : NonNegative (commonRadius globalization background state)
            radiusNN = ℚ.nonNegative
              (commonRadiusNonnegative globalization background state)

            productNN : NonNegative
              (fixedCoefficient * commonRadius globalization background state)
            productNN = ℚP.nonNeg*nonNeg⇒nonNeg
              fixedCoefficient
              (commonRadius globalization background state)
        in
        ℚP.nonNegative⁻¹
          (fixedCoefficient * commonRadius globalization background state)
  ; Signed.FiniteSignedRemainderFamily.pointwiseUpper =
      λ background state cell →
        subst
          (λ selectedRadius →
            localRemainder local background state cell
            ≤ fixedCoefficient * selectedRadius
              * localCharge local background state cell)
          (radiusExact globalization background state cell)
          (Primitive.upper
            (signedFiniteAtomExpansionBound local background state cell))
  ; Signed.FiniteSignedRemainderFamily.pointwiseLower =
      λ background state cell →
        subst
          (λ selectedRadius →
            - (fixedCoefficient * selectedRadius
                * localCharge local background state cell)
            ≤ localRemainder local background state cell)
          (radiusExact globalization background state cell)
          (Primitive.lower
            (signedFiniteAtomExpansionBound local background state cell))
  ; Signed.FiniteSignedRemainderFamily.incidenceNormBound =
      λ background state →
        subst
          (λ lower → lower ≤ globalNormSq globalization background state)
          (mappedSumEqualsLiteralSum
            (cells globalization background)
            (localCharge local background state))
          (incidenceNormBound globalization background state)
  }

signedAtomFiniteInductionLevel : ProofLevel
signedAtomFiniteInductionLevel = machineChecked

signedAtomPointwiseBoundLevel : ProofLevel
signedAtomPointwiseBoundLevel = machineChecked

signedAtomToGlobalFamilyLevel : ProofLevel
signedAtomToGlobalFamilyLevel = machineChecked
