module DASHI.Physics.YangMills.BalabanFiniteSelectorL2DefinitenessExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Prove definiteness of the literal finite squared l2 norm carried by a
-- proof-bearing finite selector.  The theorem is deliberately pointwise: if
-- the finite sum of rational coordinate squares is zero, every represented
-- coordinate is zero.  This is the exact kernel lemma needed to turn a strict
-- quadratic floor on a reduced multiplier presentation into an injectivity
-- statement without function extensionality or a dimension-count argument.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; 1/_; ≢-nonZero)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis

Vector : Set → Set
Vector Index = Index → ℚ

finiteSelectorNormSq :
  ∀ {Index : Set} → Basis.FiniteSelector Index → Vector Index → ℚ
finiteSelectorNormSq selector vector =
  Sums.sumRational (Basis.elements selector)
    (λ index → vector index * vector index)

selectorSquareFactorBelow :
  ∀ {Index : Set}
    (selector : Basis.FiniteSelector Index)
    (vector : Vector Index) target candidate →
  (vector candidate * vector candidate)
    * Basis.kronecker (Basis.decide selector) candidate target
  ≤ vector candidate * vector candidate
selectorSquareFactorBelow selector vector target candidate
  with Basis.decide selector candidate target
... | yes refl =
  subst
    (λ left → left ≤ vector target * vector target)
    (ℚRing.solve-∀ (vector target))
    ℚP.≤-refl
... | no _ =
  subst
    (λ left → left ≤ vector candidate * vector candidate)
    (ℚRing.solve-∀ (vector candidate))
    (FiniteL2.squareNonnegative (vector candidate))

finiteSelectorCoordinateSquareBelowNorm :
  ∀ {Index : Set}
    (selector : Basis.FiniteSelector Index)
    (vector : Vector Index) target →
  vector target * vector target
  ≤ finiteSelectorNormSq selector vector
finiteSelectorCoordinateSquareBelowNorm selector vector target =
  let
    selected = Schur.sumPointwiseBelow
      (Basis.elements selector) _ _
      (selectorSquareFactorBelow selector vector target)

    exact :
      Sums.sumRational (Basis.elements selector)
        (λ candidate →
          (vector candidate * vector candidate)
          * Basis.kronecker (Basis.decide selector) candidate target)
      ≡ vector target * vector target
    exact = Basis.selectorExact selector
      (λ candidate → vector candidate * vector candidate) target
  in
  subst
    (λ lower → lower ≤ finiteSelectorNormSq selector vector)
    exact selected

rationalSquareZeroImpliesZero : ∀ value →
  value * value ≡ 0ℚ → value ≡ 0ℚ
rationalSquareZeroImpliesZero value squareZero
  with value ℚP.≟ 0ℚ
... | yes valueZero = valueZero
... | no valueNonzero =
  let
    instance
      valueNZ = ≢-nonZero valueNonzero

    inverseLeft : (1/ value) * value ≡ 1ℚ
    inverseLeft = ℚP.*-inverseˡ value
  in
  trans
    (sym (ℚP.*-identityˡ value))
    (trans
      (cong (_* value) (sym inverseLeft))
      (trans
        (ℚP.*-assoc (1/ value) value value)
        (trans
          (cong ((1/ value) *_) squareZero)
          (ℚP.*-zeroʳ (1/ value)))))

finiteSelectorNormZeroPointwise :
  ∀ {Index : Set}
    (selector : Basis.FiniteSelector Index)
    (vector : Vector Index) →
  finiteSelectorNormSq selector vector ≡ 0ℚ →
  ∀ target → vector target ≡ 0ℚ
finiteSelectorNormZeroPointwise selector vector normZero target =
  let
    squareBelowNorm = finiteSelectorCoordinateSquareBelowNorm
      selector vector target

    squareBelowZero : vector target * vector target ≤ 0ℚ
    squareBelowZero = subst
      (λ upper → vector target * vector target ≤ upper)
      normZero squareBelowNorm

    squareZero : vector target * vector target ≡ 0ℚ
    squareZero = ℚP.≤-antisym
      squareBelowZero (FiniteL2.squareNonnegative (vector target))
  in
  rationalSquareZeroImpliesZero (vector target) squareZero

finiteSelectorL2CoordinateBoundLevel : ProofLevel
finiteSelectorL2CoordinateBoundLevel = machineChecked

finiteSelectorL2DefinitenessLevel : ProofLevel
finiteSelectorL2DefinitenessLevel = machineChecked
