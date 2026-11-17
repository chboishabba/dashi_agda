module DASHI.Physics.YangMills.BalabanFiniteRationalCauchyExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; squareNonnegative; baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (natAsRational; sumRational)

sumSquares : List ℚ → ℚ
sumSquares values = sumRational values sq

pairDifferenceFrom : ℚ → List ℚ → ℚ
pairDifferenceFrom value values =
  sumRational values (λ other → sq (value - other))

pairDifferenceEnergy : List ℚ → ℚ
pairDifferenceEnergy [] = 0ℚ
pairDifferenceEnergy (value ∷ values) =
  pairDifferenceFrom value values + pairDifferenceEnergy values

sumDifferenceSquaresFormula : ∀ value values →
  pairDifferenceFrom value values
  ≡ natAsRational (length values) * sq value
    - (1ℚ + 1ℚ) * value * sumRational values (λ item → item)
    + sumSquares values
sumDifferenceSquaresFormula value [] = ℚRing.solve-∀
sumDifferenceSquaresFormula value (other ∷ values)
  rewrite sumDifferenceSquaresFormula value values =
  ℚRing.solve-∀

pairDifferenceIdentity : ∀ values →
  natAsRational (length values) * sumSquares values
    - sq (sumRational values (λ item → item))
  ≡ pairDifferenceEnergy values
pairDifferenceIdentity [] = ℚRing.solve-∀
pairDifferenceIdentity (value ∷ values)
  rewrite sumDifferenceSquaresFormula value values
        | pairDifferenceIdentity values =
  ℚRing.solve-∀

sumNonnegative : ∀ values term →
  (∀ value → 0ℚ ≤ term value) →
  0ℚ ≤ sumRational values term
sumNonnegative [] term pointwise = ℚP.≤-refl
sumNonnegative (value ∷ values) term pointwise =
  subst
    (λ left → left ≤ term value + sumRational values term)
    (ℚP.+-identityˡ 0ℚ)
    (ℚP.+-mono-≤
      (pointwise value)
      (sumNonnegative values term pointwise))

pairDifferenceFromNonnegative : ∀ value values →
  0ℚ ≤ pairDifferenceFrom value values
pairDifferenceFromNonnegative value values =
  sumNonnegative values (λ other → sq (value - other))
    (λ other → squareNonnegative (value - other))

pairDifferenceEnergyNonnegative : ∀ values →
  0ℚ ≤ pairDifferenceEnergy values
pairDifferenceEnergyNonnegative [] = ℚP.≤-refl
pairDifferenceEnergyNonnegative (value ∷ values) =
  subst
    (λ left → left ≤
      pairDifferenceFrom value values + pairDifferenceEnergy values)
    (ℚP.+-identityˡ 0ℚ)
    (ℚP.+-mono-≤
      (pairDifferenceFromNonnegative value values)
      (pairDifferenceEnergyNonnegative values))

finiteCauchyRemainderExact : ∀ values →
  sq (sumRational values (λ item → item))
    + pairDifferenceEnergy values
  ≡ natAsRational (length values) * sumSquares values
finiteCauchyRemainderExact values =
  trans
    (cong
      (λ remainder →
        sq (sumRational values (λ item → item)) + remainder)
      (sym (pairDifferenceIdentity values)))
    (ℚRing.solve-∀)

finiteRationalCauchy : ∀ values →
  sq (sumRational values (λ item → item))
  ≤ natAsRational (length values) * sumSquares values
finiteRationalCauchy values =
  subst
    (λ right →
      sq (sumRational values (λ item → item)) ≤ right)
    (finiteCauchyRemainderExact values)
    (baseBelowBasePlusRemainder
      (sq (sumRational values (λ item → item)))
      (pairDifferenceEnergy values)
      (pairDifferenceEnergyNonnegative values))

finiteRationalCauchyLevel : ProofLevel
finiteRationalCauchyLevel = machineChecked
