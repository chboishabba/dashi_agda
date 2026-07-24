module DASHI.Physics.YangMills.BalabanConfiguredSideLatticeSpacingExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (squareNonnegative)
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact

------------------------------------------------------------------------
-- Exact four-dimensional lattice-spacing normalization.
--
-- With physical bond norm a^4 sum |h|^2 and physical difference energy
-- a^4 sum |delta h / a|^2 = a^2 sum |delta h|^2, the dimensionless block
-- theorem scales by a^2.  Division by a^2 is kept as an explicit inverse law,
-- so no positivity or nonzero side condition is hidden in a notation rewrite.
------------------------------------------------------------------------

spacingSquared : ℚ → ℚ
spacingSquared spacing = spacing * spacing

spacingFourthPower : ℚ → ℚ
spacingFourthPower spacing = spacingSquared spacing * spacingSquared spacing

physicalNormSqAtSpacing :
  ℚ → PhysicalSU2Tangent4 → ℚ
physicalNormSqAtSpacing spacing tangent =
  spacingFourthPower spacing * physicalUnweightedNormSq tangent

physicalDifferenceEnergyAtSpacing :
  ℚ → PhysicalSU2Tangent4 → ℚ
physicalDifferenceEnergyAtSpacing spacing tangent =
  spacingSquared spacing * physicalReferenceDifferenceEnergy tangent

physicalCoerciveTermAtSpacing :
  ℚ → PhysicalSU2Tangent4 → ℚ
physicalCoerciveTermAtSpacing spacing tangent =
  configuredPathCoercivityConstant
  * spacingSquared spacing
  * physicalUnweightedNormSq tangent

spacingSquaredNonnegative : ∀ spacing → 0ℚ ≤ spacingSquared spacing
spacingSquaredNonnegative = squareNonnegative

scaledConfiguredPoincareRaw :
  ∀ spacing tangent →
  PhysicalBlockAverageZero tangent →
  spacingSquared spacing
    * (configuredPathCoercivityConstant * physicalUnweightedNormSq tangent)
  ≤ spacingSquared spacing * physicalReferenceDifferenceEnergy tangent
scaledConfiguredPoincareRaw spacing tangent blockZero =
  let
    instance
      spacingSquaredNonnegativeInstance :
        NonNegative (spacingSquared spacing)
      spacingSquaredNonnegativeInstance =
        nonNegative (spacingSquaredNonnegative spacing)
  in
  ℚP.*-monoˡ-≤-nonNeg
    (spacingSquared spacing)
    (physicalBlockConstrainedDifferencePoincare tangent blockZero)

physicalCoerciveTermScaleExact : ∀ spacing tangent →
  spacingSquared spacing
    * (configuredPathCoercivityConstant * physicalUnweightedNormSq tangent)
  ≡ physicalCoerciveTermAtSpacing spacing tangent
physicalCoerciveTermScaleExact spacing tangent =
  ℚRing.solve-∀
    spacing
    configuredPathCoercivityConstant
    (physicalUnweightedNormSq tangent)

physicalLatticeSpacingCoercivity :
  ∀ spacing tangent →
  PhysicalBlockAverageZero tangent →
  physicalCoerciveTermAtSpacing spacing tangent
  ≤ physicalDifferenceEnergyAtSpacing spacing tangent
physicalLatticeSpacingCoercivity spacing tangent blockZero =
  subst
    (λ left → left ≤ physicalDifferenceEnergyAtSpacing spacing tangent)
    (physicalCoerciveTermScaleExact spacing tangent)
    (scaledConfiguredPoincareRaw spacing tangent blockZero)

------------------------------------------------------------------------
-- Explicit inverse-square presentation of the same theorem.
------------------------------------------------------------------------

record LatticeSpacingInverseData (spacing : ℚ) : Set where
  field
    inverseSpacingSquared : ℚ
    inverseSpacingSquaredLaw :
      inverseSpacingSquared * spacingSquared spacing ≡ 1ℚ

open LatticeSpacingInverseData public

physicalCoercivityCoefficient :
  ∀ {spacing} → LatticeSpacingInverseData spacing → ℚ
physicalCoercivityCoefficient inverseData =
  configuredPathCoercivityConstant * inverseSpacingSquared inverseData

coefficientTimesPhysicalNormExact :
  ∀ {spacing} (inverseData : LatticeSpacingInverseData spacing) tangent →
  physicalCoercivityCoefficient inverseData
    * physicalNormSqAtSpacing spacing tangent
  ≡ physicalCoerciveTermAtSpacing spacing tangent
coefficientTimesPhysicalNormExact {spacing} inverseData tangent =
  trans
    (ℚRing.solve-∀
      configuredPathCoercivityConstant
      (inverseSpacingSquared inverseData)
      (spacingSquared spacing)
      (physicalUnweightedNormSq tangent))
    (trans
      (cong
        (λ inverseProduct →
          configuredPathCoercivityConstant
          * inverseProduct
          * spacingSquared spacing
          * physicalUnweightedNormSq tangent)
        (inverseSpacingSquaredLaw inverseData))
      (ℚRing.solve-∀
        configuredPathCoercivityConstant
        (spacingSquared spacing)
        (physicalUnweightedNormSq tangent)))

physicalInverseSquareLatticeSpacingCoercivity :
  ∀ {spacing} (inverseData : LatticeSpacingInverseData spacing) tangent →
  PhysicalBlockAverageZero tangent →
  physicalCoercivityCoefficient inverseData
    * physicalNormSqAtSpacing spacing tangent
  ≤ physicalDifferenceEnergyAtSpacing spacing tangent
physicalInverseSquareLatticeSpacingCoercivity inverseData tangent blockZero =
  subst
    (λ left → left ≤ physicalDifferenceEnergyAtSpacing _ tangent)
    (sym (coefficientTimesPhysicalNormExact inverseData tangent))
    (physicalLatticeSpacingCoercivity _ tangent blockZero)

configuredSideLatticeSpacingNormalizationLevel : ProofLevel
configuredSideLatticeSpacingNormalizationLevel = machineChecked

configuredSideInverseSquareCoefficientLevel : ProofLevel
configuredSideInverseSquareCoefficientLevel = machineChecked
