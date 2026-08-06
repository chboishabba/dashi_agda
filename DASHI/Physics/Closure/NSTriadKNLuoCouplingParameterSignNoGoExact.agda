module DASHI.Physics.Closure.NSTriadKNLuoCouplingParameterSignNoGoExact where

------------------------------------------------------------------------
-- PRIMARY AUDIT TARGET
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO. DOI: none located.
-- Status: manuscript/preprint and audit target only.
--
-- DASHI CONTRIBUTION
--
-- The manuscript assumes an estimate of the form
--
--   S' <= C2 (E + D)
--
-- and couples it with the gradient inequality using T = E + alpha S.
-- The resulting Laplacian coefficient is
--
--   2 nu - alpha C2,
--
-- while the new energy source is alpha C2 E.  Therefore choosing alpha so
-- large that alpha C2 >= 2 nu makes the dissipative coefficient nonpositive;
-- at equality it is exactly zero.  Choosing alpha smaller does not remove the
-- positive alpha C2 E source.  A valid coupled functional needs a genuine
-- negative response cancelling the nonlinear transfer, not another positive
-- upper bound.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; -_; _-_; _≤_; _<_; positive; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

record CouplingParameters : Set where
  constructor couplingParameters
  field
    viscosity alpha structuralConstant energy : ℚ
    viscosityNonnegative : 0ℚ ≤ viscosity
    alphaNonnegative : 0ℚ ≤ alpha
    structuralConstantNonnegative : 0ℚ ≤ structuralConstant
    energyNonnegative : 0ℚ ≤ energy

open CouplingParameters public

dissipativeCoefficient : CouplingParameters → ℚ
dissipativeCoefficient parameters =
  2 * viscosity parameters
  - alpha parameters * structuralConstant parameters

coupledEnergySource : CouplingParameters → ℚ
coupledEnergySource parameters =
  alpha parameters
  * structuralConstant parameters
  * energy parameters

largeCouplingDestroysStrictDissipation :
  ∀ parameters →
  2 * viscosity parameters
    ≤ alpha parameters * structuralConstant parameters →
  dissipativeCoefficient parameters ≤ 0ℚ
largeCouplingDestroysStrictDissipation parameters threshold =
  let
    shifted :
      2 * viscosity parameters
        + (- (alpha parameters * structuralConstant parameters))
      ≤
      alpha parameters * structuralConstant parameters
        + (- (alpha parameters * structuralConstant parameters))
    shifted =
      ℚₚ.+-monoʳ-≤
        (- (alpha parameters * structuralConstant parameters))
        threshold

    leftMeaning :
      2 * viscosity parameters
        + (- (alpha parameters * structuralConstant parameters))
      ≡ dissipativeCoefficient parameters
    leftMeaning =
      solve
        ( viscosity parameters
        ∷ alpha parameters
        ∷ structuralConstant parameters
        ∷ [])

    rightMeaning :
      alpha parameters * structuralConstant parameters
        + (- (alpha parameters * structuralConstant parameters))
      ≡ 0ℚ
    rightMeaning =
      solve
        ( alpha parameters
        ∷ structuralConstant parameters
        ∷ [])

    normalizedLeft :
      dissipativeCoefficient parameters
      ≤
      alpha parameters * structuralConstant parameters
        + (- (alpha parameters * structuralConstant parameters))
    normalizedLeft =
      subst
        (λ left →
          left
          ≤ alpha parameters * structuralConstant parameters
            + (- (alpha parameters * structuralConstant parameters)))
        leftMeaning
        shifted
  in
  subst
    (λ right → dissipativeCoefficient parameters ≤ right)
    rightMeaning
    normalizedLeft

thresholdChoiceHasZeroDissipation :
  ∀ parameters →
  alpha parameters * structuralConstant parameters
    ≡ 2 * viscosity parameters →
  dissipativeCoefficient parameters ≡ 0ℚ
thresholdChoiceHasZeroDissipation parameters equality
  rewrite equality =
  solve (viscosity parameters ∷ [])

coupledEnergySourceNonnegative :
  ∀ parameters → 0ℚ ≤ coupledEnergySource parameters
coupledEnergySourceNonnegative parameters =
  let
    instance
      alphaNN = nonNegative (alphaNonnegative parameters)
      constantNN =
        nonNegative (structuralConstantNonnegative parameters)
      firstProductNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (alpha parameters)
          (structuralConstant parameters)
      energyNN = nonNegative (energyNonnegative parameters)
      secondProductNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (alpha parameters * structuralConstant parameters)
          (energy parameters)
  in
  ℚₚ.nonNegative⁻¹ (coupledEnergySource parameters)

strictPositiveSource :
  ∀ parameters →
  0ℚ < alpha parameters →
  0ℚ < structuralConstant parameters →
  0ℚ < energy parameters →
  0ℚ < coupledEnergySource parameters
strictPositiveSource parameters alphaPositive constantPositive energyPositive =
  let
    instance
      alphaPositiveInstance = positive alphaPositive
      constantPositiveInstance = positive constantPositive
      firstProductPositive =
        ℚₚ.pos*pos⇒pos
          (alpha parameters)
          (structuralConstant parameters)
      energyPositiveInstance = positive energyPositive
      secondProductPositive =
        ℚₚ.pos*pos⇒pos
          (alpha parameters * structuralConstant parameters)
          (energy parameters)
  in
  ℚₚ.positive⁻¹ (coupledEnergySource parameters)

record CouplingSignAuditConclusion : Set where
  constructor couplingSignAuditConclusion
  field
    choosingAlphaAboveThresholdCreatesDissipation : Set
    choosingAlphaAtThresholdLeavesStrictMargin : Set
    positiveEnergySourceAutomaticallyCancelled : Set
    negativeStabilityResponseStillRequired : Set

canonicalCouplingSignAuditConclusion : CouplingSignAuditConclusion
canonicalCouplingSignAuditConclusion =
  couplingSignAuditConclusion
    ⊥ ⊥ ⊥ ⊤
  where
  open import Data.Empty using (⊥)
  open import Data.Unit using (⊤)
