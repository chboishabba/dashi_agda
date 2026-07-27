module DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelComputed where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; -_)
import Data.Rational.Properties as ℚP
import Relation.Nullary.Decidable.Core as StdDec

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
  using (shiftForward4; shiftBackward4; siteSum4)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (axis0; axis1; axis2; axis3)

------------------------------------------------------------------------
-- Exact C4 characters over Gaussian rationals.
------------------------------------------------------------------------

Gaussianℚ : Set
Gaussianℚ = Product ℚ ℚ

realPart : Gaussianℚ → ℚ
realPart = first

imaginaryPart : Gaussianℚ → ℚ
imaginaryPart = second

multiplyGaussian : Gaussianℚ → Gaussianℚ → Gaussianℚ
multiplyGaussian (pair ar ai) (pair br bi) =
  pair (ar * br - ai * bi) (ar * bi + ai * br)

scaleGaussian : ℚ → Gaussianℚ → Gaussianℚ
scaleGaussian coefficient (pair real imaginary) =
  pair (coefficient * real) (coefficient * imaginary)

character1 : CyclicIndex four → CyclicIndex four → Gaussianℚ
character1 zeroᵢ x = pair 1ℚ 0ℚ
character1 (sucᵢ zeroᵢ) zeroᵢ = pair 1ℚ 0ℚ
character1 (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) = pair 0ℚ 1ℚ
character1 (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) = pair (- 1ℚ) 0ℚ
character1 (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = pair 0ℚ (- 1ℚ)
character1 (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ = pair 1ℚ 0ℚ
character1 (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) = pair (- 1ℚ) 0ℚ
character1 (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ zeroᵢ)) = pair 1ℚ 0ℚ
character1 (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = pair (- 1ℚ) 0ℚ
character1 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ = pair 1ℚ 0ℚ
character1 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ zeroᵢ) = pair 0ℚ (- 1ℚ)
character1 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ (sucᵢ zeroᵢ)) = pair (- 1ℚ) 0ℚ
character1 (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = pair 0ℚ 1ℚ

character4 : PhysicalBlockL side4 → PhysicalBlockL side4 → Gaussianℚ
character4
  (pair (pair k0 k1) (pair k2 k3))
  (pair (pair x0 x1) (pair x2 x3)) =
  multiplyGaussian (character1 k0 x0)
    (multiplyGaussian (character1 k1 x1)
      (multiplyGaussian (character1 k2 x2) (character1 k3 x3)))

------------------------------------------------------------------------
-- Exact spectral coefficient.  The one-dimensional Laplacian eigenvalues are
-- 0,2,4,2, so halfEigen ranges from zero through eight.
------------------------------------------------------------------------

coordinateHalfEigen : CyclicIndex four → Nat
coordinateHalfEigen zeroᵢ = 0
coordinateHalfEigen (sucᵢ zeroᵢ) = 1
coordinateHalfEigen (sucᵢ (sucᵢ zeroᵢ)) = 2
coordinateHalfEigen (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = 1

momentumHalfEigen : PhysicalBlockL side4 → Nat
momentumHalfEigen (pair (pair k0 k1) (pair k2 k3)) =
  coordinateHalfEigen k0 + coordinateHalfEigen k1
  + coordinateHalfEigen k2 + coordinateHalfEigen k3

inverseConfiguredEigen : Nat → ℚ
inverseConfiguredEigen zero = 1ℚ
inverseConfiguredEigen (suc zero) = + 1 / 2
inverseConfiguredEigen (suc (suc zero)) = + 1 / 4
inverseConfiguredEigen (suc (suc (suc zero))) = + 1 / 6
inverseConfiguredEigen (suc (suc (suc (suc zero)))) = + 1 / 8
inverseConfiguredEigen (suc (suc (suc (suc (suc zero))))) = + 1 / 10
inverseConfiguredEigen (suc (suc (suc (suc (suc (suc zero)))))) = + 1 / 12
inverseConfiguredEigen (suc (suc (suc (suc (suc (suc (suc zero))))))) = + 1 / 14
inverseConfiguredEigen
  (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = + 1 / 16
inverseConfiguredEigen _ = 0ℚ

oneTwoFiftySix : ℚ
oneTwoFiftySix = + 1 / 256

scalarGreenKernel : PhysicalBlockL side4 → ℚ
scalarGreenKernel offset =
  oneTwoFiftySix *
    sumRational (elements (periodicTorus4Finite four))
      (λ momentum →
        inverseConfiguredEigen (momentumHalfEigen momentum)
        * realPart (character4 momentum offset))

scalarKernelLaplacian : PhysicalBlockL side4 → ℚ
scalarKernelLaplacian offset =
  (scalarGreenKernel offset + scalarGreenKernel offset)
  - (scalarGreenKernel (shiftForward4 axis0 offset)
    + scalarGreenKernel (shiftBackward4 axis0 offset))
  + ((scalarGreenKernel offset + scalarGreenKernel offset)
    - (scalarGreenKernel (shiftForward4 axis1 offset)
      + scalarGreenKernel (shiftBackward4 axis1 offset)))
  + ((scalarGreenKernel offset + scalarGreenKernel offset)
    - (scalarGreenKernel (shiftForward4 axis2 offset)
      + scalarGreenKernel (shiftBackward4 axis2 offset)))
  + ((scalarGreenKernel offset + scalarGreenKernel offset)
    - (scalarGreenKernel (shiftForward4 axis3 offset)
      + scalarGreenKernel (shiftBackward4 axis3 offset)))

zeroSite4 : PhysicalBlockL side4
zeroSite4 = pair (pair zeroᵢ zeroᵢ) (pair zeroᵢ zeroᵢ)

scalarDeltaAtZero : PhysicalBlockL side4 → ℚ
scalarDeltaAtZero offset
  with periodicTorus4DecidableEquality four offset zeroSite4
... | yes equality = 1ℚ
... | no inequality = 0ℚ

KernelEquation : PhysicalBlockL side4 → Set
KernelEquation offset =
  scalarKernelLaplacian offset + oneTwoFiftySix
  ≡ scalarDeltaAtZero offset

------------------------------------------------------------------------
-- Generic finite checked-universal quantification.  The only large computation
-- is the closed decision over the 256 literal offsets; arbitrary-offset use is
-- then obtained from enumeration completeness.
------------------------------------------------------------------------

data All {A : Set} (Predicate : A → Set) : List A → Set where
  all[] : All Predicate []
  _all∷_ : ∀ {value values} →
    Predicate value → All Predicate values → All Predicate (value ∷ values)

lookupAll : ∀ {A : Set} {Predicate : A → Set} {value values} →
  value ∈ values → All Predicate values → Predicate value
lookupAll here (proof all∷ proofs) = proof
lookupAll (there membership) (proof all∷ proofs) = lookupAll membership proofs

decideAll : ∀ {A : Set} {Predicate : A → Set} →
  (∀ value → StdDec.Dec (Predicate value)) →
  (values : List A) → StdDec.Dec (All Predicate values)
decideAll decide [] = StdDec.yes all[]
decideAll decide (value ∷ values)
  with decide value | decideAll decide values
... | StdDec.yes proof | StdDec.yes proofs = StdDec.yes (proof all∷ proofs)
... | StdDec.no refute | tailDecision =
  StdDec.no (λ where (proof all∷ proofs) → refute proof)
... | StdDec.yes proof | StdDec.no refute =
  StdDec.no (λ where (headProof all∷ tailProofs) → refute tailProofs)

data IsYes {Proposition : Set} : StdDec.Dec Proposition → Set where
  isYes : ∀ {proof : Proposition} → IsYes (StdDec.yes proof)

extractYes : ∀ {Proposition : Set} (decision : StdDec.Dec Proposition) →
  IsYes decision → Proposition
extractYes (StdDec.yes proof) isYes = proof
extractYes (StdDec.no refute) ()

kernelEquationDecision : ∀ offset → StdDec.Dec (KernelEquation offset)
kernelEquationDecision offset =
  ℚP._≟_
    (scalarKernelLaplacian offset + oneTwoFiftySix)
    (scalarDeltaAtZero offset)

allKernelEquationDecision :
  StdDec.Dec
    (All KernelEquation (elements (periodicTorus4Finite four)))
allKernelEquationDecision =
  decideAll kernelEquationDecision (elements (periodicTorus4Finite four))

allKernelEquationDecisionIsYes : IsYes allKernelEquationDecision
allKernelEquationDecisionIsYes = isYes

allKernelEquations :
  All KernelEquation (elements (periodicTorus4Finite four))
allKernelEquations =
  extractYes allKernelEquationDecision allKernelEquationDecisionIsYes

scalarGreenKernelEquation : ∀ offset → KernelEquation offset
scalarGreenKernelEquation offset =
  lookupAll
    (complete (periodicTorus4Finite four) offset)
    allKernelEquations

KernelNormalization : Set
KernelNormalization = siteSum4 scalarGreenKernel ≡ 1ℚ

kernelNormalizationDecision : StdDec.Dec KernelNormalization
kernelNormalizationDecision = ℚP._≟_ (siteSum4 scalarGreenKernel) 1ℚ

kernelNormalizationDecisionIsYes : IsYes kernelNormalizationDecision
kernelNormalizationDecisionIsYes = isYes

scalarGreenKernelTotalExact : KernelNormalization
scalarGreenKernelTotalExact =
  extractYes kernelNormalizationDecision kernelNormalizationDecisionIsYes

scalarGreenKernelComputedLevel : ProofLevel
scalarGreenKernelComputedLevel = machineChecked

scalarGreenKernelEquationLevel : ProofLevel
scalarGreenKernelEquationLevel = machineChecked

scalarGreenKernelNormalizationLevel : ProofLevel
scalarGreenKernelNormalizationLevel = machineChecked
