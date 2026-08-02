module DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingDimensionAuditExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance and convention separation.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
-- This paper gives the original local averaging operation studied in the
-- preceding tranche, including equations (42)--(43) and Proposition 4.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
-- This later four-dimensional RG paper uses its own Euclidean-symmetric
-- averaging convention.  Constants and support statements may be transported
-- between the papers only after an explicit convention-identification proof.
--
-- For the CMP 98 formula, equations (42) and (43) use the volume coefficient
-- L^{-d}, not L^{-(d-1)}.  Consequently, for dyadic blocking L = 2, the literal
-- averaging coefficient is 1/8 in d = 3 and 1/16 in d = 4.
--
-- Proposition 4 and equations (146)--(147) prove locality, analyticity and a
-- uniform bound on the linearized kernel Q_k(U_0;c,b).  They do not state a
-- relative 1/8 contraction of the squared adjoint norm.  The latter remains a
-- separate normalized weighted-kernel theorem.
--
-- Secondary orientation.
--
-- Abhishek Goswami,
-- "The Variational Problem and Background Field in the Renormalization Group
-- Method for Nonlinear Sigma Models", Annales Henri Poincare 25 (2024),
-- 2065--2085. DOI: 10.1007/s00023-023-01353-7; arXiv:2204.08252.
-- Relationship: peer-reviewed exposition confirming that Bałaban's programme
-- treats lattice Yang--Mills in d = 3,4 and locating the constrained minimizer
-- and background-field formulas.  It is not substituted for Bałaban's primary
-- equation text.
------------------------------------------------------------------------

data SourceAuthority : Set where
  primaryPeerReviewed : SourceAuthority
  peerReviewedSecondary : SourceAuthority
  quarantinedLocator : SourceAuthority

data AveragingExponentConvention : Set where
  volumeDimensionExponent : AveragingExponentConvention

data AveragingOperatorConvention : Set where
  cmp98OriginalLocalAverage : AveragingOperatorConvention
  cmp109EuclideanSymmetricAverage : AveragingOperatorConvention

data ClaimUse : Set where
  theoremAuthority : ClaimUse
  methodologicalOrientation : ClaimUse
  locatorOnly : ClaimUse

record SourceClassification : Set where
  constructor classifySource
  field
    title author identifier : String
    authority : SourceAuthority
    use : ClaimUse

open SourceClassification public

balabanAveragingPrimary : SourceClassification
balabanAveragingPrimary = classifySource
  "Averaging Operations for Lattice Gauge Theories"
  "Tadeusz Balaban"
  "DOI 10.1007/BF01211042"
  primaryPeerReviewed
  theoremAuthority

balabanFourDimensionalRGPrimary : SourceClassification
balabanFourDimensionalRGPrimary = classifySource
  "Renormalization Group Approach to Lattice Gauge Field Theories. I. Generation of Effective Actions in a Small Field Approximation and a Coupling Constant Renormalization in Four Dimensions"
  "Tadeusz Balaban"
  "DOI 10.1007/BF01215223"
  primaryPeerReviewed
  theoremAuthority

goswamiBackgroundFieldSecondary : SourceClassification
goswamiBackgroundFieldSecondary = classifySource
  "The Variational Problem and Background Field in the Renormalization Group Method for Nonlinear Sigma Models"
  "Abhishek Goswami"
  "DOI 10.1007/s00023-023-01353-7; arXiv:2204.08252"
  peerReviewedSecondary
  methodologicalOrientation

balabanDimockStructuralPackageLocator : SourceClassification
balabanDimockStructuralPackageLocator = classifySource
  "The Balaban-Dimock Structural Package"
  "unverified locator authorship"
  "ai.viXra:2602.0069v1; no DOI"
  quarantinedLocator
  locatorOnly

primaryEquation42And43Exponent : AveragingExponentConvention
primaryEquation42And43Exponent = volumeDimensionExponent

dyadicD3AveragingWeight dyadicD4AveragingWeight : ℚ
dyadicD3AveragingWeight = + 1 / 8
dyadicD4AveragingWeight = + 1 / 16

dyadicD3WeightExact : dyadicD3AveragingWeight ≡ + 1 / 8
dyadicD3WeightExact = refl

dyadicD4WeightExact : dyadicD4AveragingWeight ≡ + 1 / 16
dyadicD4WeightExact = refl

record SelectedAveragingConvention : Set where
  constructor selectedAveragingConvention
  field
    operatorConvention : AveragingOperatorConvention
    dimension blockSide : Nat
    coefficient : ℚ
    sourceUsesVolumeExponent : AveragingExponentConvention
    coefficientIsOperatorContraction : Bool

open SelectedAveragingConvention public

fourDimensionalDyadicCMP98Convention : SelectedAveragingConvention
fourDimensionalDyadicCMP98Convention = selectedAveragingConvention
  cmp98OriginalLocalAverage
  4 2 dyadicD4AveragingWeight volumeDimensionExponent false

threeDimensionalDyadicCMP98Convention : SelectedAveragingConvention
threeDimensionalDyadicCMP98Convention = selectedAveragingConvention
  cmp98OriginalLocalAverage
  3 2 dyadicD3AveragingWeight volumeDimensionExponent false

-- Backwards-compatible names retained for existing imports.
fourDimensionalDyadicPrimaryConvention : SelectedAveragingConvention
fourDimensionalDyadicPrimaryConvention = fourDimensionalDyadicCMP98Convention

threeDimensionalDyadicPrimaryConvention : SelectedAveragingConvention
threeDimensionalDyadicPrimaryConvention = threeDimensionalDyadicCMP98Convention

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

record PhysicalAveragingConventionMeaning
    {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
    (LiteralMap : Set ℓ₁) (Derivative : Set ℓ₂)
    (Support : Set ℓ₃) (Normalization : Set ℓ₄) : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    selectedConvention : AveragingOperatorConvention

    LiteralMapMatches : AveragingOperatorConvention → LiteralMap → Set
    DerivativeMatches : AveragingOperatorConvention → Derivative → Set
    SupportMatches : AveragingOperatorConvention → Support → Set
    NormalizationMatches : AveragingOperatorConvention → Normalization → Set

    physicalLiteralMap : LiteralMap
    physicalDerivative : Derivative
    physicalSupport : Support
    physicalNormalization : Normalization

    literalMapMatchesSelected :
      LiteralMapMatches selectedConvention physicalLiteralMap
    derivativeMatchesSelected :
      DerivativeMatches selectedConvention physicalDerivative
    supportMatchesSelected :
      SupportMatches selectedConvention physicalSupport
    normalizationMatchesSelected :
      NormalizationMatches selectedConvention physicalNormalization

open PhysicalAveragingConventionMeaning public

primaryAveragingNormalizationLevel : ProofLevel
primaryAveragingNormalizationLevel = standardImported

dyadicDimensionArithmeticLevel : ProofLevel
dyadicDimensionArithmeticLevel = machineChecked

averagingOperatorConventionDistinctionLevel : ProofLevel
averagingOperatorConventionDistinctionLevel = standardImported

qkPrimaryKernelBoundProvenanceLevel : ProofLevel
qkPrimaryKernelBoundProvenanceLevel = standardImported

physicalAveragingConventionSelectionInputsLevel : ProofLevel
physicalAveragingConventionSelectionInputsLevel = conditional

qstarOneEighthContractionFromPrimaryCoefficientLevel : ProofLevel
qstarOneEighthContractionFromPrimaryCoefficientLevel = conjectural

structuralPackageAcceptedAsAuthority : Bool
structuralPackageAcceptedAsAuthority = false
