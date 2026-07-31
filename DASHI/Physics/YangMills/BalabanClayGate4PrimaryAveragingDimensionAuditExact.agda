module DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingDimensionAuditExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Balaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Equations (42) and (43) define the one-step and iterated bond averaging
-- operations with the volume coefficient L^{-d}.  They do not use
-- L^{-(d-1)}.  Consequently, for dyadic blocking L = 2, the literal averaging
-- coefficient is 1/8 in d = 3 and 1/16 in d = 4.
--
-- Proposition 4 and equations (146)--(147) prove locality, analyticity and a
-- uniform bound on the linearized kernel Q_k(U_0;c,b).  They do not state a
-- relative 1/8 contraction of the squared adjoint norm.  The latter remains a
-- separate normalized kernel theorem.
--
-- Secondary orientation.
--
-- Abhishek Goswami,
-- "The Variational Problem and Background Field in the Renormalization Group
-- Method for Non-Linear Sigma Models", Annales Henri Poincare 25 (2024).
-- DOI: 10.1007/s00023-023-01353-7; arXiv:2204.08252.
-- Relationship: peer-reviewed exposition confirming that Balaban's programme
-- treats lattice Yang--Mills in d = 3,4 and locating the constrained minimizer
-- and background-field formulas.  It is not substituted for Balaban's primary
-- equation text.
------------------------------------------------------------------------

data SourceAuthority : Set where
  primaryPeerReviewed : SourceAuthority
  peerReviewedSecondary : SourceAuthority
  quarantinedLocator : SourceAuthority

data AveragingExponentConvention : Set where
  volumeDimensionExponent : AveragingExponentConvention

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

goswamiBackgroundFieldSecondary : SourceClassification
goswamiBackgroundFieldSecondary = classifySource
  "The Variational Problem and Background Field in the Renormalization Group Method for Non-Linear Sigma Models"
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
    dimension blockSide : Nat
    coefficient : ℚ
    sourceUsesVolumeExponent : AveragingExponentConvention
    coefficientIsOperatorContraction : Bool

open SelectedAveragingConvention public

fourDimensionalDyadicPrimaryConvention : SelectedAveragingConvention
fourDimensionalDyadicPrimaryConvention = selectedAveragingConvention
  4 2 dyadicD4AveragingWeight volumeDimensionExponent false

threeDimensionalDyadicPrimaryConvention : SelectedAveragingConvention
threeDimensionalDyadicPrimaryConvention = selectedAveragingConvention
  3 2 dyadicD3AveragingWeight volumeDimensionExponent false

primaryAveragingNormalizationLevel : ProofLevel
primaryAveragingNormalizationLevel = standardImported

dyadicDimensionArithmeticLevel : ProofLevel
dyadicDimensionArithmeticLevel = machineChecked

qkPrimaryKernelBoundProvenanceLevel : ProofLevel
qkPrimaryKernelBoundProvenanceLevel = standardImported

qstarOneEighthContractionFromPrimaryCoefficientLevel : ProofLevel
qstarOneEighthContractionFromPrimaryCoefficientLevel = conjectural

structuralPackageAcceptedAsAuthority : Bool
structuralPackageAcceptedAsAuthority = false
