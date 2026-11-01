module DASHI.Wikimedia.IbrahimA027907PathCubeConvolutionAttributionProofExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Moonshine.Base369Ternary27PathCubeSpectralBandsExact as Bands
import DASHI.Wikimedia.IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact as Seam
import DASHI.Wikimedia.IbrahimTernaryGeometricPartialSumRegularisationOEISSnowballExact as Geo

------------------------------------------------------------------------
-- A027907 ATTRIBUTION + CONSUMER-PRESERVING CONVOLUTION PROOF
--
-- Keep four attribution roles distinct:
--
--   N. J. A. Sloane  : A027907 sequence author / canonical OEIS entry,
--   Gerald McGarvey   : row sums are powers of 3 (OEIS formula contribution),
--   Tony Foster III   : even-position sub-sum = (3^n-1)/2,
--   Shapiro et al.    : cited Riordan-array literature provenance.
--
-- None of these attribution records is itself the local proof.
--
-- Local proof route:
--
--   one path axis has one mode of each type  [-sqrt2,0,+sqrt2]
--   -> convolution by [1,1,1]
--   -> n=1 row [1,1,1]
--   -> n=2 row [1,2,3,2,1]
--   -> n=3 row [1,3,6,7,6,3,1]
--   -> literal P3 □ P3 □ P3 bandMultiplicity row.
--
-- This pays why A027907 appears here: both constructions count the same
-- three-choice tensor-sum multiplicity grammar.  It does NOT identify the
-- path-cube action with Albert/F4/E6/Monster actions.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. External attribution receipts.
------------------------------------------------------------------------

oeisA027907Source : Attribution.AttributedSource
oeisA027907Source = Attribution.mkNoDOISource
  "N. J. A. Sloane"
  "A027907: Triangle of trinomial coefficients"
  "The On-Line Encyclopedia of Integer Sequences"
  "current entry; contributor history retained by OEIS"
  "https://oeis.org/A027907"
  (Attribution.namedSourceKind "reference database / integer-sequence entry")
  "canonical external coordinate for coefficients of (1+x+x^2)^n; source identity and contributor notes do not import a DASHI theorem"
  Attribution.publicAttribution

riordanGroupSource : Attribution.AttributedSource
riordanGroupSource = Attribution.mkDOISource
  "Louis W. Shapiro; Seyoum Getu; Wen-Jin Woan; Leon C. Woodson"
  "The Riordan group"
  "Discrete Applied Mathematics 34 (1991), 229-239"
  "1991"
  "10.1016/0166-218X(91)90088-E"
  "https://doi.org/10.1016/0166-218X(91)90088-E"
  Attribution.academicArticleSource
  "literature provenance cited by A027907; does not by citation alone prove the path-cube spectral identification"
  Attribution.publicAttribution

oeisAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt oeisA027907Source
riordanAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt riordanGroupSource

record OEISContributorAttribution : Set where
  constructor oeis-contributor-attribution
  field
    contributor : String
    contribution : String
    contributionDate : String
    externalObject : String
    localClaimSeparatelyChecked : Bool
open OEISContributorAttribution public

sloaneSequenceAttribution : OEISContributorAttribution
sloaneSequenceAttribution = oeis-contributor-attribution
  "N. J. A. Sloane"
  "author of A027907; n-th row is the coefficient row of (1+x+x^2)^n"
  "OEIS author field / current entry"
  "A027907"
  true

mcGarveyRowSumAttribution : OEISContributorAttribution
mcGarveyRowSumAttribution = oeis-contributor-attribution
  "Gerald McGarvey"
  "row sums are powers of 3 (A000244)"
  "2004-08-14"
  "A027907 formula contribution"
  true

fosterEvenSubsumAttribution : OEISContributorAttribution
fosterEvenSubsumAttribution = oeis-contributor-attribution
  "Tony Foster III"
  "sum_{k=0..n-1} T(n,2*k) = (3^n-1)/2"
  "2020-10-06"
  "A027907 formula contribution"
  true

------------------------------------------------------------------------
-- 2. Explicit three-choice convolution rows.
------------------------------------------------------------------------

-- n=0

t00 : Nat
t00 = 1

-- n=1 = [1] convolved with [1,1,1].
t10 t11 t12 : Nat
t10 = t00
t11 = t00
t12 = t00

row1Is111 : t10 ≡ 1 × t11 ≡ 1 × t12 ≡ 1
row1Is111 = refl , refl , refl

-- n=2 = [1,1,1] convolved with [1,1,1].
t20 t21 t22 t23 t24 : Nat
t20 = t10
t21 = t10 + t11
t22 = t10 + t11 + t12
t23 = t11 + t12
t24 = t12

row2Is12321 :
  t20 ≡ 1 × t21 ≡ 2 × t22 ≡ 3 × t23 ≡ 2 × t24 ≡ 1
row2Is12321 = refl , refl , refl , refl , refl

-- n=3 = [1,2,3,2,1] convolved with [1,1,1].
t30 t31 t32 t33 t34 t35 t36 : Nat
t30 = t20
t31 = t20 + t21
t32 = t20 + t21 + t22
t33 = t21 + t22 + t23
t34 = t22 + t23 + t24
t35 = t23 + t24
t36 = t24

row3Is1367631 :
  t30 ≡ 1 × t31 ≡ 3 × t32 ≡ 6 × t33 ≡ 7 ×
  t34 ≡ 6 × t35 ≡ 3 × t36 ≡ 1
row3Is1367631 = refl , refl , refl , refl , refl , refl , refl

------------------------------------------------------------------------
-- 3. Exact weld to the existing literal path-cube spectral consumer.
------------------------------------------------------------------------

pathBandMinus3MatchesTrinomial :
  Bands.bandMultiplicity Bands.bandMinus3 ≡ t30
pathBandMinus3MatchesTrinomial = refl

pathBandMinus2MatchesTrinomial :
  Bands.bandMultiplicity Bands.bandMinus2 ≡ t31
pathBandMinus2MatchesTrinomial = refl

pathBandMinus1MatchesTrinomial :
  Bands.bandMultiplicity Bands.bandMinus1 ≡ t32
pathBandMinus1MatchesTrinomial = refl

pathBandZeroMatchesTrinomial :
  Bands.bandMultiplicity Bands.bandZero ≡ t33
pathBandZeroMatchesTrinomial = refl

pathBandPlus1MatchesTrinomial :
  Bands.bandMultiplicity Bands.bandPlus1 ≡ t34
pathBandPlus1MatchesTrinomial = refl

pathBandPlus2MatchesTrinomial :
  Bands.bandMultiplicity Bands.bandPlus2 ≡ t35
pathBandPlus2MatchesTrinomial = refl

pathBandPlus3MatchesTrinomial :
  Bands.bandMultiplicity Bands.bandPlus3 ≡ t36
pathBandPlus3MatchesTrinomial = refl

literalPathCubeRowIsThirdTrinomialConvolution :
  Bands.bandMultiplicity Bands.bandMinus3 ≡ t30 ×
  Bands.bandMultiplicity Bands.bandMinus2 ≡ t31 ×
  Bands.bandMultiplicity Bands.bandMinus1 ≡ t32 ×
  Bands.bandMultiplicity Bands.bandZero ≡ t33 ×
  Bands.bandMultiplicity Bands.bandPlus1 ≡ t34 ×
  Bands.bandMultiplicity Bands.bandPlus2 ≡ t35 ×
  Bands.bandMultiplicity Bands.bandPlus3 ≡ t36
literalPathCubeRowIsThirdTrinomialConvolution =
  refl , refl , refl , refl , refl , refl , refl

------------------------------------------------------------------------
-- 4. Follow the proved row into the existing 10 / 13 consumers.
------------------------------------------------------------------------

provedLeftFlank : Nat
provedLeftFlank = t30 + t31 + t32

provedLeftFlankIsTen : provedLeftFlank ≡ 10
provedLeftFlankIsTen = refl

provedEvenPrefix : Nat
provedEvenPrefix = t30 + t32 + t34

provedEvenPrefixIsThirteen : provedEvenPrefix ≡ 13
provedEvenPrefixIsThirteen = refl

provedEvenPrefixMatchesA003462ThirdPartial :
  provedEvenPrefix ≡ Geo.partialSum3 3
provedEvenPrefixMatchesA003462ThirdPartial = refl

provedEvenPrefixMatchesExistingSeam :
  provedEvenPrefix ≡ Seam.evenPrefix
provedEvenPrefixMatchesExistingSeam = refl

provedRowSum : Nat
provedRowSum = t30 + t31 + t32 + t33 + t34 + t35 + t36

provedRowSumIsTwentySeven : provedRowSum ≡ 27
provedRowSumIsTwentySeven = refl

provedRowSumMatchesPathCube :
  provedRowSum ≡ Bands.spectralMultiplicityTotal
provedRowSumMatchesPathCube = refl

------------------------------------------------------------------------
-- 5. Why this is stronger than OEIS membership but weaker than an action iso.
------------------------------------------------------------------------

data OEISAttributionImportsLocalProof : Set where
data MatchingCoefficientRowCreatesActionIso : Set where
data ConvolutionGrammarCreatesExceptionalAction : Set where
data SharedThirteenCreatesSameCarrier : Set where

oeisAttributionDoesNotImportProof : OEISAttributionImportsLocalProof → ⊥
oeisAttributionDoesNotImportProof ()

coefficientMatchDoesNotCreateActionIso : MatchingCoefficientRowCreatesActionIso → ⊥
coefficientMatchDoesNotCreateActionIso ()

convolutionDoesNotCreateExceptionalAction : ConvolutionGrammarCreatesExceptionalAction → ⊥
convolutionDoesNotCreateExceptionalAction ()

sharedThirteenDoesNotCreateSameCarrier : SharedThirteenCreatesSameCarrier → ⊥
sharedThirteenDoesNotCreateSameCarrier ()

record A027907ConvolutionAttributionFrontier : Set where
  constructor a027907-convolution-attribution-frontier
  field
    oeisSequenceAuthorAttributed : Bool
    rowSumContributorAttributed : Bool
    evenSubsumContributorAttributed : Bool
    riordanLiteratureDOIAttached : Bool
    n1ConvolutionPaid : Bool
    n2ConvolutionPaid : Bool
    n3ConvolutionPaid : Bool
    literalPathCubeRowWeldPaid : Bool
    leftFlankTenRecoveredFromProof : Bool
    evenPrefixThirteenRecoveredFromProof : Bool
    a003462ThirdPartialRecoveredFromProof : Bool
    actionIntertwinerPaid : Bool
    nextResidual : String
open A027907ConvolutionAttributionFrontier public

currentA027907ConvolutionAttributionFrontier : A027907ConvolutionAttributionFrontier
currentA027907ConvolutionAttributionFrontier = a027907-convolution-attribution-frontier
  true true true true
  true true true true
  true true true false
  "generalise the finite convolution witness from the hard-coded n=3 rows to a reusable coefficient recurrence only if an existing polynomial/list carrier can host it cheaply. For the proof we actually need next, keep the literal P3^3 consumer and test whether its three-axis tensor-factor decomposition supplies any same-object map to an already-owned 27-dimensional Albert/E6 carrier; numerical equality, A027907 membership, and the shared 13 atom remain insufficient without an action/intertwiner."
