module DASHI.Physics.YangMills.BalabanClayGate4BFAverageCoherenceScopeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Bałaban--Federbush averaging coherence: exact source scope.
--
-- Hugo H. Torriani and Michiel Hazewinkel,
-- "Coherence and Uniqueness Theorems for Averaging Processes in Statistical
-- Mechanics", Acta Applicandae Mathematicae 77 (2003), 105--123.
-- DOI: 10.1023/A:1024018909120.
-- arXiv: math-ph/0410046.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Scope correction:
--
-- * Torriani--Hazewinkel prove coherence of the BF weight formula in every
--   dimension and prove a factorized uniqueness theorem via the D=1 case.
-- * Their fully nonfactorized symmetry theorem is proved in D=2 (Theorem 6.1);
--   the higher-dimensional version is explicitly Conjecture 6.2.
-- * Their objects are scalar plaquette-function averages.  The paper does not
--   prove existence of Bałaban's non-Abelian analytic group centre defined by
--   equation (0.10).
--
-- The current repository's 1/16 dyadic carrier has exact scalar two-step
-- coherence, but identification with CMP109's centred block convention remains
-- a physical convention bridge rather than a consequence of the BF paper.
------------------------------------------------------------------------

record BFAverageSourceReceipt : Set where
  constructor bfAverageSourceReceipt
  field
    firstAuthor secondAuthor title journal yearPages doi arxiv : String

open BFAverageSourceReceipt public

hazewinkelTorriani2003 : BFAverageSourceReceipt
hazewinkelTorriani2003 = record
  { firstAuthor = "Hugo H. Torriani"
  ; secondAuthor = "Michiel Hazewinkel"
  ; title = "Coherence and Uniqueness Theorems for Averaging Processes in Statistical Mechanics"
  ; journal = "Acta Applicandae Mathematicae 77"
  ; yearPages = "2003, 105-123"
  ; doi = "10.1023/A:1024018909120"
  ; arxiv = "math-ph/0410046"
  }

record BFAverageScopeAudit : Set where
  constructor bfAverageScopeAudit
  field
    coherenceFormulaAllDimensions : Bool
    factorizedUniquenessViaDimensionOne : Bool
    nonfactorizedSymmetricUniquenessDimensionTwo : Bool
    higherDimensionalNonfactorizedStatementIsConjecture : Bool
    higherDimensionalNonfactorizedStatementProved : Bool
    nonAbelianFederbushCentreExistenceProved : Bool

open BFAverageScopeAudit public

bfAverageScope : BFAverageScopeAudit
bfAverageScope = record
  { coherenceFormulaAllDimensions = true
  ; factorizedUniquenessViaDimensionOne = true
  ; nonfactorizedSymmetricUniquenessDimensionTwo = true
  ; higherDimensionalNonfactorizedStatementIsConjecture = true
  ; higherDimensionalNonfactorizedStatementProved = false
  ; nonAbelianFederbushCentreExistenceProved = false
  }

bfHigherDimensionalNonfactorizedNotPromoted :
  higherDimensionalNonfactorizedStatementProved bfAverageScope ≡ false
bfHigherDimensionalNonfactorizedNotPromoted = refl

bfNonAbelianCentreExistenceNotAttributed :
  nonAbelianFederbushCentreExistenceProved bfAverageScope ≡ false
bfNonAbelianCentreExistenceNotAttributed = refl

------------------------------------------------------------------------
-- Exact scalar normalization and two-step dyadic coherence.
------------------------------------------------------------------------

addNat : Nat → Nat → Nat
addNat zero right = right
addNat (suc left) right = suc (addNat left right)

multiplyNat : Nat → Nat → Nat
multiplyNat zero right = zero
multiplyNat (suc left) right = addNat right (multiplyNat left right)

twice : Nat → Nat
twice value = addNat value value

fourthPower : Nat → Nat
fourthPower value =
  multiplyNat value
    (multiplyNat value (multiplyNat value value))

record PositiveFraction : Set where
  constructor positiveFraction
  field
    numerator denominator : Nat

open PositiveFraction public

multiplyFraction : PositiveFraction → PositiveFraction → PositiveFraction
multiplyFraction
    (positiveFraction leftNumerator leftDenominator)
    (positiveFraction rightNumerator rightDenominator) =
  positiveFraction
    (multiplyNat leftNumerator rightNumerator)
    (multiplyNat leftDenominator rightDenominator)

oneSixteenth : PositiveFraction
oneSixteenth = positiveFraction 1 16

oneTwoHundredFiftySix : PositiveFraction
oneTwoHundredFiftySix = positiveFraction 1 256

dyadicFourDimensionalTwoStepWeight :
  multiplyFraction oneSixteenth oneSixteenth
  ≡ oneTwoHundredFiftySix
dyadicFourDimensionalTwoStepWeight = refl

record CMP109CenteredOddBlockNormalization : Set where
  constructor cmp109CenteredOddBlockNormalization
  field
    radius blockSide blockVolume : Nat
    blockWeight : PositiveFraction

    blockSideMeaning : blockSide ≡ suc (twice radius)
    blockVolumeMeaning : blockVolume ≡ fourthPower blockSide
    blockWeightMeaning :
      blockWeight ≡ positiveFraction 1 blockVolume

open CMP109CenteredOddBlockNormalization public

canonicalCenteredOddBlockNormalization :
  Nat → CMP109CenteredOddBlockNormalization
canonicalCenteredOddBlockNormalization radius = record
  { radius = radius
  ; blockSide = suc (twice radius)
  ; blockVolume = fourthPower (suc (twice radius))
  ; blockWeight = positiveFraction 1
      (fourthPower (suc (twice radius)))
  ; blockSideMeaning = refl
  ; blockVolumeMeaning = refl
  ; blockWeightMeaning = refl
  }

bfAverageBibliographyLevel : ProofLevel
bfAverageBibliographyLevel = computed

bfCoherenceAllDimensionsLevel : ProofLevel
bfCoherenceAllDimensionsLevel = standardImported

bfFactorizedUniquenessAllDimensionsLevel : ProofLevel
bfFactorizedUniquenessAllDimensionsLevel = standardImported

bfNonfactorizedUniquenessDimensionTwoLevel : ProofLevel
bfNonfactorizedUniquenessDimensionTwoLevel = standardImported

bfNonfactorizedUniquenessHigherDimensionsLevel : ProofLevel
bfNonfactorizedUniquenessHigherDimensionsLevel = conjectural

bfSourceScopeFailClosedLevel : ProofLevel
bfSourceScopeFailClosedLevel = machineChecked

dyadicFourDimensionalTwoStepWeightLevel : ProofLevel
dyadicFourDimensionalTwoStepWeightLevel = computed

cmp109CenteredOddBlockNormalizationLevel : ProofLevel
cmp109CenteredOddBlockNormalizationLevel = computed

physicalDyadicCornerToCMP109CenteredBlockBridgeInputsLevel : ProofLevel
physicalDyadicCornerToCMP109CenteredBlockBridgeInputsLevel = conditional

physicalNonAbelianFederbushAverageExistenceInputsLevel : ProofLevel
physicalNonAbelianFederbushAverageExistenceInputsLevel = conditional
