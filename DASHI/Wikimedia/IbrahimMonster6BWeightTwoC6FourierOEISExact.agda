module DASHI.Wikimedia.IbrahimMonster6BWeightTwoC6FourierOEISExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.Monster3BBalancedRegularFibreExact as ThreeB
import DASHI.Wikimedia.IbrahimMonster3BOEIS6BPowerNormalizationBridgeExact as SixB
import DASHI.Wikimedia.IbrahimMonster236BMcKayThompsonNormalizationInvariantOEISExact as Normalization
import DASHI.Wikimedia.IbrahimMonster6BCompleteReplicabilityPowerSnowballExact as Replicability

------------------------------------------------------------------------
-- MONSTER 6B WEIGHT-TWO C6 FOURIER SPECTRUM
--
-- This is a theorem-bearing use of OEIS that remains source-bounded:
--
--   * normalized 6B McKay--Thompson: Tr(g | V^natural_2)   = 78,
--   * ATLAS power map:                g^2 is class 3B,
--   * existing 3B weight-two owner:  Tr(g^2 | V^natural_2) = 54,
--   * ATLAS power map:                g^3 is class 2B,
--   * normalized 2B McKay--Thompson: Tr(g^3 | V^natural_2) = 276,
--   * dim V^natural_2 = 196884.
--
-- The McKay--Thompson traces are real, hence inverse powers have equal traces:
-- Tr(g^5)=78 and Tr(g^4)=54.  Finite C6 Fourier inversion then determines
-- the six eigenspace multiplicities.
--
-- Two upstream refinements are now retained explicitly:
--
--   * normalization invariance: q^1 traces 78/54/276 survive the documented
--     OEIS q^0 normalization variants for 6B/3B/2B;
--   * complete replicability: the whole normalized 6B series has power-map
--     replicate targets 3B and 2B at the class-function level.
--
-- Neither refinement creates a literal selected VOA action or the separate
-- N(3B) multiplicity-space 12+78 decomposition.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Source graph.
------------------------------------------------------------------------

oeisA007246 : Attribution.AttributedSource
oeisA007246 = Attribution.mkNoDOISource
  "N. J. A. Sloane; OEIS contributors"
  "A007246: McKay-Thompson series of class 2B for the Monster group"
  "On-Line Encyclopedia of Integer Sequences"
  "retrieved 2026-09-15"
  "https://oeis.org/A007246"
  (Attribution.namedSourceKind "integer-sequence database record")
  "normalized 2B McKay-Thompson coefficient provenance; the q coefficient 276 is used only through the Conway-Norton graded-trace interpretation"
  Attribution.publicAttribution

oeisA007246Attribution = Snowball.canonicalSourceRoleSnowballReceipt oeisA007246

conwayNortonSource = SixB.conwayNorton
atlasMonsterSource = SixB.atlasMonster
oeisA007255Source = SixB.oeisA007255

normalizationInvariantTraceBoundary : Normalization.NormalizationInvariantOEISFrontier
normalizationInvariantTraceBoundary = Normalization.currentNormalizationInvariantOEISFrontier

replicabilityPowerBoundary : Replicability.Monster6BReplicabilityFrontier
replicabilityPowerBoundary = Replicability.currentMonster6BReplicabilityFrontier

------------------------------------------------------------------------
-- 2. Weight-two trace vector.
------------------------------------------------------------------------

weightTwoDimension : Nat
weightTwoDimension = 196884

sixBTraceWeightTwo : Nat
sixBTraceWeightTwo = 78

threeBTraceWeightTwo : Nat
threeBTraceWeightTwo = 54

twoBTraceWeightTwo : Nat
twoBTraceWeightTwo = 276

threeBTraceMatchesExistingOwner : ThreeB.monster3BConformalTrace ≡ threeBTraceWeightTwo
threeBTraceMatchesExistingOwner = ThreeB.monster3BConformalTraceIs54

record C6WeightTwoTraceVector : Set where
  constructor c6-weight-two-trace-vector
  field
    traceG0 : Nat
    traceG1 : Nat
    traceG2 : Nat
    traceG3 : Nat
    traceG4 : Nat
    traceG5 : Nat
    sixBSquareClass : String
    sixBCubeClass : String
    inverseTraceSymmetryPaid : Bool
    sameMoonshineWeightTwoGradingPaid : Bool
open C6WeightTwoTraceVector public

traceVector19688478542765478 : C6WeightTwoTraceVector
traceVector19688478542765478 = c6-weight-two-trace-vector
  196884 78 54 276 54 78
  "3B" "2B"
  true true

------------------------------------------------------------------------
-- 3. Integer Fourier solution.
--
-- Let m_j be the multiplicity of exp(2*pi*i*j/6), j=0,...,5.
-- Reality gives m1=m5 and m2=m4.  Instead of importing complex arithmetic,
-- the exact inverse-DFT solution is certified by the resulting integer linear
-- equations.  All equations are subtraction-free Nat equalities.
------------------------------------------------------------------------

record C6WeightTwoMultiplicitySpectrum : Set where
  constructor c6-weight-two-multiplicity-spectrum
  field
    m0 : Nat
    m1 : Nat
    m2 : Nat
    m3 : Nat
    m4 : Nat
    m5 : Nat
    conjugatePair15 : m1 ≡ m5
    conjugatePair24 : m2 ≡ m4
    dimensionEquation : m0 + m1 + m2 + m3 + m4 + m5 ≡ 196884
    sixBTraceEquation : m0 + m1 ≡ 78 + m2 + m3
    threeBTraceEquation : m0 + m3 ≡ 54 + m1 + m2
    twoBTraceEquation : m0 + 2 * m2 ≡ 276 + 2 * m1 + m3
open C6WeightTwoMultiplicitySpectrum public

canonicalC6WeightTwoMultiplicitySpectrum : C6WeightTwoMultiplicitySpectrum
canonicalC6WeightTwoMultiplicitySpectrum = c6-weight-two-multiplicity-spectrum
  32904 32772 32838 32760 32838 32772
  refl refl refl refl refl refl

c6WeightTwoMultiplicityTuple : String
c6WeightTwoMultiplicityTuple = "(32904,32772,32838,32760,32838,32772)"

------------------------------------------------------------------------
-- 4. Role boundary against the N(3B) 12+78 lane.
------------------------------------------------------------------------

record C6VsN3BRoleBoundary : Set where
  constructor c6-vs-n3b-role-boundary
  field
    sixBSpectrumLivesOnMoonshineWeightTwo : Bool
    n3BSplitLivesOnNormalizerMultiplicitySpace : Bool
    sharedSeventyEightInteger : Bool
    sameCarrierPaid : Bool
    sameActionPaid : Bool
    sameCharacterDecompositionPaid : Bool
    intertwinerPaid : Bool
open C6VsN3BRoleBoundary public

canonicalC6VsN3BRoleBoundary : C6VsN3BRoleBoundary
canonicalC6VsN3BRoleBoundary = c6-vs-n3b-role-boundary
  true true true false false false false

------------------------------------------------------------------------
-- 5. WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data C6SpectrumCreatesN3BMultiplicityWeld : Set where
data Shared32772CreatesRepresentationIdentity : Set where
data SharedSeventyEightCreatesMultiplicityCharacter : Set where
data OEISTraceCreatesLiteralMonsterMatrix : Set where
data ClassPowerCreatesSubspaceIntertwiner : Set where

data ReplicabilityCreatesLiteralSpectralProjectors : Set where

c6SpectrumDoesNotCreateN3BMultiplicityWeld :
  C6SpectrumCreatesN3BMultiplicityWeld → ⊥
c6SpectrumDoesNotCreateN3BMultiplicityWeld ()

shared32772DoesNotIdentifyRepresentation :
  Shared32772CreatesRepresentationIdentity → ⊥
shared32772DoesNotIdentifyRepresentation ()

sharedSeventyEightDoesNotCreateMultiplicityCharacter :
  SharedSeventyEightCreatesMultiplicityCharacter → ⊥
sharedSeventyEightDoesNotCreateMultiplicityCharacter ()

oeisTraceDoesNotCreateLiteralMatrix : OEISTraceCreatesLiteralMonsterMatrix → ⊥
oeisTraceDoesNotCreateLiteralMatrix ()

classPowerDoesNotCreateIntertwiner : ClassPowerCreatesSubspaceIntertwiner → ⊥
classPowerDoesNotCreateIntertwiner ()

replicabilityDoesNotCreateLiteralProjectors :
  ReplicabilityCreatesLiteralSpectralProjectors → ⊥
replicabilityDoesNotCreateLiteralProjectors ()

------------------------------------------------------------------------
-- 6. Pareto frontier.
------------------------------------------------------------------------

record WeightTwoC6FourierFrontier : Set where
  constructor weight-two-c6-fourier-frontier
  field
    sixBNormalizedTrace78Paid : Bool
    sixBSquareTo3BPaid : Bool
    threeBTrace54Paid : Bool
    sixBCubeTo2BPaid : Bool
    twoBNormalizedTrace276Paid : Bool
    normalizationInvariantTraceExtractionPaid : Bool
    wholeSeriesReplicabilityPowerRelationPaid : Bool
    inverseTraceSymmetryPaid : Bool
    weightTwoDimension196884Paid : Bool
    c6FourierIntegerSpectrumPaid : Bool
    literalSixBMatrixPaid : Bool
    n3BMultiplicityWeldPaid : Bool
    nextResidual : String
open WeightTwoC6FourierFrontier public

weightTwoC6FourierFrontier : WeightTwoC6FourierFrontier
weightTwoC6FourierFrontier = weight-two-c6-fourier-frontier
  true true true true true true true true true true false false
  "the class-function/graded-trace data determine the C6 weight-two spectrum (32904,32772,32838,32760,32838,32772), and complete replicability supplies the whole normalized-series power relation behind 6B -> 3B / 2B rather than isolated coefficient matching. Keep both as independent source-paid receipts. The next action-level payment is a literal selected 6B endomorphism on the same V^natural_2 carrier, with its square/cube identified to the selected 3B/2B actions and spectral projectors realizing these eigenspaces. Do not use q^0 normalization constants, shared 78, or replicability alone to identify the separate N(3B) 12+78 multiplicity representation."

sixBPowerNormalizationFrontier : SixB.OEIS6BPowerNormalizationFrontier
sixBPowerNormalizationFrontier = SixB.oeis6BPowerNormalizationFrontier
