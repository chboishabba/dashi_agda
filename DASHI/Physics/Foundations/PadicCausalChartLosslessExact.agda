module DASHI.Physics.Foundations.PadicCausalChartLosslessExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Kernel
import DASHI.Biology.TriadicCarryResidualExact as Carry
import DASHI.Biology.CausalHierarchicalChartResidualExact as Chart
import DASHI.Biology.FinitePadicCollapseExact as Collapse
import DASHI.Biology.ConsciousAccessRound4SourceAtlas as PadicSources

------------------------------------------------------------------------
-- Finite cyclic residual chart.
--
-- This is the exact finite quotient analogue of causal residual coding.  The
-- predictor is supplied from prior data; the target is used only to construct
-- a residual.  Decoding combines the same predictor with that residual.

negateResidue : Carry.TriResidue → Carry.TriResidue
negateResidue Carry.residue0 = Carry.residue0
negateResidue Carry.residue1 = Carry.residue2
negateResidue Carry.residue2 = Carry.residue1

encodeResidual :
  Carry.TriResidue → Carry.TriResidue → Carry.TriResidue
encodeResidual predicted target =
  Carry.cyclicAdd3 (negateResidue predicted) target

decodeResidual :
  Carry.TriResidue → Carry.TriResidue → Carry.TriResidue
decodeResidual predicted residual =
  Carry.cyclicAdd3 predicted residual

decodeEncodeResidual :
  (predicted target : Carry.TriResidue) →
  decodeResidual predicted (encodeResidual predicted target) ≡ target
decodeEncodeResidual Carry.residue0 Carry.residue0 = refl
decodeEncodeResidual Carry.residue0 Carry.residue1 = refl
decodeEncodeResidual Carry.residue0 Carry.residue2 = refl
decodeEncodeResidual Carry.residue1 Carry.residue0 = refl
decodeEncodeResidual Carry.residue1 Carry.residue1 = refl
decodeEncodeResidual Carry.residue1 Carry.residue2 = refl
decodeEncodeResidual Carry.residue2 Carry.residue0 = refl
decodeEncodeResidual Carry.residue2 Carry.residue1 = refl
decodeEncodeResidual Carry.residue2 Carry.residue2 = refl

SheetResidue : Set
SheetResidue = Carry.TriResidue × Carry.TriResidue

encodeSheetResidual : SheetResidue → SheetResidue → SheetResidue
encodeSheetResidual (p₁ , p₂) (x₁ , x₂) =
  encodeResidual p₁ x₁ , encodeResidual p₂ x₂

decodeSheetResidual : SheetResidue → SheetResidue → SheetResidue
decodeSheetResidual (p₁ , p₂) (r₁ , r₂) =
  decodeResidual p₁ r₁ , decodeResidual p₂ r₂

decodeEncodeSheetResidual :
  (predicted target : SheetResidue) →
  decodeSheetResidual predicted (encodeSheetResidual predicted target)
  ≡
  target
decodeEncodeSheetResidual (p₁ , p₂) (x₁ , x₂)
  rewrite decodeEncodeResidual p₁ x₁
        | decodeEncodeResidual p₂ x₂
  = refl

------------------------------------------------------------------------
-- Support/orientation gating is exactly invertible on every trit.

foldedDigitPlaneRoundTrip :
  (trit : Kernel.KernelTrit) →
  Kernel.unfoldTrit (Kernel.foldTrit trit) ≡ trit
foldedDigitPlaneRoundTrip = Kernel.unfoldFoldTrit

------------------------------------------------------------------------
-- Abstract matched coder.  The only property used by losslessness is the
-- decoder/encoder round trip; probability modelling and rate optimality are
-- separate concerns.

record MatchedCoder (Symbol Code : Set) : Set where
  constructor matchedCoder
  field
    encode : Symbol → Code
    decode : Code → Symbol
    decodeEncode : (symbol : Symbol) → decode (encode symbol) ≡ symbol

open MatchedCoder public

identityResidueCoder : MatchedCoder Carry.TriResidue Carry.TriResidue
identityResidueCoder = matchedCoder (λ x → x) (λ x → x) (λ x → refl)

record CausalResidualPacket : Set where
  constructor causalResidualPacket
  field
    predictorValue : Carry.TriResidue
    codedResidual : Carry.TriResidue

open CausalResidualPacket public

encodePacket :
  Carry.TriResidue → Carry.TriResidue → CausalResidualPacket
encodePacket predicted target =
  causalResidualPacket
    predicted
    (encode identityResidueCoder (encodeResidual predicted target))

decodePacket : CausalResidualPacket → Carry.TriResidue
decodePacket packet =
  decodeResidual
    (predictorValue packet)
    (decode identityResidueCoder (codedResidual packet))

packetLossless :
  (predicted target : Carry.TriResidue) →
  decodePacket (encodePacket predicted target) ≡ target
packetLossless predicted target = decodeEncodeResidual predicted target

------------------------------------------------------------------------
-- Finite nested cylinders.  A depth-three address refines depth two, which in
-- turn refines depth one.  Distinct fine states may occupy one coarse cylinder.

record DepthThreeCylinder : Set where
  constructor depthThreeCylinder
  field
    digit0 : Kernel.KernelTrit
    digit1 : Kernel.KernelTrit
    digit2 : Kernel.KernelTrit

open DepthThreeCylinder public

record DepthTwoCylinder : Set where
  constructor depthTwoCylinder
  field
    prefix0 : Kernel.KernelTrit
    prefix1 : Kernel.KernelTrit

open DepthTwoCylinder public

truncateOne : DepthThreeCylinder → Kernel.KernelTrit
truncateOne cylinder = digit0 cylinder

truncateTwo : DepthThreeCylinder → DepthTwoCylinder
truncateTwo cylinder =
  depthTwoCylinder (digit0 cylinder) (digit1 cylinder)

fineCylinderA : DepthThreeCylinder
fineCylinderA =
  depthThreeCylinder
    Kernel.positiveTrit
    Kernel.zeroTrit
    Kernel.negativeTrit

fineCylinderB : DepthThreeCylinder
fineCylinderB =
  depthThreeCylinder
    Kernel.positiveTrit
    Kernel.zeroTrit
    Kernel.positiveTrit

sameDepthTwoDifferentDepthThree :
  truncateTwo fineCylinderA ≡ truncateTwo fineCylinderB
sameDepthTwoDifferentDepthThree = refl

sameDepthOneDifferentFineState :
  truncateOne fineCylinderA ≡ truncateOne fineCylinderB
sameDepthOneDifferentFineState = refl

------------------------------------------------------------------------
-- Finite chart selection.  This reuses the exact objective from the existing
-- causal hierarchical chart rather than introducing a second MDL surrogate.

selectedChart : Chart.ChartCandidate
selectedChart = Chart.refinedCandidate

selectedChartIsMinimal :
  (candidate : Chart.ChartCandidate) →
  Chart.candidateObjective selectedChart
  ≤
  Chart.candidateObjective candidate
selectedChartIsMinimal = Chart.refinedCandidateIsMinimal

collapseRetainsCoarseResidual :
  Collapse.depthZeroSupport
    (Collapse.collapseProfileAt Collapse.collapseTime3)
  ≡
  4
collapseRetainsCoarseResidual = Collapse.coarseResidualSurvivesCollapse

------------------------------------------------------------------------
-- Existing p-adic provenance is imported rather than duplicated.

existingPadicSourceCountIsEight :
  PadicSources.canonicalRound4SourceCount ≡ 8
existingPadicSourceCountIsEight =
  PadicSources.canonicalRound4SourceCountIsEight

------------------------------------------------------------------------
-- Authority boundary.

record PadicCausalChartLosslessBoundary : Set where
  constructor padicCausalChartLosslessBoundary
  field
    finiteCyclicResidualIsFullIntegerPadicSubtraction : Bool
    finiteCyclicResidualIsFullIntegerPadicSubtractionIsFalse :
      finiteCyclicResidualIsFullIntegerPadicSubtraction ≡ false

    matchedCoderRoundTripImpliesEntropyOptimality : Bool
    matchedCoderRoundTripImpliesEntropyOptimalityIsFalse :
      matchedCoderRoundTripImpliesEntropyOptimality ≡ false

    finiteNestedCylinderIsDifferentiableManifold : Bool
    finiteNestedCylinderIsDifferentiableManifoldIsFalse :
      finiteNestedCylinderIsDifferentiableManifold ≡ false

    endofunctionRuleTowerIsSearchedByTheCodec : Bool
    endofunctionRuleTowerIsSearchedByTheCodecIsFalse :
      endofunctionRuleTowerIsSearchedByTheCodec ≡ false

    finiteLosslessPacketProvesRateOptimality : Bool
    finiteLosslessPacketProvesRateOptimalityIsFalse :
      finiteLosslessPacketProvesRateOptimality ≡ false

open PadicCausalChartLosslessBoundary public

canonicalPadicCausalChartLosslessBoundary :
  PadicCausalChartLosslessBoundary
canonicalPadicCausalChartLosslessBoundary =
  padicCausalChartLosslessBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
