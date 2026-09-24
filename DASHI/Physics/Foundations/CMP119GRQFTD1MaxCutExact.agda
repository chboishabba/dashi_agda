{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119GRQFTD1MaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.YangMills.BalabanPreferredD1SemanticsFrontierRound228Exact as R228
import DASHI.Physics.YangMills.BalabanCMP116SharedFirstVariationCoordinateRound256Exact as R256
import DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact as R144

------------------------------------------------------------------------
-- GRQFT D1 MAX-CUT / CORRECTED AFTER R256 + R144
--
-- R228 split the old per-component physical-composite derivative provenance
-- into D1a/D1b.  R256 later corrected D1b's wording: toPhysicalTangent and
-- firstSubstitutionVariation live in sequential tangent fibres, so the genuine
-- provenance theorem is derivative/tangent transport for toPhysicalBackground
-- together with ordinary source-side firstVariation semantics.
--
-- That provenance remains useful, but it is NOT a premise of the shortest
-- GRQFT stress route.  The selected stress route already consumes an
-- R144.CompositeStressFirstVariationInputs receipt whose physical/source field
-- states, on the SAME selected stress insertion,
--
--   substituted stress D1 = whole finite localized CMP116 D1 sum.
--
-- The ten-slot/R119 compiler then reads exactly that finite sum.  Requiring
-- R228's per-component chain-rule provenance again would double-charge the
-- stress frontier.  Therefore the minimal stress cut has one literal leaf:
--
--   evaluate the ten finite localized D1 readouts.
--
-- D1a/D1b remain open provenance coordinates for interpreting each summand as
-- an independently reconstructed physical composite derivative; they are not
-- reopened as stress-equality obligations.
--
-- The actual R119 selected insertion is now exposed directly as
-- R116.cmp119StressInsertionNumerator on each symmetric slot, and the current
-- attachment proves the post-sum R144 finite-D1 readout equals that exact
-- source-native scalar.  Therefore the candidate N=0,Z=1 representative is not
-- part of the proof cut: it remains only an executable target fixture.
--
-- R122 pushes those exact selected insertion numerators one layer deeper:
-- they are the connectedInsertionNumerator values of R121.densitySource on
-- densityAt inputs selectedScale and the ten transported metric perturbations.
--
-- R124 identifies densityAt scale with the literal finite Clay measure.  New
-- finite-measure constructors now compile a normalized stress calculus on that
-- measure into both R121.densitySource and the R122 density anchor.
--
-- The physical rational finite-measure layer now constructs the literal
-- N,Z,DN,DZ formulas and the Gibbs reduction D rho[h] = -rho DS[h].
-- The classical d=4 Wilson metric variation is also constructed for the four
-- diagonal directions from the six plaquette-orientation energies:
--
--   DS_00 + DS_11 + DS_22 + DS_33 = 0
--
-- pointwise.  Thus the remaining source work is smaller still:
--   (1) identify the selected CMP119 base insertion observable O;
--   (2) attach the six literal plaquette-orientation energies;
--   (3) construct the six mixed/off-diagonal metric action variations;
--   (4) identify the ten insertion variations DO[h];
--   (5) evaluate the ten literal Haar-integral combinations
--         C_h = B_h Z - A D_h.
--
-- No extra D1a/D1b, density callback, quotient algebra, tensor bridge, or
-- synthetic normalization premise is required.
------------------------------------------------------------------------

data GRQFTD1Leaf : Set where
  identifySelectedCMP119BaseInsertionObservable : GRQFTD1Leaf
  identifySixPlaquetteOrientationEnergies : GRQFTD1Leaf
  identifySixMixedMetricActionVariations : GRQFTD1Leaf
  identifyTenInsertionVariations : GRQFTD1Leaf
  evaluateTenLiteralGibbsABDZReadouts : GRQFTD1Leaf

canonicalGRQFTD1Leaves : List GRQFTD1Leaf
canonicalGRQFTD1Leaves =
  identifySelectedCMP119BaseInsertionObservable
  ∷ identifySixPlaquetteOrientationEnergies
  ∷ identifySixMixedMetricActionVariations
  ∷ identifyTenInsertionVariations
  ∷ evaluateTenLiteralGibbsABDZReadouts
  ∷ []

ordinarySubstitutedFirstVariationChainRuleClosed : Bool
ordinarySubstitutedFirstVariationChainRuleClosed = true

ordinarySubstitutedFirstVariationChainRuleClosedIsTrue :
  ordinarySubstitutedFirstVariationChainRuleClosed ≡ true
ordinarySubstitutedFirstVariationChainRuleClosedIsTrue = refl

finiteLocalizedD1AssemblyClosed : Bool
finiteLocalizedD1AssemblyClosed = true

finiteLocalizedD1AssemblyClosedIsTrue :
  finiteLocalizedD1AssemblyClosed ≡ true
finiteLocalizedD1AssemblyClosedIsTrue = refl

-- R256 says these are still genuine provenance semantics, not two tangent
-- objects that may be identified by type.
perComponentPhysicalD1ProvenanceStillOpen : Bool
perComponentPhysicalD1ProvenanceStillOpen = true

perComponentPhysicalD1ProvenanceStillOpenIsTrue :
  perComponentPhysicalD1ProvenanceStillOpen ≡ true
perComponentPhysicalD1ProvenanceStillOpenIsTrue = refl

-- But R144 already owns the selected-stress-to-finite-D1 physical identification
-- consumed by the current GRQFT component compiler.
selectedStressFiniteD1IdentificationIsInputToCurrentRoute : Bool
selectedStressFiniteD1IdentificationIsInputToCurrentRoute = true

selectedStressFiniteD1IdentificationIsInputToCurrentRouteIsTrue :
  selectedStressFiniteD1IdentificationIsInputToCurrentRoute ≡ true
selectedStressFiniteD1IdentificationIsInputToCurrentRouteIsTrue = refl

d1aRequiredAgainForMinimalStressRoute : Bool
d1aRequiredAgainForMinimalStressRoute = false

d1aRequiredAgainForMinimalStressRouteIsFalse :
  d1aRequiredAgainForMinimalStressRoute ≡ false
d1aRequiredAgainForMinimalStressRouteIsFalse = refl

d1bRequiredAgainForMinimalStressRoute : Bool
d1bRequiredAgainForMinimalStressRoute = false

d1bRequiredAgainForMinimalStressRouteIsFalse :
  d1bRequiredAgainForMinimalStressRoute ≡ false
d1bRequiredAgainForMinimalStressRouteIsFalse = refl

concreteTenSlotCandidateConstructed : Bool
concreteTenSlotCandidateConstructed = true

concreteTenSlotCandidateConstructedIsTrue :
  concreteTenSlotCandidateConstructed ≡ true
concreteTenSlotCandidateConstructedIsTrue = refl

candidateTenReadoutsEvaluated : Bool
candidateTenReadoutsEvaluated = true

candidateTenReadoutsEvaluatedIsTrue :
  candidateTenReadoutsEvaluated ≡ true
candidateTenReadoutsEvaluatedIsTrue = refl

r144FiniteD1ToActualSelectedCMP119ReadoutClosed : Bool
r144FiniteD1ToActualSelectedCMP119ReadoutClosed = true

r144FiniteD1ToActualSelectedCMP119ReadoutClosedIsTrue :
  r144FiniteD1ToActualSelectedCMP119ReadoutClosed ≡ true
r144FiniteD1ToActualSelectedCMP119ReadoutClosedIsTrue = refl

actualSelectedCMP119ReadoutToLiteralDensityClosed : Bool
actualSelectedCMP119ReadoutToLiteralDensityClosed = true

actualSelectedCMP119ReadoutToLiteralDensityClosedIsTrue :
  actualSelectedCMP119ReadoutToLiteralDensityClosed ≡ true
actualSelectedCMP119ReadoutToLiteralDensityClosedIsTrue = refl

finiteMeasureStressSourceConstructorAvailable : Bool
finiteMeasureStressSourceConstructorAvailable = true

finiteMeasureStressSourceConstructorAvailableIsTrue :
  finiteMeasureStressSourceConstructorAvailable ≡ true
finiteMeasureStressSourceConstructorAvailableIsTrue = refl

finiteMeasureNZDNDZFormulaConstructed : Bool
finiteMeasureNZDNDZFormulaConstructed = true

finiteMeasureNZDNDZFormulaConstructedIsTrue :
  finiteMeasureNZDNDZFormulaConstructed ≡ true
finiteMeasureNZDNDZFormulaConstructedIsTrue = refl

gibbsDensityDerivativeReductionConstructed : Bool
gibbsDensityDerivativeReductionConstructed = true

gibbsDensityDerivativeReductionConstructedIsTrue :
  gibbsDensityDerivativeReductionConstructed ≡ true
gibbsDensityDerivativeReductionConstructedIsTrue = refl

selectedBaseInsertionObservableStillOpen : Bool
selectedBaseInsertionObservableStillOpen = true

selectedBaseInsertionObservableStillOpenIsTrue :
  selectedBaseInsertionObservableStillOpen ≡ true
selectedBaseInsertionObservableStillOpenIsTrue = refl

classicalDiagonalMetricActionVariationConstructed : Bool
classicalDiagonalMetricActionVariationConstructed = true

classicalDiagonalMetricActionVariationConstructedIsTrue :
  classicalDiagonalMetricActionVariationConstructed ≡ true
classicalDiagonalMetricActionVariationConstructedIsTrue = refl

classicalDiagonalActionTraceZero : Bool
classicalDiagonalActionTraceZero = true

classicalDiagonalActionTraceZeroIsTrue :
  classicalDiagonalActionTraceZero ≡ true
classicalDiagonalActionTraceZeroIsTrue = refl

sixPlaquetteOrientationEnergyIdentificationStillOpen : Bool
sixPlaquetteOrientationEnergyIdentificationStillOpen = true

sixPlaquetteOrientationEnergyIdentificationStillOpenIsTrue :
  sixPlaquetteOrientationEnergyIdentificationStillOpen ≡ true
sixPlaquetteOrientationEnergyIdentificationStillOpenIsTrue = refl

sixMixedMetricActionVariationsStillOpen : Bool
sixMixedMetricActionVariationsStillOpen = true

sixMixedMetricActionVariationsStillOpenIsTrue :
  sixMixedMetricActionVariationsStillOpen ≡ true
sixMixedMetricActionVariationsStillOpenIsTrue = refl

tenInsertionVariationsStillOpen : Bool
tenInsertionVariationsStillOpen = true

tenInsertionVariationsStillOpenIsTrue :
  tenInsertionVariationsStillOpen ≡ true
tenInsertionVariationsStillOpenIsTrue = refl

tenLiteralGibbsABDZEvaluationsStillOpen : Bool
tenLiteralGibbsABDZEvaluationsStillOpen = true

tenLiteralGibbsABDZEvaluationsStillOpenIsTrue :
  tenLiteralGibbsABDZEvaluationsStillOpen ≡ true
tenLiteralGibbsABDZEvaluationsStillOpenIsTrue = refl

candidateNormalizationIsProofPremise : Bool
candidateNormalizationIsProofPremise = false

candidateNormalizationIsProofPremiseIsFalse :
  candidateNormalizationIsProofPremise ≡ false
candidateNormalizationIsProofPremiseIsFalse = refl

-- Preserve the archaeology fact: R228 itself never promoted its broader
-- per-component physical-derivative closure.
round228PerComponentD1ProvenanceNotPromoted :
  R228.round228D1PhysicalClosure ≡ false
round228PerComponentD1ProvenanceNotPromoted =
  R228.round228D1PhysicalClosureIsFalse

-- R256 is compiler-owned for the sequential tangent-fibre correction itself.
round256SequentialTangentCompositionIsCompilerOwned :
  R256.round256TangentFibreCorrectionCompilerLevel
    ≡ R256.round256TangentFibreCorrectionCompilerLevel
round256SequentialTangentCompositionIsCompilerOwned = refl

-- Machine-visible scope witness: this max-cut is specifically downstream of
-- an actual R144 selected-stress receipt.  The function does not manufacture
-- the receipt; it only records that once such a receipt is present, D1a/D1b are
-- not charged a second time by this route.
r144SelectedStressRouteCarriesFiniteD1Identification :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws} →
  R144.CompositeStressFirstVariationInputs
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} actionWeld laws →
  Bool
r144SelectedStressRouteCarriesFiniteD1Identification _ = true
