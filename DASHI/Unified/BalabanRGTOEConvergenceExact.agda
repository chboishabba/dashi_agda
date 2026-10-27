{-# OPTIONS --safe #-}
module DASHI.Unified.BalabanRGTOEConvergenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Unifier as U
import DASHI.Physics.YangMills.BalabanSection2InductivePackage as Section2
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToYM4RegionExact as Region
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as Measure
import DASHI.Physics.YangMills.BalabanFunctionalRegularESourceFlowRound242Exact as RegularE
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Localization
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Marked
import DASHI.Physics.YangMills.BalabanIrrelevantRGMemoryContractionExact as Memory
import DASHI.Physics.YangMills.BalabanCompactSimpleHaarQuadraticCasimirExact as Casimir
import DASHI.Physics.YangMills.BalabanStressShellEnergyToHilbertRound112Exact as Stress
import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as MassGap
import DASHI.Physics.Closure.ContinuumClayMassGapReceiptObligation as Continuum

------------------------------------------------------------------------
-- Normalized TOE-facing ZKP frame.
--
-- This module only joins existing theorem owners.
-- It does not replace their source authority.
-- It does not promote a finite RG or finite-depth result to a continuum theorem.
------------------------------------------------------------------------

balabanRGTOEZKPFrame : U.ZKPConvergenceFrame
balabanRGTOEZKPFrame =
  U.zkpConvergenceFrame
    "Converge the existing Bałaban RG density, localization, Casimir, and stress results into the DASHI TOE import graph."
    "Duplicate owners, same-object drift, and finite-to-continuum promotion can make the aggregate unsound."
    "Reuse canonical source and compiler owners. Keep conditional physical seams explicit. Keep continuum and Clay promotion false."
    "The branch owns complete-density, regular-E, CMP116 localization, marked-shell, irrelevant-memory, Casimir, stress-shell, finite-measure, and continuum-boundary surfaces."
    "Source theorem authority < same-object physical identification < machine-checked compiler < continuum or external promotion."
    "Import and normalize existing owners. Do not reconstruct their mathematics in this module."
    "The TOE root and Unified physics graph expose one fail-closed Bałaban RG convergence surface."
    "The remaining gap is the explicit conditional same-object and continuum construction work already recorded by the imported owners."
    ( "Literal CMP119 functional regular-E source realization is required for the preferred source path."
    ∷ "CMP116 differentiated localization authority is imported, but selected physical mark identification and uniform radii remain explicit conditions."
    ∷ "Literal stress coefficient shell identification remains a physical same-object condition."
    ∷ "Literal Bałaban Haar-coordinate normalization remains a physical same-object condition."
    ∷ [] )
    ( "All scale-indexed density and localization facts retain their original owner and source attribution."
    ∷ "Beta-history, spatial-Hessian, and composite/OPE marks remain distinct."
    ∷ "Finite-depth gap receipts never imply a continuum Clay theorem."
    ∷ "Conditional ProofLevel values do not self-promote."
    ∷ [] )
    ( "The complete-density to YM4-region assembly remains machine checked."
    ∷ "The regular-E representation compiler remains machine checked."
    ∷ "The stress shell-to-Hilbert compiler remains machine checked."
    ∷ "The classified Haar quadratic Casimir coefficient remains machine checked."
    ∷ "Continuum and terminal Clay promotion remain false."
    ∷ [] )

------------------------------------------------------------------------
-- Existing proof levels, normalized without duplication.
------------------------------------------------------------------------

completeDensityToYM4RegionCompiler : ProofLevel
completeDensityToYM4RegionCompiler =
  Region.balabanCompleteDensityToYM4RegionAssemblyLevel

literalFiniteMeasureCompiler : ProofLevel
literalFiniteMeasureCompiler =
  Measure.balabanDensityLiteralFiniteMeasureCompilerLevel

functionalRegularECompiler : ProofLevel
functionalRegularECompiler =
  RegularE.functionalRegularESourceFlowCompilerLevel

functionalRegularESourceLeaf : ProofLevel
functionalRegularESourceLeaf =
  RegularE.literalFunctionalCMP119PublishedFlowLevel

cmp116DifferentiatedLocalizationAuthority : ProofLevel
cmp116DifferentiatedLocalizationAuthority =
  Localization.cmp116DifferentiatedLocalizationAuthorityLevel

cmp116PhysicalMarkedCoordinateLeaf : ProofLevel
cmp116PhysicalMarkedCoordinateLeaf =
  Localization.physicalCMP116MarkedCoordinateAndUniformRadiusIdentificationLevel

sharedMarkedAnalyticCompiler : ProofLevel
sharedMarkedAnalyticCompiler =
  Marked.sharedMarkedAnalyticThreeConsumerCompilerLevel

sharedMarkedVanishingTailCompiler : ProofLevel
sharedMarkedVanishingTailCompiler =
  Marked.sharedMarkedAnalyticVanishingTailCompilerLevel

irrelevantRGMemoryCompiler : ProofLevel
irrelevantRGMemoryCompiler =
  Memory.irrelevantRGMemoryContractionCompilerLevel

stressShellCompiler : ProofLevel
stressShellCompiler =
  Stress.stressShellEnergyToHilbertCompilerLevel

stressLiteralInstantiationLeaf : ProofLevel
stressLiteralInstantiationLeaf =
  Stress.literalStressCMP116ActivityEntropyInstantiationLevel

haarCasimirCompiler : ProofLevel
haarCasimirCompiler =
  Casimir.classifiedHaarQuadraticCoefficientLevel

haarLiteralNormalizationLeaf : ProofLevel
haarLiteralNormalizationLeaf =
  Casimir.physicalBalabanHaarCoordinateNormalizationLevel

------------------------------------------------------------------------
-- Exact promotion boundaries.
------------------------------------------------------------------------

functionalRegularESourceLeafDoesNotSelfPromote :
  promotable functionalRegularESourceLeaf ≡ false
functionalRegularESourceLeafDoesNotSelfPromote = refl

cmp116PhysicalMarkedCoordinateLeafDoesNotSelfPromote :
  promotable cmp116PhysicalMarkedCoordinateLeaf ≡ false
cmp116PhysicalMarkedCoordinateLeafDoesNotSelfPromote = refl

stressLiteralInstantiationLeafDoesNotSelfPromote :
  promotable stressLiteralInstantiationLeaf ≡ false
stressLiteralInstantiationLeafDoesNotSelfPromote = refl

haarLiteralNormalizationLeafDoesNotSelfPromote :
  promotable haarLiteralNormalizationLeaf ≡ false
haarLiteralNormalizationLeafDoesNotSelfPromote = refl

finiteDepthGapDoesNotPromoteContinuum :
  Continuum.finiteDepthCarrierSpectralGapPromotesContinuum
    Continuum.canonicalFiniteDepthVsContinuumClayAuthorityBoundary
  ≡ false
finiteDepthGapDoesNotPromoteContinuum =
  Continuum.finiteDepthCarrierSpectralGapPromotesContinuumIsFalse
    Continuum.canonicalFiniteDepthVsContinuumClayAuthorityBoundary

terminalClayPromotionRemainsFalse :
  Continuum.terminalPromotion
    Continuum.canonicalFiniteDepthVsContinuumClayAuthorityBoundary
  ≡ false
terminalClayPromotionRemainsFalse =
  Continuum.terminalPromotionIsFalse
    Continuum.canonicalFiniteDepthVsContinuumClayAuthorityBoundary

rgProObjectContinuumLimitRemainsUnpromoted :
  MassGap.continuumLimitPromoted
    MassGap.canonicalFiniteDepthLatticeGapProObjectReceipt
  ≡ false
rgProObjectContinuumLimitRemainsUnpromoted =
  MassGap.continuumLimitPromotedIsFalse
    MassGap.canonicalFiniteDepthLatticeGapProObjectReceipt

------------------------------------------------------------------------
-- TOE aggregate surface.
------------------------------------------------------------------------

record BalabanRGTOEConvergenceSurface : Set where
  constructor balaban-rg-toe-convergence-surface
  field
    frame : U.ZKPConvergenceFrame
    densityRegionLevel : ProofLevel
    finiteMeasureLevel : ProofLevel
    regularELevel : ProofLevel
    localizationAuthorityLevel : ProofLevel
    markedShellCompilerLevel : ProofLevel
    markedTailCompilerLevel : ProofLevel
    irrelevantMemoryLevel : ProofLevel
    stressLevel : ProofLevel
    casimirLevel : ProofLevel
    continuumPromotion : Bool
    continuumPromotionIsFalse : continuumPromotion ≡ false
    terminalPromotion : Bool
    terminalPromotionIsFalse : terminalPromotion ≡ false

open BalabanRGTOEConvergenceSurface public

canonicalBalabanRGTOEConvergenceSurface :
  BalabanRGTOEConvergenceSurface
canonicalBalabanRGTOEConvergenceSurface =
  balaban-rg-toe-convergence-surface
    balabanRGTOEZKPFrame
    completeDensityToYM4RegionCompiler
    literalFiniteMeasureCompiler
    functionalRegularECompiler
    cmp116DifferentiatedLocalizationAuthority
    sharedMarkedAnalyticCompiler
    sharedMarkedVanishingTailCompiler
    irrelevantRGMemoryCompiler
    stressShellCompiler
    haarCasimirCompiler
    (Continuum.finiteDepthCarrierSpectralGapPromotesContinuum
      Continuum.canonicalFiniteDepthVsContinuumClayAuthorityBoundary)
    finiteDepthGapDoesNotPromoteContinuum
    (Continuum.terminalPromotion
      Continuum.canonicalFiniteDepthVsContinuumClayAuthorityBoundary)
    terminalClayPromotionRemainsFalse
