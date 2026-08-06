module DASHI.Biology.MorphogeneticVisualGenerator where

open import DASHI.Core.Prelude

import DASHI.Biology.Morphogenesis.ReactionDiffusionModeSelection as RD
import DASHI.Biology.Morphogenesis.LocalToGlobalControlBridge as LocalGlobal
import DASHI.Biology.Morphogenesis.MorphologicalGoalQuotient as Goal

------------------------------------------------------------------------
-- Coupled morphogenetic visual generator.
--
-- The generator separates chemical prepattern, directed transport,
-- inhibitory site selection, geometrically bounded growth, and domain update.
-- This is a finite constructive abstraction of a causal stack, not a claim
-- that cortex literally runs plant-development chemistry.
--
-- Source-facing references:
-- Alan M. Turing, "The Chemical Basis of Morphogenesis",
-- DOI 10.1098/rstb.1952.0012.
-- Richard S. Smith et al., "A plausible model of phyllotaxis",
-- DOI 10.1073/pnas.0510457103.
-- Adam Runions, Brendan Lane, and Przemyslaw Prusinkiewicz,
-- "Modeling Trees with a Space Colonization Algorithm",
-- DOI 10.2312/NPH/NPH07/063-070.
-- T. A. Witten and L. M. Sander,
-- "Diffusion-Limited Aggregation, a Kinetic Critical Phenomenon",
-- DOI 10.1103/PhysRevLett.47.1400.

data ChemicalFieldState : Set where
  homogeneousField : ChemicalFieldState
  squareModeField : ChemicalFieldState
  branchingModeField : ChemicalFieldState

data SelectedMode : Set where
  noSelectedMode : SelectedMode
  squareSelectedMode : SelectedMode
  branchingSelectedMode : SelectedMode

data ModeSymmetry : Set where
  isotropicSymmetry : ModeSymmetry
  orthogonalSymmetry : ModeSymmetry
  branchingSymmetry : ModeSymmetry

data ModeWavelength : Set where
  noWavelength : ModeWavelength
  macroWavelength : ModeWavelength
  fineWavelength : ModeWavelength

data ChemicalParameter : Set where
  stableParameter : ChemicalParameter
  anisotropicParameter : ChemicalParameter
  branchingParameter : ChemicalParameter

evolveChemical :
  ChemicalParameter → ChemicalFieldState → ChemicalFieldState
evolveChemical stableParameter s = s
evolveChemical anisotropicParameter homogeneousField = squareModeField
evolveChemical anisotropicParameter squareModeField = squareModeField
evolveChemical anisotropicParameter branchingModeField = branchingModeField
evolveChemical branchingParameter homogeneousField = branchingModeField
evolveChemical branchingParameter squareModeField = branchingModeField
evolveChemical branchingParameter branchingModeField = branchingModeField

modeOfChemical : ChemicalFieldState → SelectedMode
modeOfChemical homogeneousField = noSelectedMode
modeOfChemical squareModeField = squareSelectedMode
modeOfChemical branchingModeField = branchingSelectedMode

wavelengthOfMode : SelectedMode → ModeWavelength
wavelengthOfMode noSelectedMode = noWavelength
wavelengthOfMode squareSelectedMode = macroWavelength
wavelengthOfMode branchingSelectedMode = fineWavelength

data LocalExcitationWitness : ChemicalParameter → Set where
  anisotropicExcitation : LocalExcitationWitness anisotropicParameter
  branchingExcitation : LocalExcitationWitness branchingParameter

data LateralInhibitionWitness : ChemicalParameter → Set where
  anisotropicInhibition : LateralInhibitionWitness anisotropicParameter
  branchingInhibition : LateralInhibitionWitness branchingParameter

data FiniteModeWitness : ChemicalParameter → SelectedMode → Set where
  squareFiniteMode :
    FiniteModeWitness anisotropicParameter squareSelectedMode
  branchingFiniteMode :
    FiniteModeWitness branchingParameter branchingSelectedMode

data SymmetryAllowedWitness : ModeSymmetry → SelectedMode → Set where
  squareOrthogonalAllowed :
    SymmetryAllowedWitness orthogonalSymmetry squareSelectedMode
  branchingAllowed :
    SymmetryAllowedWitness branchingSymmetry branchingSelectedMode

data StationaryPatternWitness : ChemicalParameter → SelectedMode → Set where
  squareStationary :
    StationaryPatternWitness anisotropicParameter squareSelectedMode
  branchingStationary :
    StationaryPatternWitness branchingParameter branchingSelectedMode

finiteReactionDiffusionSystem : RD.ReactionDiffusionModeSystem
finiteReactionDiffusionSystem =
  record
    { FieldState = ChemicalFieldState
    ; Mode = SelectedMode
    ; Symmetry = ModeSymmetry
    ; Wavelength = ModeWavelength
    ; Parameter = ChemicalParameter
    ; evolve = evolveChemical
    ; modeOf = modeOfChemical
    ; wavelength = wavelengthOfMode
    ; LocalExcitation = LocalExcitationWitness
    ; LateralInhibition = LateralInhibitionWitness
    ; FiniteWavelengthUnstable = FiniteModeWitness
    ; SymmetryAllowed = SymmetryAllowedWitness
    ; StationaryPattern = StationaryPatternWitness
    }

squareModeSelectionWitness :
  RD.TuringModeSelectionWitness finiteReactionDiffusionSystem
squareModeSelectionWitness =
  record
    { parameter = anisotropicParameter
    ; mode = squareSelectedMode
    ; symmetry = orthogonalSymmetry
    ; excitation = anisotropicExcitation
    ; inhibition = anisotropicInhibition
    ; finiteMode = squareFiniteMode
    ; allowed = squareOrthogonalAllowed
    ; stationary = squareStationary
    }

------------------------------------------------------------------------
-- Candidate growth laws and their exact finite signatures.

data GrowthLaw : Set where
  squareLatticeLaw : GrowthLaw
  tangencyLaw : GrowthLaw
  phyllotacticLaw : GrowthLaw
  reactionDiffusionLaw : GrowthLaw
  hybridMorphogeneticLaw : GrowthLaw

curvedTriangularGaps : GrowthLaw → Bool
curvedTriangularGaps squareLatticeLaw = false
curvedTriangularGaps tangencyLaw = true
curvedTriangularGaps phyllotacticLaw = false
curvedTriangularGaps reactionDiffusionLaw = false
curvedTriangularGaps hybridMorphogeneticLaw = true

branchingCurvedPassages : GrowthLaw → Bool
branchingCurvedPassages squareLatticeLaw = false
branchingCurvedPassages tangencyLaw = true
branchingCurvedPassages phyllotacticLaw = true
branchingCurvedPassages reactionDiffusionLaw = true
branchingCurvedPassages hybridMorphogeneticLaw = true

globalPeriodicity : GrowthLaw → Bool
globalPeriodicity squareLatticeLaw = true
globalPeriodicity tangencyLaw = false
globalPeriodicity phyllotacticLaw = false
globalPeriodicity reactionDiffusionLaw = true
globalPeriodicity hybridMorphogeneticLaw = true

localRuleRegularity : GrowthLaw → Bool
localRuleRegularity squareLatticeLaw = true
localRuleRegularity tangencyLaw = true
localRuleRegularity phyllotacticLaw = true
localRuleRegularity reactionDiffusionLaw = true
localRuleRegularity hybridMorphogeneticLaw = true

molecularTransportRelevant : GrowthLaw → Bool
molecularTransportRelevant squareLatticeLaw = false
molecularTransportRelevant tangencyLaw = false
molecularTransportRelevant phyllotacticLaw = true
molecularTransportRelevant reactionDiffusionLaw = true
molecularTransportRelevant hybridMorphogeneticLaw = true

hybridCarriesSquareAndCurvedSignatures :
  globalPeriodicity hybridMorphogeneticLaw ≡ true
  ×
  curvedTriangularGaps hybridMorphogeneticLaw ≡ true
hybridCarriesSquareAndCurvedSignatures = refl , refl

hybridCarriesBiologicalAndBranchingSignatures :
  molecularTransportRelevant hybridMorphogeneticLaw ≡ true
  ×
  branchingCurvedPassages hybridMorphogeneticLaw ≡ true
hybridCarriesBiologicalAndBranchingSignatures = refl , refl

------------------------------------------------------------------------
-- A finite state-update stack.

record MorphogeneticState : Set where
  constructor morphogeneticState
  field
    residualMaterial : Nat
    activatorLevel : Nat
    inhibitorLevel : Nat
    resourceLevel : Nat
    cavityCount : Nat

open MorphogeneticState public

chemicalPrepattern : MorphogeneticState → MorphogeneticState
chemicalPrepattern (morphogeneticState r a i e c) =
  morphogeneticState r (suc a) i e c

directedTransport : MorphogeneticState → MorphogeneticState
directedTransport (morphogeneticState r a i e c) =
  morphogeneticState r a (suc i) e c

competitiveSelection : MorphogeneticState → MorphogeneticState
competitiveSelection (morphogeneticState r a i e c) =
  morphogeneticState r a i (e ∸ i) c

boundedGrowth : MorphogeneticState → MorphogeneticState
boundedGrowth (morphogeneticState r a i e c) =
  morphogeneticState (r ∸ e) a i e (suc c)

morphogeneticStep : MorphogeneticState → MorphogeneticState
morphogeneticStep s =
  boundedGrowth
    (competitiveSelection
      (directedTransport
        (chemicalPrepattern s)))

initialMorphogeneticState : MorphogeneticState
initialMorphogeneticState =
  morphogeneticState 10 0 0 3 0

firstMorphogeneticState : MorphogeneticState
firstMorphogeneticState =
  morphogeneticStep initialMorphogeneticState

firstStepResidualMaterialIsEight :
  residualMaterial firstMorphogeneticState ≡ 8
firstStepResidualMaterialIsEight = refl

firstStepCreatesOneCavity :
  cavityCount firstMorphogeneticState ≡ 1
firstStepCreatesOneCavity = refl

firstStepChangesChemicalState :
  activatorLevel firstMorphogeneticState ≡ 1
  ×
  inhibitorLevel firstMorphogeneticState ≡ 1
firstStepChangesChemicalState = refl , refl

------------------------------------------------------------------------
-- Shared morphology class does not imply mechanism identity.

data MechanismCarrier : Set where
  neuralFieldCarrier : MechanismCarrier
  biologicalMorphogenCarrier : MechanismCarrier
  shaderGeometryCarrier : MechanismCarrier

data MorphologicalClass : Set where
  excitationInhibitionClass : MorphologicalClass
  recursivePackingClass : MorphologicalClass

classOfMechanism : MechanismCarrier → MorphologicalClass
classOfMechanism neuralFieldCarrier = excitationInhibitionClass
classOfMechanism biologicalMorphogenCarrier = excitationInhibitionClass
classOfMechanism shaderGeometryCarrier = recursivePackingClass

neuralAndBiologicalShareMorphologicalClass :
  classOfMechanism neuralFieldCarrier
  ≡
  classOfMechanism biologicalMorphogenCarrier
neuralAndBiologicalShareMorphologicalClass = refl

neuralAndBiologicalMechanismsRemainDistinct :
  neuralFieldCarrier ≡ biologicalMorphogenCarrier → ⊥
neuralAndBiologicalMechanismsRemainDistinct ()

------------------------------------------------------------------------
-- Existing repository authority boundaries are consumed directly.

canonicalLocalGlobalAuthorityBoundary :
  LocalGlobal.LocalGlobalAuthorityBoundary
canonicalLocalGlobalAuthorityBoundary =
  record
    { noSingleMasterCode = ⊤
    ; localCompetenceIsNotGlobalOmniscience = ⊤
    ; globalPatternIsNotCentralControllerByDefinition = ⊤
    ; modelControllabilityIsNotEmpiricalRegeneration = ⊤
    }

canonicalMorphologicalGoalAuthorityBoundary :
  Goal.MorphologicalGoalAuthorityBoundary
canonicalMorphologicalGoalAuthorityBoundary =
  record
    { goalIsNotFutureCause = ⊤
    ; quotientIsNotSemanticRepresentationByDefinition = ⊤
    ; anatomicalAttractorIsNotConsciousness = ⊤
    ; repairGoalIsNotUniversalTeleology = ⊤
    }

noSingleMasterCodeWitness :
  LocalGlobal.LocalGlobalAuthorityBoundary.noSingleMasterCode
    canonicalLocalGlobalAuthorityBoundary
noSingleMasterCodeWitness = tt

goalIsNotFutureCauseWitness :
  Goal.MorphologicalGoalAuthorityBoundary.goalIsNotFutureCause
    canonicalMorphologicalGoalAuthorityBoundary
goalIsNotFutureCauseWitness = tt

record MorphogeneticVisualBoundary : Set₁ where
  constructor morphogeneticVisualBoundary
  field
    visualSimilarityImpliesMechanismIdentity : Bool
    visualSimilarityImpliesMechanismIdentityIsFalse :
      visualSimilarityImpliesMechanismIdentity ≡ false

    chemicalModelIsLiteralNeuralMechanism : Bool
    chemicalModelIsLiteralNeuralMechanismIsFalse :
      chemicalModelIsLiteralNeuralMechanism ≡ false

    oneGrowthLawExplainsAllNaturalGeometry : Bool
    oneGrowthLawExplainsAllNaturalGeometryIsFalse :
      oneGrowthLawExplainsAllNaturalGeometry ≡ false

    localGlobalAuthorityBoundary :
      LocalGlobal.LocalGlobalAuthorityBoundary

    morphologicalGoalAuthorityBoundary :
      Goal.MorphologicalGoalAuthorityBoundary

open MorphogeneticVisualBoundary public

canonicalMorphogeneticVisualBoundary : MorphogeneticVisualBoundary
canonicalMorphogeneticVisualBoundary =
  morphogeneticVisualBoundary
    false refl
    false refl
    false refl
    canonicalLocalGlobalAuthorityBoundary
    canonicalMorphologicalGoalAuthorityBoundary
