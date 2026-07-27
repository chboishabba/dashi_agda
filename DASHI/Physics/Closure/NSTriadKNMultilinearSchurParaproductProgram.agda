module DASHI.Physics.Closure.NSTriadKNMultilinearSchurParaproductProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
-- Uses: Theorem 1(c), three independent weights, both partial adjoints,
-- and the affine homogeneity method.
-- Relationship: the primary Stage-3 operator theorem.
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "Multilinear Calderon--Zygmund Theory".
-- Venue/year: Advances in Mathematics 165 (2002), 124--164.
-- DOI: 10.1006/aima.2001.2028.
-- Uses: formal transposes, kernel-variable permutation, and the frozen-input
-- transpose rule in equations (15)--(16).
-- Relationship: supplies exact transpose combinatorics, not the model-specific
-- Navier--Stokes derivative or cancellation estimate.
--
-- Author: Pierre Germain.
-- Title: "Multipliers, paramultipliers, and weak-strong uniqueness for the
-- Navier-Stokes equations".
-- Venue/year: Journal of Differential Equations 226 (2006), 373--428.
-- DOI: 10.1016/j.jde.2005.10.007.
-- Uses: equation (9), the three-term Pi + R + tilde-Pi decomposition, and
-- Theorem 3.9's Sobolev-indexed multiplier/paramultiplier characterization.
-- Relationship: supports the paramultiplier proof strategy and boundary-index
-- bookkeeping.  It does not supply the repository's eight orbit-shell classes.
--
-- Author: Terence Tao.
-- Title: "Lecture Notes 6 for 247B: Paradifferential calculus,
-- fractional chain and Leibnitz rules".
-- Venue/year: UCLA Math 247B Fourier Analysis lecture notes, Winter 2007.
-- DOI: none; these are course lecture notes.
-- Uses: transpose multipliers and the high-high/high-low/low-high split.
-- Relationship: supplies the shared frozen-leg frequency combinatorics only.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- Venue/year: Annales scientifiques de l'Ecole Normale Superieure,
-- Serie 4, 14 (1981), no. 2, 209--246.
-- DOI: 10.24033/asens.1404.
-- Uses: original paradifferential-calculus provenance.
-- Relationship: supplies the decomposition principle only; near/far,
-- transition and residual orbit-shell classes are repository-original.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNGrafakosTorresThreeFunctionSchurProgram as ThreeFunction
import DASHI.Physics.Closure.NSTriadKNGrafakosTorresExactTransposeSymbols as Transpose
import DASHI.Physics.Closure.NSTriadKNTaoFrozenLegParaproductProgram as Tao
import DASHI.Physics.Closure.NSTriadKNBernsteinDirectionAudit as Bernstein
import DASHI.Physics.Closure.NSTriadKNFrozenLegDerivativeLerayLedger as Derivative
import DASHI.Physics.Closure.NSTriadKNShellExponentLedgerProgram as Ledgers
import DASHI.Physics.Closure.NSTriadKNHighHighToLowCancellationProgram as HighHigh
import DASHI.Physics.Closure.NSTriadKNThreeWeightAffineCertificateProgram as Certificate

data ParaproductGeometry : Set where
  near lowHigh highLow highHighToLow farLow farHigh transition residual :
    ParaproductGeometry

record PositiveMultilinearSchurCarrier
    {a b c s : Level} : Set (lsuc (a ⊔ b ⊔ c ⊔ s)) where
  field
    LeftIndex : Set a
    RightIndex : Set b
    OutputIndex : Set c
    Scalar : Set s

    zero : Scalar
    add multiply : Scalar → Scalar → Scalar
    leq : Scalar → Scalar → Set s
    StrictlyPositive : Scalar → Set s

    triadKernelMagnitude : OutputIndex → LeftIndex → RightIndex → Scalar
    resonance : OutputIndex → LeftIndex → RightIndex → Set

    leftWeight : LeftIndex → Scalar
    rightWeight : RightIndex → Scalar
    outputWeight : OutputIndex → Scalar

    multilinearOperatorValue : OutputIndex → Scalar
    leftPartialAdjointValue : LeftIndex → Scalar
    rightPartialAdjointValue : RightIndex → Scalar

open PositiveMultilinearSchurCarrier public

record PositiveMultilinearSchurTheorem
    {a b c s : Level}
    (C : PositiveMultilinearSchurCarrier {a} {b} {c} {s}) :
    Set (lsuc (a ⊔ b ⊔ c ⊔ s)) where
  field
    leftWeightPositive : ∀ left → StrictlyPositive C (leftWeight C left)
    rightWeightPositive : ∀ right → StrictlyPositive C (rightWeight C right)
    outputWeightPositive : ∀ output → StrictlyPositive C (outputWeight C output)

    outputSchurCondition : Set s
    leftPartialAdjointSchurCondition : Set s
    rightPartialAdjointSchurCondition : Set s
    discreteTrilinearFormBound : Set s

open PositiveMultilinearSchurTheorem public

record FrozenLegParametrizedAdjointRoute
    {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff State : Set c
    Scalar : Set s

    frozenLeg : Tao.FrozenLeg
    fullTrilinearForm : Cutoff → State → State → State → Scalar
    frozenLegForm :
      Tao.FrozenLeg → Cutoff → State → State → State → Scalar

    incidencePermutationInvariant : Set s
    oneLowTwoHighClassTransportClosed : Set s
    nearTransitionResidualTransportClosed : Set s
    exactDecompositionForEveryFrozenLeg : Set s

    grafakosTorresKernelPermutationConsumed : Set s
    grafakosTorresFrozenTransposeRuleConsumed : Set s
    outputScalarSymbolIdentified : Set s
    firstTransposeScalarSymbolIdentified : Set s
    secondTransposeScalarSymbolIdentified : Set s

    outputVectorSymbolIdentified : Set s
    firstTransposeVectorSymbolIdentified : Set s
    secondTransposeVectorSymbolIdentified : Set s

    outputDerivativeOwnerIdentified : Set s
    firstAdjointDerivativeOwnerIdentified : Set s
    secondAdjointDerivativeOwnerIdentified : Set s

    outputLerayPlacementIdentified : Set s
    firstAdjointLerayPlacementIdentified : Set s
    secondAdjointLerayPlacementIdentified : Set s

    outputHolderTargetIdentified : Set s
    firstAdjointHolderTargetIdentified : Set s
    secondAdjointHolderTargetIdentified : Set s

    bernsteinDirectionsNamedAndSeparated : Set s
    outputHighHighRelocationIdentified : Set s
    firstAdjointPrimitiveLowGainRejected : Set s
    secondAdjointFrozenDerivativeIdentified : Set s

    sharedCombinatorialLedgerClosed : Set s
    outputAnalyticLedgerClosed : Set s
    firstAdjointAnalyticLedgerClosed : Set s
    secondAdjointAnalyticLedgerClosed : Set s
    allThreeLedgersCutoffUniform : Set s

open FrozenLegParametrizedAdjointRoute public

record NavierStokesParaproductDualRoute
    {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff State : Set c
    Scalar : Set s
    add : Scalar → Scalar → Scalar
    leq : Scalar → Scalar → Set s

    fullTrilinearForm : Cutoff → State → State → State → Scalar
    classTrilinearForm :
      ParaproductGeometry → Cutoff → State → State → State → Scalar

    exactClassDecomposition : Set s
    frozenLegParametrizedDecomposition : Set s
    permutationCombinatoricsClosed : Set s
    exponentLedgersRemainLegSpecific : Set s

    lowHighDualBound : Set s
    highLowDualBound : Set s
    highHighToLowRemainderBound : Set s
    nearDiagonalBound : Set s
    farLowBound : Set s
    farHighBound : Set s
    transitionBound : Set s
    residualBound : Set s

    bernsteinAnnularDirectionConsumed : Set s
    bernsteinLowPassDirectionConsumed : Set s
    bernsteinHighPassTailDirectionConsumed : Set s
    noLowPassDecayInferredFromBernsteinAlone : Set s

    outputLedgerInstantiation : Set s
    firstAdjointLedgerInstantiation : Set s
    secondAdjointLedgerInstantiation : Set s

    outputCancellationGainClosed : Set s
    firstAdjointTailOrCommutatorGainClosed : Set s
    secondAdjointDirectLowDerivativeClosed : Set s

    affineThreeWeightSystemSolved : Set s
    strictEpsilonCertificateEmitted : Set s

    multiplierRouteClosed : Set s
    paramultiplierRouteClosed : Set s
    threeFunctionSchurRouteClosed : Set s
    classwiseDualTrilinearAssembly : Set s
    cutoffUniformTrilinearBound : Set s

open NavierStokesParaproductDualRoute public

data HarmonicFrameworkLevel : Set where
  primaryThreeFunction
  frozenOutputTwoFunction
  frozenLegParametrizedParaproduct
  classwiseParaproductRealization : HarmonicFrameworkLevel

record Stage3HarmonicHierarchy : Set₁ where
  field
    primaryFramework : HarmonicFrameworkLevel
    primaryIsThreeFunction : primaryFramework ≡ primaryThreeFunction

    twoFunctionSpecializationAvailable : Set
    twoFunctionRequiresFrozenOutputLeg : Set

    frozenLegParametrizationAvailable : Set
    frozenLegReusesFrequencyCombinatorics : Set
    frozenLegDoesNotIdentifyAnalyticLedgers : Set

    outputConditionRequired : Set
    firstPartialAdjointConditionRequired : Set
    secondPartialAdjointConditionRequired : Set

    taoBonyTrichotomyAttributionCorrect : Set
    germainParamultiplierAttributionCorrect : Set
    repositoryEightClassAttributionExplicit : Set

    paraproductClassesRealizePartialAdjoints : Set
    bernsteinDirectionsAuditedBeforeAssembly : Set
    noRawRowTheoremPromotedToThreeFunctionClosure : Set

open Stage3HarmonicHierarchy public

record BaselineColumnStrategyFork : Set₁ where
  field
    threeFunctionSchurAvailable : Set
    linearTwoWeightSpecializationAvailable : Set
    frozenLegParametrizedTrichotomyAvailable : Set
    paraproductDualityAvailable : Set
    swapSymmetryAvailable : Set
    nullGainRedistributionAvailable : Set
    orbitCardinalityRenormalizationAvailable : Set

    selectedPrimaryStrategy : HarmonicFrameworkLevel
    selectionJustifiedByClasswiseEstimates : Set
    noFiniteCertificatePromotedToUniformTheorem : Set

open BaselineColumnStrategyFork public

frozenLegPermutationReceipt : Tao.FrozenLegPermutationReceipt
frozenLegPermutationReceipt = Tao.frozenLegPermutationReceipt

kernelPermutationReceipt : Transpose.KernelPermutationReceipt
kernelPermutationReceipt = Transpose.kernelPermutationReceipt

frozenOperatorTransposeReceipt : Transpose.FrozenOperatorTransposeReceipt
frozenOperatorTransposeReceipt = Transpose.frozenOperatorTransposeReceipt

frozenLegDerivativeReceipt : Derivative.FrozenLegDerivativeReceipt
frozenLegDerivativeReceipt = Derivative.frozenLegDerivativeReceipt

frozenLegGainReceipt : HighHigh.FrozenLegGainReceipt
frozenLegGainReceipt = HighHigh.frozenLegGainReceipt

attributionReceipt : Ledgers.AttributionReceipt
attributionReceipt = Ledgers.attributionReceipt

analyticReadinessReceipt : Certificate.AnalyticReadinessReceipt
analyticReadinessReceipt = Certificate.analyticReadinessReceipt

bernsteinDirectionReceipt : Bernstein.BernsteinDirectionReceipt
bernsteinDirectionReceipt = Bernstein.bernsteinDirectionReceipt

threeFunctionFrameworkSubsumesFrozenLegSchur : Bool
threeFunctionFrameworkSubsumesFrozenLegSchur =
  ThreeFunction.twoFunctionSchurRetainedAsFrozenOutputSpecialization

threeFunctionFrameworkSubsumesFrozenLegSchurIsTrue :
  threeFunctionFrameworkSubsumesFrozenLegSchur ≡ true
threeFunctionFrameworkSubsumesFrozenLegSchurIsTrue =
  ThreeFunction.twoFunctionSchurRetainedAsFrozenOutputSpecializationIsTrue

frozenLegTrichotomyRepresented : Bool
frozenLegTrichotomyRepresented = Tao.taoTransposeAndTrichotomySourceRepresented

frozenLegTrichotomyRepresentedIsTrue :
  frozenLegTrichotomyRepresented ≡ true
frozenLegTrichotomyRepresentedIsTrue =
  Tao.taoTransposeAndTrichotomySourceRepresentedIsTrue

literalScalarTransposeSymbolsClosed : Bool
literalScalarTransposeSymbolsClosed = Transpose.literalScalarTransposeSymbolsClosed

literalScalarTransposeSymbolsClosedIsTrue :
  literalScalarTransposeSymbolsClosed ≡ true
literalScalarTransposeSymbolsClosedIsTrue =
  Transpose.literalScalarTransposeSymbolsClosedIsTrue

frozenLegPermutationClosesAllAnalyticLedgers : Bool
frozenLegPermutationClosesAllAnalyticLedgers =
  Tao.permutationAloneClosesAllExponentLedgers

frozenLegPermutationClosesAllAnalyticLedgersIsFalse :
  frozenLegPermutationClosesAllAnalyticLedgers ≡ false
frozenLegPermutationClosesAllAnalyticLedgersIsFalse =
  Tao.permutationAloneClosesAllExponentLedgersIsFalse

bernsteinDirectionAuditRepresented : Bool
bernsteinDirectionAuditRepresented = Bernstein.bernsteinDirectionSurfaceRepresented

bernsteinDirectionAuditRepresentedIsTrue :
  bernsteinDirectionAuditRepresented ≡ true
bernsteinDirectionAuditRepresentedIsTrue =
  Bernstein.bernsteinDirectionSurfaceRepresentedIsTrue

germainEightClassAttributionCorrected : Bool
germainEightClassAttributionCorrected = true

germainEightClassAttributionCorrectedIsTrue :
  germainEightClassAttributionCorrected ≡ true
germainEightClassAttributionCorrectedIsTrue = refl

firstAdjointPrimitiveLowGainAvailable : Bool
firstAdjointPrimitiveLowGainAvailable =
  HighHigh.firstAdjointPrimitiveLowGainAvailable

firstAdjointPrimitiveLowGainAvailableIsFalse :
  firstAdjointPrimitiveLowGainAvailable ≡ false
firstAdjointPrimitiveLowGainAvailableIsFalse =
  HighHigh.firstAdjointPrimitiveLowGainAvailableIsFalse

multilinearAndParaproductRoutesRepresented : Bool
multilinearAndParaproductRoutesRepresented = true

multilinearAndParaproductRoutesRepresentedIsTrue :
  multilinearAndParaproductRoutesRepresented ≡ true
multilinearAndParaproductRoutesRepresentedIsTrue = refl

cutoffUniformDualTrilinearBoundClosed : Bool
cutoffUniformDualTrilinearBoundClosed = false

cutoffUniformDualTrilinearBoundClosedIsFalse :
  cutoffUniformDualTrilinearBoundClosed ≡ false
cutoffUniformDualTrilinearBoundClosedIsFalse = refl
