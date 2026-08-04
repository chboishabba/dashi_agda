module DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaPathCompositionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions
-- of Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Charles L. Fefferman.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Clay Mathematics Institute Millennium Prize Problem description, 2000.
-- DOI: not assigned to the official problem description.
--
-- PURPOSE
-- Compose every already-closed reducer on the highest-alpha route.  The
-- resulting receipts show that the 28 status-changing declarations do not
-- create 28 independent proof obligations: once the genuine physical leaves
-- are supplied, the weighted Fourier theorem, pair folds, multiplier theorem,
-- source/Schur theorem, equation-(4.2) adapter, four Section-4 bounds,
-- fractional ratio, Gronwall output, block decay, maximal-time contradiction,
-- infinite-cutoff transport and final theorem/audit packaging are derived.
--
-- No open physical proposition is manufactured here.  Each input remains an
-- explicit inhabitant of the corresponding official carrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNLuoWeightedIncrementFourierIntegrationCutsetExact as Weighted
import DASHI.Physics.Closure.NSTriadKNLuoThreePairCoefficientCutsetExact as Pairs
import DASHI.Physics.Closure.NSTriadKNLuoMultiplierReceiptAndSourceSchurCutsetExact as StageB
import DASHI.Physics.Closure.NSTriadKNLuoConcreteRadialMultiplierKernelExact as Multiplier
import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoExactFluxKernelDecompositionExact as Source
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalSourceSchurIdentificationExact as SourceSchur
import DASHI.Physics.Closure.NSTriadKNLuoEquation42PhysicalIdentityAdapterExact as Equation42
import DASHI.Physics.Closure.NSTriadKNLuoPerModeFiniteAssemblyAdapterExact as PerMode
import DASHI.Physics.Closure.NSTriadKNLuoPerModeCommutatorEvolutionExact as Evolution
import DASHI.Physics.Closure.NSTriadKNLuoSection4PhysicalBoundsAdapterExact as Section4
import DASHI.Physics.Closure.NSTriadKNLuoSection4ContinuityProofExact as Section4Proof
import DASHI.Physics.Closure.NSTriadKNLuoAnalyticFractionalPowerIdentificationExact as Fractional
import DASHI.Physics.Closure.NSTriadKNLuoFourAlignedAlphaThreeHalvesSummabilityExact as Summability
import DASHI.Physics.Closure.NSTriadKNLuoMeanValueGronwallReductionExact as Gronwall
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalBlockDecayReductionExact as Block
import DASHI.Physics.Closure.NSTriadKNLuoFiniteInfiniteRealPromotionExact as Promotion
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalAnalyticInputsBuilderExact as Builder
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalAnalyticInputsExact as Canonical
import DASHI.Physics.Closure.NSTriadKNLuoCriticalPathCompositionExact as Critical
import DASHI.Physics.Closure.NSTriadKNLuoMaximalTimeGlobalizationExact as Globalization
import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as Submission
import DASHI.Physics.Closure.NSTriadKNLuoGlobalPhysicalSolutionReductionExact as Global
import DASHI.Physics.Closure.NSTriadKNLuoSubmissionAuditReceiptExact as Audit
import DASHI.Physics.Closure.NSTriadKNLuoCompleteSubmissionCompositionExact as Final

record HighestAlphaFiniteAnalyticInputs : Setω where
  field
    weightedPrimitive :
      Weighted.WeightedIncrementFourierPrimitiveCutset

    pairCutset :
      Pairs.ThreePairCoefficientCutset

    MultiplierState MultiplierPoint : Set
    multiplierReceipts :
      StageB.OfficialMultiplierObservableReceipts
        MultiplierState MultiplierPoint

    equation42Inputs :
      Equation42.LuoEquation42PhysicalIdentityInputs

    Section4State Section4Scalar : Set
    section4Evolution :
      Evolution.LuoPerModeCommutatorEvolution
        Section4State Section4Scalar
    selectedSection4State : Section4State
    section4PhysicalInputs :
      Section4.LuoSection4PhysicalComponentInputs
        section4Evolution selectedSection4State

    fractionalPowerInputs :
      Fractional.AnalyticFractionalPowerPrimitiveInputs

    meanValueGronwallInputs :
      Gronwall.MeanValueGronwallPrimitiveInputs

    physicalBlockDecayInputs :
      Block.PhysicalBlockDecayPrimitiveInputs

    physicalLimitPromotion :
      Promotion.PhysicalLimitPromotionReceipt

open HighestAlphaFiniteAnalyticInputs public

record HighestAlphaFiniteAnalyticReceipt
    (inputs : HighestAlphaFiniteAnalyticInputs) : Setω where
  field
    weightedFourierRealization :
      Weighted.WeightedIncrementFourierRealization

    threePairFoldReceipt :
      Pairs.ThreePairWholeFoldReceipt

    officialMultiplierRealization :
      Multiplier.CanonicalLuoMultiplierRealization
        (MultiplierState inputs)
        (MultiplierPoint inputs)

    equation42FinitePhysicalInputs :
      PerMode.LuoPerModeFinitePhysicalInputs

    section4ComponentBounds :
      Section4Proof.LuoStep1ComponentBounds
        (section4Evolution inputs)
        (selectedSection4State inputs)
        (Section4.lowModeBound (section4PhysicalInputs inputs))
        (Section4.highModeBound (section4PhysicalInputs inputs))

    analyticFourShellRatioIdentification :
      Summability.AnalyticFourShellRatioIdentification

    meanValueGronwallReceipt :
      Gronwall.MeanValueGronwallReceipt

    physicalBlockDecayReceipt :
      Block.PhysicalBlockDecayReceipt

    infiniteCutoffSchurBound :
      Promotion.lessOrEqual
        (Promotion.schurBoundLimit (physicalLimitPromotion inputs))
        (Promotion.limitingLeft
          (Promotion.schurBoundLimit (physicalLimitPromotion inputs)))
        (Promotion.limitingRight
          (Promotion.schurBoundLimit (physicalLimitPromotion inputs)))

    infiniteCutoffEquation42 :
      Promotion.lessOrEqual
        (Promotion.equation42Limit (physicalLimitPromotion inputs))
        (Promotion.limitingLeft
          (Promotion.equation42Limit (physicalLimitPromotion inputs)))
        (Promotion.limitingRight
          (Promotion.equation42Limit (physicalLimitPromotion inputs)))

    infiniteCutoffFluxIdentity :
      Promotion.limitingLeft
        (Promotion.fluxIdentityLimit (physicalLimitPromotion inputs))
      ≡
      Promotion.limitingRight
        (Promotion.fluxIdentityLimit (physicalLimitPromotion inputs))

open HighestAlphaFiniteAnalyticReceipt public

highestAlphaFiniteAnalyticReceipt :
  (inputs : HighestAlphaFiniteAnalyticInputs) →
  HighestAlphaFiniteAnalyticReceipt inputs
highestAlphaFiniteAnalyticReceipt inputs = record
  { weightedFourierRealization =
      Weighted.weightedIncrementFourierRealization
        (weightedPrimitive inputs)
  ; threePairFoldReceipt =
      Pairs.threePairWholeFoldReceipt (pairCutset inputs)
  ; officialMultiplierRealization =
      StageB.officialMultiplierRealizationFromFiniteReceipts
        (multiplierReceipts inputs)
  ; equation42FinitePhysicalInputs =
      Equation42.equation42FinitePhysicalInputs
        (equation42Inputs inputs)
  ; section4ComponentBounds =
      Section4.section4ComponentBounds
        (section4PhysicalInputs inputs)
  ; analyticFourShellRatioIdentification =
      Fractional.analyticFourShellRatioIdentification
        (fractionalPowerInputs inputs)
  ; meanValueGronwallReceipt =
      Gronwall.meanValueGronwallReceipt
        (meanValueGronwallInputs inputs)
  ; physicalBlockDecayReceipt =
      Block.physicalBlockDecayReceipt
        (physicalBlockDecayInputs inputs)
  ; infiniteCutoffSchurBound =
      Promotion.physicalSchurBoundAtInfiniteCutoff
        (physicalLimitPromotion inputs)
  ; infiniteCutoffEquation42 =
      Promotion.physicalEquation42AtInfiniteCutoff
        (physicalLimitPromotion inputs)
  ; infiniteCutoffFluxIdentity =
      Promotion.physicalFluxIdentityAtInfiniteCutoff
        (physicalLimitPromotion inputs)
  }

record HighestAlphaSourceSchurInputs : Setω where
  field
    InitialDatum Solution Time Tensor : Set
    preBudgetData :
      PreBudget.OfficialLuoPreBudgetData
        InitialDatum Solution Time
    exactFluxKernel :
      Source.LuoExactFluxKernelDecomposition ⊤ Tensor ℚ
    sourceSchurLeaves :
      SourceSchur.CanonicalSourceSchurPhysicalLeaves
        preBudgetData Tensor exactFluxKernel

open HighestAlphaSourceSchurInputs public

highestAlphaPhysicalSourceSchurTheorem :
  (inputs : HighestAlphaSourceSchurInputs) →
  Source.LuoFluxKernelToWeightedSchur (exactFluxKernel inputs)
highestAlphaPhysicalSourceSchurTheorem inputs =
  StageB.canonicalWeightedSchurFromPhysicalLeaves
    (sourceSchurLeaves inputs)

record HighestAlphaCanonicalContradictionInputs : Setω where
  field
    InitialDatum Solution Time : Set
    preBudgetData :
      PreBudget.OfficialLuoPreBudgetData
        InitialDatum Solution Time
    physicalLeaves :
      Builder.CanonicalAnalyticPhysicalLeaves preBudgetData
    selectedFiniteMaximality :
      Globalization.SelectedTerminalMaximality preBudgetData

open HighestAlphaCanonicalContradictionInputs public

highestAlphaCriticalInputs :
  (inputs : HighestAlphaCanonicalContradictionInputs) →
  Critical.LuoCriticalPathInputs (preBudgetData inputs)
highestAlphaCriticalInputs inputs = record
  { physicalLeaves = physicalLeaves inputs
  }

highestAlphaCanonicalAnalyticInputs :
  (inputs : HighestAlphaCanonicalContradictionInputs) →
  Canonical.CanonicalAnalyticInputs (preBudgetData inputs)
highestAlphaCanonicalAnalyticInputs inputs =
  Critical.criticalPathCanonicalInputs
    (highestAlphaCriticalInputs inputs)

highestAlphaFiniteSelectedMaximalTimeImpossible :
  (inputs : HighestAlphaCanonicalContradictionInputs) → ⊥
highestAlphaFiniteSelectedMaximalTimeImpossible inputs =
  Critical.criticalPathContradictsSelectedFiniteMaximality
    (highestAlphaCriticalInputs inputs)
    (selectedFiniteMaximality inputs)

record HighestAlphaSubmissionInputs : Set₁ where
  field
    carrier :
      Submission.PeriodicNavierStokesSubmissionCarrier
    uniformPhysicalConstruction :
      Global.UniformGlobalPhysicalSolutionInputs carrier
    completeAudit :
      Audit.CompleteSubmissionAuditReceipt

open HighestAlphaSubmissionInputs public

highestAlphaSubmissionReadyTheorem :
  (inputs : HighestAlphaSubmissionInputs) →
  Final.SubmissionReadyPeriodicNavierStokesTheorem
    (carrier inputs)
highestAlphaSubmissionReadyTheorem inputs =
  Final.submissionReadyTheoremFromUniformPhysicalConstruction
    (carrier inputs)
    (uniformPhysicalConstruction inputs)
    (completeAudit inputs)

highestAlphaFiniteAnalyticCompositionClosed : Bool
highestAlphaFiniteAnalyticCompositionClosed = true

highestAlphaSourceSchurCompositionClosed : Bool
highestAlphaSourceSchurCompositionClosed = true

highestAlphaCanonicalContradictionCompositionClosed : Bool
highestAlphaCanonicalContradictionCompositionClosed = true

highestAlphaSubmissionCompositionClosed : Bool
highestAlphaSubmissionCompositionClosed = true

highestAlphaPhysicalLeavesInhabited : Bool
highestAlphaPhysicalLeavesInhabited = false

periodicNavierStokesGlobalRegularityProved : Bool
periodicNavierStokesGlobalRegularityProved = false

highestAlphaFiniteAnalyticCompositionClosedIsTrue :
  highestAlphaFiniteAnalyticCompositionClosed ≡ true
highestAlphaFiniteAnalyticCompositionClosedIsTrue = refl

highestAlphaSourceSchurCompositionClosedIsTrue :
  highestAlphaSourceSchurCompositionClosed ≡ true
highestAlphaSourceSchurCompositionClosedIsTrue = refl

highestAlphaCanonicalContradictionCompositionClosedIsTrue :
  highestAlphaCanonicalContradictionCompositionClosed ≡ true
highestAlphaCanonicalContradictionCompositionClosedIsTrue = refl

highestAlphaSubmissionCompositionClosedIsTrue :
  highestAlphaSubmissionCompositionClosed ≡ true
highestAlphaSubmissionCompositionClosedIsTrue = refl

highestAlphaPhysicalLeavesInhabitedIsFalse :
  highestAlphaPhysicalLeavesInhabited ≡ false
highestAlphaPhysicalLeavesInhabitedIsFalse = refl
