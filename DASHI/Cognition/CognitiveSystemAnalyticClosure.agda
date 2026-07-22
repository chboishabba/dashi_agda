module DASHI.Cognition.CognitiveSystemAnalyticClosure where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_)
open import Data.Vec using (Vec)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.AnesthesiaLanguagePhaseControl
import DASHI.Cognition.AnesthesiaLanguagePhaseDynamics as Dynamics
import DASHI.Cognition.BaselineMarginModelSelection as Baseline
import DASHI.Cognition.CognitiveObservableDistributions
import DASHI.Cognition.CognitiveProjectionCategory as Category
import DASHI.Cognition.CognitiveVacuumClassBoundary as Vacuum
import DASHI.Cognition.DashiCognitiveSystem as Cognitive
import DASHI.Cognition.KepplerFiniteResonanceMDL as Keppler
import DASHI.Cognition.KepplerGlutamateZPFMDLTest
import DASHI.Cognition.ResidualPhaseEmpiricalContact
import DASHI.Cognition.ResidualPhaseGeometry
import DASHI.Cognition.TernaryDerivationAddress as Address
import DASHI.Cognition.TernaryDerivationUltrametric as TritMetric
import DASHI.Cognition.VisualCompressionAttractors
import DASHI.Cognition.VisualPatternGeneratorMDL as Visual
import DASHI.Combinatorics.PDA_MDL.KernelSelection
import DASHI.Combinatorics.PDA_MDL.PDA
import DASHI.Core.ProjectionCategory as PC
import Ultrametric as U

record CognitiveAnalyticClosure : Set₁ where
  field
    ternaryUltrametric :
      ∀ {n} → U.Ultrametric (Vec BT.Trit n)

    cognitionCategory : PC.ProjectionCategory

    threeDigitAddressClosed :
      Address.encode3 (BT.neg ∷ BT.zero ∷ BT.pos ∷ []) ≡ 21

    cubicControlKinkClosed :
      Dynamics.marginAt Dynamics.canonicalKinkDynamics 1 0 0
      ≡ Cognitive.positiveMargin 13

    cuspBoundaryClosed : Dynamics.CuspBoundary 3 2

    scalarControlFixtureRejectsExtraCoupling :
      Baseline.couplingImprovesMDL 3 Baseline.scalarDataset ≡ false

    coupledFixtureSelectsExtraCoupling :
      Baseline.couplingImprovesMDL 3 Baseline.coupledDataset ≡ true

    inBandResonanceClosed :
      Keppler.resonanceScore
        Keppler.canonicalGlutamateSpectrum
        Keppler.canonicalInBandField
      ≡ 15

    offBandControlClosed :
      Keppler.resonanceScore
        Keppler.canonicalGlutamateSpectrum
        Keppler.canonicalOffBandField
      ≡ 0

    geometricCompressionClosed :
      Visual.visualMDL Visual.lattice 0
      ≤ Visual.visualMDL Visual.semanticScene 0

    stableClassNeedNotBeVacuum :
      Vacuum.VacuumClass
        Vacuum.booleanCognitiveSystem
        Vacuum.booleanDefectModel
        false
      → ⊥

canonicalCognitiveAnalyticClosure : CognitiveAnalyticClosure
canonicalCognitiveAnalyticClosure = record
  { ternaryUltrametric = TritMetric.TritUltrametric
  ; cognitionCategory = Category.cognitiveProjectionCategory
  ; threeDigitAddressClosed = Address.negativeZeroPositiveAddress
  ; cubicControlKinkClosed = Dynamics.marginInitiallyRises
  ; cuspBoundaryClosed = Dynamics.canonicalCuspBoundary
  ; scalarControlFixtureRejectsExtraCoupling =
      Baseline.extraCouplingDoesNotImproveScalarDataset
  ; coupledFixtureSelectsExtraCoupling =
      Baseline.couplingWinsThisFiniteDataset
  ; inBandResonanceClosed = Keppler.inBandScoreIsFifteen
  ; offBandControlClosed = Keppler.offBandScoreIsZero
  ; geometricCompressionClosed = Visual.latticeIsCheaperThanSemanticBinding
  ; stableClassNeedNotBeVacuum = Vacuum.falseStableClassIsNotVacuum
  }
