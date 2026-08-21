module DASHI.Biology.EmbodiedWaveCrossPollinationRegression where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.ObserverRelativeReachableSubfabricExact as Reach
import DASHI.Biology.SymmetryResolvedEmbodiedWaveControlExact as Sym
import DASHI.Biology.QuaternionOrbitEmbodiedReachNonfactorabilityExact as QReach
import DASHI.Biology.TranslationInvariantCompletionAccessibilityNonfactorabilityExact as Completion
import DASHI.Biology.EmbodiedWaveCubieHolonomyExact as Hol
import DASHI.Biology.TwoBoundarySymmetryResolvedModeSectionExact as TwoMode
import DASHI.Biology.BodyIndexedHarmonicWreathActionExact as Wreath
import DASHI.Biology.IntrospectiveSymmetryResolvedHyperformalismExact as CV
import DASHI.Mathematics.Topology.QuaternionHopfUnitOrbitExact as Hopf

record EmbodiedWaveCrossPollinationRegression : Set where
  field
    translatedRawModePreservesFineCoordinate :
      (mode : Sym.SymmetryResolvedMode) →
      Sym.fineFrequency (Sym.translateFirstMode mode) ≡ Sym.fineFrequency mode

    sourceLikeRawSymmetryCanSplitEmbodiedReach :
      (coarse : Torus.Torus3x3) (fine : Harmonic.FineFrequency) →
      Sym.modeIncidence Reach.regulatedContext (Sym.sourceModeAt coarse fine)
      ≡ Sym.modeIncidence Reach.mobilisedContext
          (Sym.translateFirstMode (Sym.sourceModeAt coarse fine)) → ⊥

    quaternionOrbitInvariantStillCannotDecodeEmbodiedReach :
      (unit : Hopf.UnitQuaternion) (pair : Hopf.QuaternionPair) →
      NF.FactorsThrough QReach.hopfSurface QReach.embodiedReach → ⊥

    completionReadoutCannotDecodeAccessibility :
      NF.FactorsThrough
        Completion.completionProjection Completion.embodiedAccessibility → ⊥

    embodiedWaveOrderDoesNotCommute :
      Hol.waveThenBody ≡ Hol.bodyThenWave → ⊥

    sameBoundariesDoNotFixModeGeometry :
      TwoMode.geometry TwoMode.sourceRoute
      ≡ TwoMode.geometry TwoMode.rotationalRoute → ⊥

    bodyShiftAndDeployComputeDoNotCommute :
      Wreath.bodyThenDeploy ≡ Wreath.deployThenBody → ⊥

    cvRecoveredSourceVsRotationalDifference :
      CV.geometry CV.sourceObservation ≡ CV.geometry CV.rotationalObservation → ⊥

    cvRecoveredGateDifference :
      CV.gate CV.sourceObservation ≡ CV.gate CV.rotationalObservation → ⊥

open EmbodiedWaveCrossPollinationRegression public

canonicalEmbodiedWaveCrossPollinationRegression : EmbodiedWaveCrossPollinationRegression
canonicalEmbodiedWaveCrossPollinationRegression = record
  { translatedRawModePreservesFineCoordinate = Sym.fineFrequencyPreservedByTranslation
  ; sourceLikeRawSymmetryCanSplitEmbodiedReach = Sym.sameRawSymmetryCanSplitEmbodiedReach
  ; quaternionOrbitInvariantStillCannotDecodeEmbodiedReach = QReach.hopfInvariantCannotDecodeEmbodiedReach
  ; completionReadoutCannotDecodeAccessibility = Completion.completionSurfaceCannotDecodeAccessibility
  ; embodiedWaveOrderDoesNotCommute = Hol.orderedEndpointsDiffer
  ; sameBoundariesDoNotFixModeGeometry = TwoMode.sameBoundariesDifferentIntermediateGeometry
  ; bodyShiftAndDeployComputeDoNotCommute = Wreath.bodyAndDeployDoNotCommute
  ; cvRecoveredSourceVsRotationalDifference = CV.recoveredGeometryDiffers
  ; cvRecoveredGateDifference = CV.recoveredGateDiffers
  }
