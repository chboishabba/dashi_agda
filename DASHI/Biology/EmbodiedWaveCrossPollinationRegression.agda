module DASHI.Biology.EmbodiedWaveCrossPollinationRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.SymmetryResolvedEmbodiedWaveControlExact as Sym
import DASHI.Biology.TranslationInvariantCompletionAccessibilityNonfactorabilityExact as Completion
import DASHI.Biology.EmbodiedWaveCubieHolonomyExact as Hol
import DASHI.Biology.TwoBoundarySymmetryResolvedModeSectionExact as TwoMode
import DASHI.Biology.BodyIndexedHarmonicWreathActionExact as Wreath
import DASHI.Biology.IntrospectiveSymmetryResolvedHyperformalismExact as CV

record EmbodiedWaveCrossPollinationRegression : Set where
  field
    translatedRawModePreservesFineCoordinate :
      (mode : Sym.SymmetryResolvedMode) →
      Sym.fineFrequency (Sym.translateFirstMode mode) ≡ Sym.fineFrequency mode

    sourceLikeRawSymmetryCanSplitEmbodiedReach :
      (mode : Sym.SymmetryResolvedMode) →
      Sym.geometry mode ≡ Sym.sourceSinkGeometry →
      Sym.modeIncidence Sym.Reach.regulatedContext mode
      ≡ Sym.modeIncidence Sym.Reach.mobilisedContext (Sym.translateFirstMode mode) → ⊥

    completionReadoutCannotDecodeAccessibility :
      Completion.NF.FactorsThrough
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
  ; completionReadoutCannotDecodeAccessibility = Completion.completionSurfaceCannotDecodeAccessibility
  ; embodiedWaveOrderDoesNotCommute = Hol.orderedEndpointsDiffer
  ; sameBoundariesDoNotFixModeGeometry = TwoMode.sameBoundariesDifferentIntermediateGeometry
  ; bodyShiftAndDeployComputeDoNotCommute = Wreath.bodyAndDeployDoNotCommute
  ; cvRecoveredSourceVsRotationalDifference = CV.recoveredGeometryDiffers
  ; cvRecoveredGateDifference = CV.recoveredGateDiffers
  }
