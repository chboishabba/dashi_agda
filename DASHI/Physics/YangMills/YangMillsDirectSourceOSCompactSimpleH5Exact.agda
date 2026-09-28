{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsDirectSourceOSCompactSimpleH5Exact where

------------------------------------------------------------------------
-- H5 SOURCE-FIRST: EVERY COMPACT SIMPLE G GETS THE SAME H1/H2/H3 PACKAGE.
--
-- Classification/package lookup is already compiler-owned.  The physical H5
-- theorem is one parametric continuation from QuantitativeCompactLiePackage G
-- to the actual direct-source construction used by the mass-gap proof.
--
-- To prevent a parallel group universe, this owner also carries an exact
-- roundtrip between the repository's classified CompactSimpleLieGroup and the
-- literal endpoint CompactSimpleGroup carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.CompactSimpleQuantitativeCoverage as Compact
import DASHI.Physics.YangMills.YangMillsCompactSimpleParametricPromotionReductionExact as Groups
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSameHGapExact as H1H3
import DASHI.Physics.YangMills.YangMillsDirectSourceOSSelectedWilsonH2Exact as H2
import DASHI.Physics.YangMills.YangMillsDirectSourceOSRationalContinuumH2Exact as H2Continuum
import DASHI.Physics.YangMills.YangMillsDirectSourceOSReconstructedSpectrumH3Exact as H3

record LiteralGroupDirectSourcePackage
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (continuum : H2Continuum.RationalLiteralContinuumSameObjectBridge Y)
    (G : Top.CompactSimpleGroup C)
    : Set₂ where
  field
    h1h3 :
      H1H3.LiteralGroupDirectSourceSameHGap Y G

    h2SelectedWilson :
      H2.LiteralSelectedWilsonExpectationApplication h1h3

    h3SameOS :
      H3.LiteralSelectedSpectrumIsSameOSHamiltonian continuum h1h3

    --------------------------------------------------------------------
    -- Finite literal YM semantics on the SAME Y finite family.
    --------------------------------------------------------------------
    finiteVolumeCutoffMeasure :
      ∀ cutoff →
      Top.IsFiniteVolumeCutoffMeasure S G cutoff
        (Top.finiteMeasure Y G cutoff)

    reflectionPositiveRegularization :
      ∀ cutoff →
      Top.IsReflectionPositiveRegularization S G cutoff
        (Top.finiteMeasure Y G cutoff)

    ultravioletYangMillsNormalization :
      Top.HasUltravioletYangMillsNormalization S G
        (Top.finiteMeasure Y G)

    asymptoticallyFreeScaleTrajectory :
      Top.HasAsymptoticallyFreeScaleTrajectory S G
        (Top.finiteMeasure Y G)

    gaugeSymmetryPreserved :
      Top.GaugeSymmetryPreservedAlongConstruction S G

    localityPreserved :
      Top.LocalityPreservedAlongConstruction S G

    euclideanCovariancePreserved :
      Top.EuclideanCovariancePreservedAlongConstruction S G

    reflectionPositivityPreserved :
      Top.ReflectionPositivityPreservedAlongConstruction S G

    positivityNormalizationPreserved :
      Top.PositivityNormalizationPreservedAlongConstruction S G

    volumeCutoffCompatibility :
      Top.VolumeCutoffCompatibilityPreserved S G

open LiteralGroupDirectSourcePackage public

record LiteralCompactSimpleDirectSourceContinuation
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    : Set₂ where
  field
    LieElement GroupElement : Set

    authority :
      Compact.CompactSimpleQuantitativeAuthority
        ℚ LieElement GroupElement

    classifiedToLiteral :
      Compact.CompactSimpleLieGroup →
      Top.CompactSimpleGroup C

    literalToClassified :
      Top.CompactSimpleGroup C →
      Compact.CompactSimpleLieGroup

    classifiedLiteralRoundtrip :
      ∀ G →
      classifiedToLiteral (literalToClassified G) ≡ G

    continuum :
      H2Continuum.RationalLiteralContinuumSameObjectBridge Y

    compactSimple :
      ∀ G → Top.IsCompactSimple S G

    fourDimensionalEuclidean :
      Top.IsFourDimensionalEuclidean S (Top.spacetime Y)

    compactSimpleParameterization :
      Top.CompactSimpleParameterizationPreserved S

    continueLiteralDirectSource :
      (G : Compact.CompactSimpleLieGroup) →
      Compact.QuantitativeCompactLiePackage
        ℚ LieElement GroupElement G →
      LiteralGroupDirectSourcePackage
        Y continuum (classifiedToLiteral G)

open LiteralCompactSimpleDirectSourceContinuation public


structuralBaseFromCompactSimpleContinuation :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  LiteralCompactSimpleDirectSourceContinuation Y →
  Five.LiteralClayStructuralBase Y
structuralBaseFromCompactSimpleContinuation source = record
  { Five.LiteralClayStructuralBase.compactSimple =
      compactSimple source
  ; Five.LiteralClayStructuralBase.fourDimensionalEuclidean =
      fourDimensionalEuclidean source
  ; Five.LiteralClayStructuralBase.compactSimpleParameterization =
      compactSimpleParameterization source
  }

asParametricContinuation :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  (source : LiteralCompactSimpleDirectSourceContinuation Y) →
  Groups.CompactSimpleParametricYMContinuation
    ℚ (LieElement source) (GroupElement source)
asParametricContinuation {Y = Y} source = record
  { Groups.CompactSimpleParametricYMContinuation.authority =
      authority source
  ; Groups.CompactSimpleParametricYMContinuation.PhysicalConstruction =
      λ G →
        LiteralGroupDirectSourcePackage
          Y (continuum source) (classifiedToLiteral source G)
  ; Groups.CompactSimpleParametricYMContinuation.continueFromQuantitativePackage =
      continueLiteralDirectSource source
  }

classifiedConstruction :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : LiteralCompactSimpleDirectSourceContinuation Y)
    G →
  LiteralGroupDirectSourcePackage
    Y (continuum source) (classifiedToLiteral source G)
classifiedConstruction source G =
  Groups.allCompactSimpleConstruction
    (asParametricContinuation source) G

constructionForEveryLiteralCompactSimpleGroup :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : LiteralCompactSimpleDirectSourceContinuation Y)
    G →
  LiteralGroupDirectSourcePackage Y (continuum source) G
constructionForEveryLiteralCompactSimpleGroup {Y = Y} source G =
  subst
    (LiteralGroupDirectSourcePackage Y (continuum source))
    (classifiedLiteralRoundtrip source G)
    (classifiedConstruction source (literalToClassified source G))


finiteRGForEveryLiteralGroup :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  LiteralCompactSimpleDirectSourceContinuation Y →
  Five.LiteralWeakCouplingRGConstruction Y
finiteRGForEveryLiteralGroup source = record
  { Five.LiteralWeakCouplingRGConstruction.finiteVolumeCutoffMeasure =
      λ G cutoff →
        finiteVolumeCutoffMeasure
          (constructionForEveryLiteralCompactSimpleGroup source G)
          cutoff
  ; Five.LiteralWeakCouplingRGConstruction.reflectionPositiveRegularization =
      λ G cutoff →
        reflectionPositiveRegularization
          (constructionForEveryLiteralCompactSimpleGroup source G)
          cutoff
  ; Five.LiteralWeakCouplingRGConstruction.ultravioletYangMillsNormalization =
      λ G →
        ultravioletYangMillsNormalization
          (constructionForEveryLiteralCompactSimpleGroup source G)
  ; Five.LiteralWeakCouplingRGConstruction.asymptoticallyFreeScaleTrajectory =
      λ G →
        asymptoticallyFreeScaleTrajectory
          (constructionForEveryLiteralCompactSimpleGroup source G)
  ; Five.LiteralWeakCouplingRGConstruction.gaugeSymmetryPreserved =
      λ G →
        gaugeSymmetryPreserved
          (constructionForEveryLiteralCompactSimpleGroup source G)
  ; Five.LiteralWeakCouplingRGConstruction.localityPreserved =
      λ G →
        localityPreserved
          (constructionForEveryLiteralCompactSimpleGroup source G)
  ; Five.LiteralWeakCouplingRGConstruction.euclideanCovariancePreserved =
      λ G →
        euclideanCovariancePreserved
          (constructionForEveryLiteralCompactSimpleGroup source G)
  ; Five.LiteralWeakCouplingRGConstruction.reflectionPositivityPreserved =
      λ G →
        reflectionPositivityPreserved
          (constructionForEveryLiteralCompactSimpleGroup source G)
  ; Five.LiteralWeakCouplingRGConstruction.positivityNormalizationPreserved =
      λ G →
        positivityNormalizationPreserved
          (constructionForEveryLiteralCompactSimpleGroup source G)
  ; Five.LiteralWeakCouplingRGConstruction.volumeCutoffCompatibility =
      λ G →
        volumeCutoffCompatibility
          (constructionForEveryLiteralCompactSimpleGroup source G)
  }

sameHGapForEveryLiteralGroup :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  LiteralCompactSimpleDirectSourceContinuation Y →
  H1H3.LiteralDirectSourceSameHMassGap Y
sameHGapForEveryLiteralGroup source = record
  { H1H3.LiteralDirectSourceSameHMassGap.forGroup =
      λ G →
        h1h3
          (constructionForEveryLiteralCompactSimpleGroup source G)
  }

h2ForEveryLiteralGroup :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : LiteralCompactSimpleDirectSourceContinuation Y)
    G →
  H2.LiteralSelectedWilsonExpectationApplication
    (H1H3.forGroup (sameHGapForEveryLiteralGroup source) G)
h2ForEveryLiteralGroup source G =
  h2SelectedWilson
    (constructionForEveryLiteralCompactSimpleGroup source G)

h3ForEveryLiteralGroup :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    (source : LiteralCompactSimpleDirectSourceContinuation Y)
    G →
  H3.LiteralSelectedSpectrumIsSameOSHamiltonian
    (continuum source)
    (H1H3.forGroup (sameHGapForEveryLiteralGroup source) G)
h3ForEveryLiteralGroup source G =
  h3SameOS
    (constructionForEveryLiteralCompactSimpleGroup source G)

directH5ClassificationCompilerLevel : ProofLevel
directH5ClassificationCompilerLevel =
  Groups.compactSimpleClassificationToParametricFamilyLevel

-- The single remaining H5 physical theorem is continueLiteralDirectSource:
-- construct the literal selected-background/CMP116/continuum/spectral package
-- from QuantitativeCompactLiePackage G for arbitrary classified G.
directH5PhysicalParametricContinuationLevel : ProofLevel
directH5PhysicalParametricContinuationLevel = conditional
