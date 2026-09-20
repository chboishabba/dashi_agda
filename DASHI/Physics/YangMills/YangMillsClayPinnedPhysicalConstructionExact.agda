module DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact where

------------------------------------------------------------------------
-- PINNED PHYSICAL YANG--MILLS CONSTRUCTION
--
-- Choose the actual finite, continuum, OS/Hamiltonian, mass-gap and local-QFT
-- objects first.  The literal Clay construction is compiled FROM those objects.
--
-- Same-object relationships are therefore definitional wherever possible:
--
--   finite family -> continuum measure -> Schwinger family -> H/Hamiltonian
--        \                                               /
--         \-> local fields/OPE/stress         physical gap + SI attachment
--
-- SI is an attachment to the proved physical inverse correlation length/gap;
-- it is never used to manufacture clustering.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact as T78
import DASHI.Physics.YangMills.YangMillsSIScalingEndpointExact as SI

------------------------------------------------------------------------
-- Finite physical family.
--
-- The literal finite-measure family is THIS object.  There is no later
-- densityToFiniteMeasure equality in the canonical route.
------------------------------------------------------------------------

record PinnedFiniteYMConstruction
    {C : Top.LiteralYangMillsCarriers}
    (S : Top.LiteralYangMillsSemantics C) : Set₁ where
  field
    finiteMeasure :
      Top.CompactSimpleGroup C → Top.Cutoff C → Top.FiniteMeasure C

    finiteVolumeCutoffMeasure : ∀ G cutoff →
      Top.IsFiniteVolumeCutoffMeasure S G cutoff
        (finiteMeasure G cutoff)

    reflectionPositiveRegularization : ∀ G cutoff →
      Top.IsReflectionPositiveRegularization S G cutoff
        (finiteMeasure G cutoff)

    ultravioletYangMillsNormalization : ∀ G →
      Top.HasUltravioletYangMillsNormalization S G (finiteMeasure G)

    asymptoticallyFreeScaleTrajectory : ∀ G →
      Top.HasAsymptoticallyFreeScaleTrajectory S G (finiteMeasure G)

    gaugeSymmetryPreserved : ∀ G →
      Top.GaugeSymmetryPreservedAlongConstruction S G

    localityPreserved : ∀ G →
      Top.LocalityPreservedAlongConstruction S G

    euclideanCovariancePreserved : ∀ G →
      Top.EuclideanCovariancePreservedAlongConstruction S G

    reflectionPositivityPreserved : ∀ G →
      Top.ReflectionPositivityPreservedAlongConstruction S G

    positivityNormalizationPreserved : ∀ G →
      Top.PositivityNormalizationPreservedAlongConstruction S G

    volumeCutoffCompatibility : ∀ G →
      Top.VolumeCutoffCompatibilityPreserved S G

open PinnedFiniteYMConstruction public

------------------------------------------------------------------------
-- Continuum measure / Schwinger / SAME OS reconstruction.
------------------------------------------------------------------------

record PinnedContinuumYMConstruction
    {C : Top.LiteralYangMillsCarriers}
    (S : Top.LiteralYangMillsSemantics C)
    (finite : PinnedFiniteYMConstruction S) : Set₁ where
  field
    continuumMeasure :
      Top.CompactSimpleGroup C → Top.ContinuumMeasure C

    schwinger :
      Top.CompactSimpleGroup C → Top.SchwingerFamily C

    hilbertSpace :
      Top.CompactSimpleGroup C → Top.HilbertSpace C

    hamiltonian :
      Top.CompactSimpleGroup C → Top.Hamiltonian C

    continuumLimit : ∀ G →
      Top.IsContinuumLimitOf S G
        (finiteMeasure finite G)
        (continuumMeasure G)

    schwingerBelongsToContinuumMeasure : ∀ G →
      Top.SchwingerBelongsToMeasure S
        (continuumMeasure G)
        (schwinger G)

    acceptedWightmanOrOSAxioms : ∀ G →
      Top.SatisfiesAcceptedWightmanOrOSAxioms S G
        (schwinger G)

    reconstructedHilbertSpace : ∀ G →
      Top.IsReconstructedHilbertSpace S G
        (schwinger G)
        (hilbertSpace G)

    positiveSelfAdjointHamiltonian : ∀ G →
      Top.IsPositiveSelfAdjointHamiltonian S
        (hilbertSpace G)
        (hamiltonian G)

open PinnedContinuumYMConstruction public

------------------------------------------------------------------------
-- Physical mass gap on that SAME Hamiltonian, with SI attachment.
------------------------------------------------------------------------

record PinnedPhysicalMassGap
    {C : Top.LiteralYangMillsCarriers}
    (S : Top.LiteralYangMillsSemantics C)
    {finite : PinnedFiniteYMConstruction S}
    (continuum : PinnedContinuumYMConstruction S finite) : Set₁ where
  field
    vacuum :
      Top.CompactSimpleGroup C → Top.VacuumState C

    massGap :
      Top.CompactSimpleGroup C → ℚ

    vacuumSectorAndPositiveEnergyComplement : ∀ G →
      Top.IsVacuumSectorAndPositiveEnergyComplement S
        (hilbertSpace continuum G)
        (hamiltonian continuum G)
        (vacuum G)

    strictlyPositiveFiniteMassGap : ∀ G →
      Top.IsStrictlyPositiveFiniteMassGap S
        (hamiltonian continuum G)
        (massGap G)

    physicalScaleLowerBoundUniform : ∀ G →
      Top.PhysicalScaleLowerBoundUniform S G (massGap G)

    noSpectralPollutionBelowGap : ∀ G →
      Top.NoSpectralPollutionBelowGap S G
        (hamiltonian continuum G)
        (massGap G)

    gapAndClusteringDerived : ∀ G →
      Top.GapAndClusteringAreDerivedNotAssumed S G

    -- Physical typing: inverse correlation length first.
    siScales : ∀ G → SI.YangMillsGapScales ℚ

    siMassGap : ∀ G →
      SI.SIYangMillsMassGap ℚ (siScales G)

    -- The literal rational Clay gap is the magnitude of the SAME SI mass
    -- quantity attached to the physical inverse-correlation-length scale.
    literalGapIsSIMassMagnitude : ∀ G →
      massGap G
      ≡
      SI.magnitude (SI.SIYangMillsMassGap.massGap (siMassGap G))

open PinnedPhysicalMassGap public

------------------------------------------------------------------------
-- Local curvature fields / OPE / stress on SAME continuum Schwinger family.
------------------------------------------------------------------------

record PinnedLocalQFTConstruction
    {C : Top.LiteralYangMillsCarriers}
    (S : Top.LiteralYangMillsSemantics C)
    {finite : PinnedFiniteYMConstruction S}
    (continuum : PinnedContinuumYMConstruction S finite) : Set₁ where
  field
    localObservable :
      Top.CompactSimpleGroup C → Top.Position C → Top.Observable C

    curvatureOperator :
      Top.CompactSimpleGroup C →
      Top.CurvaturePolynomial C → Top.LocalOperator C

    opeCoefficient :
      Top.CompactSimpleGroup C →
      Top.LocalOperator C → Top.LocalOperator C → Top.LocalOperator C →
      Top.Position C → Top.OPECoefficient C

    opeRemainder :
      Top.CompactSimpleGroup C →
      Top.LocalOperator C → Top.LocalOperator C →
      Top.Position C → Nat → ℚ

    stressTensor :
      Top.CompactSimpleGroup C → Top.StressTensor C

    gaugeInvariantLocalObservable : ∀ G position →
      Top.IsGaugeInvariantObservable S (localObservable G position)
      × Top.IsLocalObservable S (localObservable G position) position

    curvatureOperatorCorrespondence : ∀ G →
      Top.CurvatureOperatorCorrespondence S G (curvatureOperator G)

    curvatureOperatorsGaugeInvariant : ∀ G polynomial →
      Top.IsGaugeInvariantLocalOperator S (curvatureOperator G polynomial)

    curvatureOperatorsLocal : ∀ G polynomial position →
      Top.IsLocalOperator S (curvatureOperator G polynomial) position

    shortDistanceAsymptoticFreedom : ∀ G →
      Top.HasShortDistanceAsymptoticFreedom S G (schwinger continuum G)

    stressTensorAndOPE : ∀ G →
      Top.HasStressTensorAndOPE S G
        (schwinger continuum G)
        (stressTensor G)

    physicalOPECoefficient : ∀ G left right output position →
      Top.IsPhysicalOPECoefficient S G left right output position
        (opeCoefficient G left right output position)

    physicalOPERemainder : ∀ G left right position depth →
      Top.IsPhysicalOPERemainder S G left right position depth
        (opeRemainder G left right position depth)

open PinnedLocalQFTConstruction public

------------------------------------------------------------------------
-- One canonical pinned object.
------------------------------------------------------------------------

record PinnedYangMillsConstruction
    {C : Top.LiteralYangMillsCarriers}
    (S : Top.LiteralYangMillsSemantics C) : Set₁ where
  field
    spacetime : Top.Spacetime C

    compactSimple : ∀ G → Top.IsCompactSimple S G

    fourDimensionalEuclidean :
      Top.IsFourDimensionalEuclidean S spacetime

    compactSimpleParameterization :
      Top.CompactSimpleParameterizationPreserved S

    finite : PinnedFiniteYMConstruction S

    continuum : PinnedContinuumYMConstruction S finite

    gap : PinnedPhysicalMassGap S continuum

    local : PinnedLocalQFTConstruction S continuum

open PinnedYangMillsConstruction public

------------------------------------------------------------------------
-- Literal construction: all object choices are projections of the pinned
-- object.  No endpoint object is chosen again.
------------------------------------------------------------------------

asLiteralYangMillsConstruction :
  ∀ {C S} →
  PinnedYangMillsConstruction {C = C} S →
  Top.LiteralYangMillsConstruction C S
asLiteralYangMillsConstruction pinned = record
  { Top.LiteralYangMillsConstruction.spacetime =
      spacetime pinned
  ; Top.LiteralYangMillsConstruction.finiteMeasure =
      finiteMeasure (finite pinned)
  ; Top.LiteralYangMillsConstruction.continuumMeasure =
      continuumMeasure (continuum pinned)
  ; Top.LiteralYangMillsConstruction.schwinger =
      schwinger (continuum pinned)
  ; Top.LiteralYangMillsConstruction.localObservable =
      localObservable (local pinned)
  ; Top.LiteralYangMillsConstruction.curvatureOperator =
      curvatureOperator (local pinned)
  ; Top.LiteralYangMillsConstruction.opeCoefficient =
      opeCoefficient (local pinned)
  ; Top.LiteralYangMillsConstruction.opeRemainder =
      opeRemainder (local pinned)
  ; Top.LiteralYangMillsConstruction.stressTensor =
      stressTensor (local pinned)
  ; Top.LiteralYangMillsConstruction.hilbertSpace =
      hilbertSpace (continuum pinned)
  ; Top.LiteralYangMillsConstruction.hamiltonian =
      hamiltonian (continuum pinned)
  ; Top.LiteralYangMillsConstruction.vacuum =
      vacuum (gap pinned)
  ; Top.LiteralYangMillsConstruction.massGap =
      massGap (gap pinned)
  }

------------------------------------------------------------------------
-- Existing T1/T3/T2/T4 consumers compile directly from the pinned object.
------------------------------------------------------------------------

compileStructuralBase :
  ∀ {C S}
    (pinned : PinnedYangMillsConstruction {C = C} S) →
  Five.LiteralClayStructuralBase
    (asLiteralYangMillsConstruction pinned)
compileStructuralBase pinned = record
  { Five.LiteralClayStructuralBase.compactSimple =
      compactSimple pinned
  ; Five.LiteralClayStructuralBase.fourDimensionalEuclidean =
      fourDimensionalEuclidean pinned
  ; Five.LiteralClayStructuralBase.compactSimpleParameterization =
      compactSimpleParameterization pinned
  }

compileWeakCouplingRG :
  ∀ {C S}
    (pinned : PinnedYangMillsConstruction {C = C} S) →
  Five.LiteralWeakCouplingRGConstruction
    (asLiteralYangMillsConstruction pinned)
compileWeakCouplingRG pinned = record
  { Five.LiteralWeakCouplingRGConstruction.finiteVolumeCutoffMeasure =
      finiteVolumeCutoffMeasure (finite pinned)
  ; Five.LiteralWeakCouplingRGConstruction.reflectionPositiveRegularization =
      reflectionPositiveRegularization (finite pinned)
  ; Five.LiteralWeakCouplingRGConstruction.ultravioletYangMillsNormalization =
      ultravioletYangMillsNormalization (finite pinned)
  ; Five.LiteralWeakCouplingRGConstruction.asymptoticallyFreeScaleTrajectory =
      asymptoticallyFreeScaleTrajectory (finite pinned)
  ; Five.LiteralWeakCouplingRGConstruction.gaugeSymmetryPreserved =
      gaugeSymmetryPreserved (finite pinned)
  ; Five.LiteralWeakCouplingRGConstruction.localityPreserved =
      localityPreserved (finite pinned)
  ; Five.LiteralWeakCouplingRGConstruction.euclideanCovariancePreserved =
      euclideanCovariancePreserved (finite pinned)
  ; Five.LiteralWeakCouplingRGConstruction.reflectionPositivityPreserved =
      reflectionPositivityPreserved (finite pinned)
  ; Five.LiteralWeakCouplingRGConstruction.positivityNormalizationPreserved =
      positivityNormalizationPreserved (finite pinned)
  ; Five.LiteralWeakCouplingRGConstruction.volumeCutoffCompatibility =
      volumeCutoffCompatibility (finite pinned)
  }

compileUnifiedContinuum :
  ∀ {C S}
    (pinned : PinnedYangMillsConstruction {C = C} S) →
  Five.UnifiedContinuumYMConstruction
    (asLiteralYangMillsConstruction pinned)
compileUnifiedContinuum pinned = record
  { Five.UnifiedContinuumYMConstruction.continuumLimit =
      continuumLimit (continuum pinned)
  ; Five.UnifiedContinuumYMConstruction.schwingerBelongsToContinuumMeasure =
      schwingerBelongsToContinuumMeasure (continuum pinned)
  ; Five.UnifiedContinuumYMConstruction.acceptedWightmanOrOSAxioms =
      acceptedWightmanOrOSAxioms (continuum pinned)
  ; Five.UnifiedContinuumYMConstruction.reconstructedHilbertSpace =
      reconstructedHilbertSpace (continuum pinned)
  ; Five.UnifiedContinuumYMConstruction.positiveSelfAdjointHamiltonian =
      positiveSelfAdjointHamiltonian (continuum pinned)
  }

compilePhysicalMassGap :
  ∀ {C S}
    (pinned : PinnedYangMillsConstruction {C = C} S) →
  Five.CutoffUniformPhysicalMassGap
    (asLiteralYangMillsConstruction pinned)
compilePhysicalMassGap pinned = record
  { Five.CutoffUniformPhysicalMassGap.vacuumSectorAndPositiveEnergyComplement =
      vacuumSectorAndPositiveEnergyComplement (gap pinned)
  ; Five.CutoffUniformPhysicalMassGap.strictlyPositiveFiniteMassGap =
      strictlyPositiveFiniteMassGap (gap pinned)
  ; Five.CutoffUniformPhysicalMassGap.physicalScaleLowerBoundUniform =
      physicalScaleLowerBoundUniform (gap pinned)
  ; Five.CutoffUniformPhysicalMassGap.noSpectralPollutionBelowGap =
      noSpectralPollutionBelowGap (gap pinned)
  ; Five.CutoffUniformPhysicalMassGap.gapAndClusteringDerived =
      gapAndClusteringDerived (gap pinned)
  }

compileLocalQFT :
  ∀ {C S}
    (pinned : PinnedYangMillsConstruction {C = C} S) →
  Five.ContinuumLocalFieldOPEStressWard
    (asLiteralYangMillsConstruction pinned)
compileLocalQFT pinned = record
  { Five.ContinuumLocalFieldOPEStressWard.gaugeInvariantLocalObservable =
      gaugeInvariantLocalObservable (local pinned)
  ; Five.ContinuumLocalFieldOPEStressWard.curvatureOperatorCorrespondence =
      curvatureOperatorCorrespondence (local pinned)
  ; Five.ContinuumLocalFieldOPEStressWard.curvatureOperatorsGaugeInvariant =
      curvatureOperatorsGaugeInvariant (local pinned)
  ; Five.ContinuumLocalFieldOPEStressWard.curvatureOperatorsLocal =
      curvatureOperatorsLocal (local pinned)
  ; Five.ContinuumLocalFieldOPEStressWard.shortDistanceAsymptoticFreedom =
      shortDistanceAsymptoticFreedom (local pinned)
  ; Five.ContinuumLocalFieldOPEStressWard.stressTensorAndOPE =
      stressTensorAndOPE (local pinned)
  ; Five.ContinuumLocalFieldOPEStressWard.physicalOPECoefficient =
      physicalOPECoefficient (local pinned)
  ; Five.ContinuumLocalFieldOPEStressWard.physicalOPERemainder =
      physicalOPERemainder (local pinned)
  }

------------------------------------------------------------------------
-- T78 A/B/C are now thin compilers from ONE pinned physical construction.
------------------------------------------------------------------------

compileT78A :
  ∀ {C S}
    (pinned : PinnedYangMillsConstruction {C = C} S) →
  T78.UVToContinuumYM
    (asLiteralYangMillsConstruction pinned)
compileT78A pinned = record
  { T78.UVToContinuumYM.weakCouplingRG =
      compileWeakCouplingRG pinned
  ; T78.UVToContinuumYM.continuumYM =
      compileUnifiedContinuum pinned
  }

compileT78B :
  ∀ {C S}
    (pinned : PinnedYangMillsConstruction {C = C} S) →
  T78.SameHamiltonianPhysicalMassGap
    (asLiteralYangMillsConstruction pinned)
compileT78B pinned = record
  { T78.SameHamiltonianPhysicalMassGap.physicalGap =
      compilePhysicalMassGap pinned
  }

compileT78C :
  ∀ {C S}
    (pinned : PinnedYangMillsConstruction {C = C} S) →
  T78.SameFamilyLocalFieldsOPEStressWard
    (asLiteralYangMillsConstruction pinned)
compileT78C pinned = record
  { T78.SameFamilyLocalFieldsOPEStressWard.localFields =
      compileLocalQFT pinned
  }

------------------------------------------------------------------------
-- SI projection: usable without reopening the Clay/T78 object graph.
------------------------------------------------------------------------

pinnedSIMassGap :
  ∀ {C S}
    (pinned : PinnedYangMillsConstruction {C = C} S)
    (G : Top.CompactSimpleGroup C) →
  SI.SIYangMillsMassGap ℚ
    (siScales (gap pinned) G)
pinnedSIMassGap pinned G =
  siMassGap (gap pinned) G

pinnedLiteralGapIsSIMassMagnitude :
  ∀ {C S}
    (pinned : PinnedYangMillsConstruction {C = C} S)
    (G : Top.CompactSimpleGroup C) →
  Top.massGap (asLiteralYangMillsConstruction pinned) G
  ≡
  SI.magnitude
    (SI.SIYangMillsMassGap.massGap
      (pinnedSIMassGap pinned G))
pinnedLiteralGapIsSIMassMagnitude pinned G =
  literalGapIsSIMassMagnitude (gap pinned) G

pinnedPhysicalConstructionCompilerLevel : ProofLevel
pinnedPhysicalConstructionCompilerLevel = machineChecked

pinnedT78ACompilerLevel : ProofLevel
pinnedT78ACompilerLevel = machineChecked

pinnedT78BCompilerLevel : ProofLevel
pinnedT78BCompilerLevel = machineChecked

pinnedT78CCompilerLevel : ProofLevel
pinnedT78CCompilerLevel = machineChecked

pinnedSIGapAttachmentCompilerLevel : ProofLevel
pinnedSIGapAttachmentCompilerLevel = machineChecked

-- Only actual physical analysis/evidence fields remain inputs.  Object choices
-- and same-object attachments are construction/compiler owned.
pinnedPhysicalInputsLevel : ProofLevel
pinnedPhysicalInputsLevel = conditional
