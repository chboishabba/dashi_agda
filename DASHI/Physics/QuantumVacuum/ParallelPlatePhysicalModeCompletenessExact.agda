module DASHI.Physics.QuantumVacuum.ParallelPlatePhysicalModeCompletenessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Physics.QuantumVacuum.ParallelPlateTETMModeExpansionSourceAuthorityExact as Source
import DASHI.Physics.QuantumVacuum.ParallelPlatePhysicalModeClassExact as Class
import DASHI.Physics.QuantumVacuum.PerfectConductorTETMProofBearingCompletenessExact as Legacy

------------------------------------------------------------------------
-- PHYSICAL COMPLETENESS WITH TEM EXPLICIT
------------------------------------------------------------------------

fieldExpansionClaim : Transport.SourceBackedClaim
fieldExpansionClaim = record
  { Transport.SourceClaim =
      Source.fieldsExpandedAsLinearCombinationOfModes
        Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName = Source.sourceName Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceLocator = Source.exactSectionLocator Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.reading = "Parallel-plate fields expand in the source TEM/TE/TM mode family."
  }

longitudinalExpansionClaim : Transport.SourceBackedClaim
longitudinalExpansionClaim = record
  { Transport.SourceClaim =
      Source.fieldsExpandedAsLinearCombinationOfModes
        Source.canonicalParallelPlateTETMModeExpansionAuthority
      × Source.longitudinalIntegerQuantisationDerived
        Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceReceipt = tt , tt
  ; Transport.sourceName = Source.sourceName Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceLocator = Source.exactSectionLocator Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.reading = "Parallel-plate mode expansion with integer longitudinal indexing."
  }

record LocalPhysicalModeCompletenessSkeleton : Set₁ where
  field
    PhysicalMode : Set
    modeClass : PhysicalMode → Class.PlateModeClass

    SameSourceAndCasimirModeSemantics : Set
    sameSourceAndCasimirModeSemanticsEvidence : SameSourceAndCasimirModeSemantics

    FiniteEnergyHilbertCarrierMatchesSource : Set
    finiteEnergyHilbertCarrierMatchesSourceEvidence :
      FiniteEnergyHilbertCarrierMatchesSource

    SourceExpansionSpansPhysicalModes : Set
    sourceExpansionToPhysicalSpanning :
      Transport.SourceClaim fieldExpansionClaim →
      (SameSourceAndCasimirModeSemantics × FiniteEnergyHilbertCarrierMatchesSource) →
      SourceExpansionSpansPhysicalModes

    TransverseCoverage : Set
    sourceExpansionToTransverseCoverage :
      Transport.SourceClaim fieldExpansionClaim →
      (SameSourceAndCasimirModeSemantics × FiniteEnergyHilbertCarrierMatchesSource) →
      TransverseCoverage

    LongitudinalCoverage : Set
    sourceExpansionToLongitudinalCoverage :
      Transport.SourceClaim longitudinalExpansionClaim →
      (SameSourceAndCasimirModeSemantics × FiniteEnergyHilbertCarrierMatchesSource) →
      LongitudinalCoverage

    reading : String

open LocalPhysicalModeCompletenessSkeleton public

SourceCarrierWeld : LocalPhysicalModeCompletenessSkeleton → Set
SourceCarrierWeld S =
  SameSourceAndCasimirModeSemantics S ×
  FiniteEnergyHilbertCarrierMatchesSource S

sourceCarrierWeldEvidence :
  (S : LocalPhysicalModeCompletenessSkeleton) → SourceCarrierWeld S
sourceCarrierWeldEvidence S =
  sameSourceAndCasimirModeSemanticsEvidence S ,
  finiteEnergyHilbertCarrierMatchesSourceEvidence S

localTarget :
  (claim : Transport.SourceBackedClaim) →
  (LocalClaim SameObject : Set) →
  (Transport.SourceClaim claim → SameObject → LocalClaim) →
  Transport.LocalTheoremTarget claim
localTarget claim LocalClaim SameObject translate = record
  { Transport.LocalClaim = LocalClaim
  ; Transport.sameMathematicalObject = SameObject
  ; Transport.sourceSemanticsToLocal = translate
  ; Transport.reading = "Source TEM/TE/TM expansion transported only after the finite-energy mode carrier is identified."
  }

compilePhysicalSpanning :
  (S : LocalPhysicalModeCompletenessSkeleton) →
  SourceExpansionSpansPhysicalModes S
compilePhysicalSpanning S =
  Transport.transportSourceBackedTheorem
    fieldExpansionClaim
    (localTarget fieldExpansionClaim
      (SourceExpansionSpansPhysicalModes S)
      (SourceCarrierWeld S)
      (sourceExpansionToPhysicalSpanning S))
    (record { Transport.objectWeld = sourceCarrierWeldEvidence S })

compileTransverseCoverage :
  (S : LocalPhysicalModeCompletenessSkeleton) →
  TransverseCoverage S
compileTransverseCoverage S =
  Transport.transportSourceBackedTheorem
    fieldExpansionClaim
    (localTarget fieldExpansionClaim
      (TransverseCoverage S)
      (SourceCarrierWeld S)
      (sourceExpansionToTransverseCoverage S))
    (record { Transport.objectWeld = sourceCarrierWeldEvidence S })

compileLongitudinalCoverage :
  (S : LocalPhysicalModeCompletenessSkeleton) →
  LongitudinalCoverage S
compileLongitudinalCoverage S =
  Transport.transportSourceBackedTheorem
    longitudinalExpansionClaim
    (localTarget longitudinalExpansionClaim
      (LongitudinalCoverage S)
      (SourceCarrierWeld S)
      (sourceExpansionToLongitudinalCoverage S))
    (record { Transport.objectWeld = sourceCarrierWeldEvidence S })

record ProofBearingPhysicalModeCompleteness
    (S : LocalPhysicalModeCompletenessSkeleton) : Set₁ where
  field
    sourceSpanning : SourceExpansionSpansPhysicalModes S
    transverseCoverage : TransverseCoverage S
    longitudinalCoverage : LongitudinalCoverage S

    reading : String

open ProofBearingPhysicalModeCompleteness public

compilePhysicalModeCompleteness :
  (S : LocalPhysicalModeCompletenessSkeleton) →
  ProofBearingPhysicalModeCompleteness S
compilePhysicalModeCompleteness S = record
  { sourceSpanning = compilePhysicalSpanning S
  ; transverseCoverage = compileTransverseCoverage S
  ; longitudinalCoverage = compileLongitudinalCoverage S
  ; reading = reading S
  }

------------------------------------------------------------------------
-- LEGACY TE/TM ADAPTER
--
-- TEM is represented as the legacy TM-zero branch only here.  The canonical
-- physical datatype remains TEM | TE+ n | TM+ n.
------------------------------------------------------------------------

LegacyTE LegacyTM LegacyZero : Class.PlateModeClass → Set
LegacyTE Class.TEM = ⊥
LegacyTE (Class.TE+ n) = ⊤
LegacyTE (Class.TM+ n) = ⊥

LegacyTM Class.TEM = ⊤
LegacyTM (Class.TE+ n) = ⊥
LegacyTM (Class.TM+ n) = ⊤

LegacyZero Class.TEM = ⊤
LegacyZero (Class.TE+ n) = ⊥
LegacyZero (Class.TM+ n) = ⊥

legacyCovered : ∀ c → LegacyTE c ⊎ LegacyTM c
legacyCovered Class.TEM = inj₂ tt
legacyCovered (Class.TE+ n) = inj₁ tt
legacyCovered (Class.TM+ n) = inj₂ tt

legacyNoDoubleCounting : ∀ c → LegacyTE c → LegacyTM c → ⊥
legacyNoDoubleCounting Class.TEM ()
legacyNoDoubleCounting (Class.TE+ n) te ()
legacyNoDoubleCounting (Class.TM+ n) ()

legacyZeroExactlyTEM : ∀ c → LegacyZero c → Class.IsTEM c
legacyZeroExactlyTEM Class.TEM proof = tt
legacyZeroExactlyTEM (Class.TE+ n) ()
legacyZeroExactlyTEM (Class.TM+ n) ()

asLegacyProofBearingCompleteness :
  (S : LocalPhysicalModeCompletenessSkeleton) →
  Legacy.ProofBearingTETMCompletenessReceipt
asLegacyProofBearingCompleteness S = record
  { Legacy.PhysicalMode = PhysicalMode S
  ; Legacy.TE = λ m → LegacyTE (modeClass S m)
  ; Legacy.TM = λ m → LegacyTM (modeClass S m)
  ; Legacy.longitudinalIndex = λ m → Class.longitudinalIndex (modeClass S m)
  ; Legacy.zeroSector = λ m → LegacyZero (modeClass S m)

  ; Legacy.EveryPhysicalModeTEorTM =
      ∀ m → LegacyTE (modeClass S m) ⊎ LegacyTM (modeClass S m)
  ; Legacy.everyPhysicalModeTEorTMEvidence = λ m → legacyCovered (modeClass S m)

  ; Legacy.NoDoubleCountingAwayFromZeroSector =
      ∀ m → LegacyTE (modeClass S m) → LegacyTM (modeClass S m) → ⊥
  ; Legacy.noDoubleCountingAwayFromZeroSectorEvidence =
      λ m → legacyNoDoubleCounting (modeClass S m)

  ; Legacy.ZeroSectorCountingCorrect =
      ∀ m → LegacyZero (modeClass S m) → Class.IsTEM (modeClass S m)
  ; Legacy.zeroSectorCountingCorrectEvidence =
      λ m → legacyZeroExactlyTEM (modeClass S m)

  ; Legacy.TransverseCompleteness = TransverseCoverage S
  ; Legacy.transverseCompletenessEvidence = compileTransverseCoverage S

  ; Legacy.LongitudinalCompleteness = LongitudinalCoverage S
  ; Legacy.longitudinalCompletenessEvidence = compileLongitudinalCoverage S

  ; Legacy.reading =
      "Legacy TE/TM adapter generated from the canonical TEM | TE+ | TM+ physical mode class."
  }

------------------------------------------------------------------------
-- BIDI pruning.
------------------------------------------------------------------------

record ReversePhysicalModeCompletenessObligations : Set where
  field
    oneFiniteEnergySourceCarrierWeld : Set
    reading : String

open ReversePhysicalModeCompletenessObligations public

data SeparateTEZeroExclusionReceiptStillRequired : Set where
data SeparateTMZeroCountingReceiptStillRequired : Set where
data SeparateTETMIndependenceReceiptStillRequired : Set where

teZeroPrunedByDatatype : SeparateTEZeroExclusionReceiptStillRequired → ⊥
teZeroPrunedByDatatype ()

tmZeroPrunedByTEMConstructor : SeparateTMZeroCountingReceiptStillRequired → ⊥
tmZeroPrunedByTEMConstructor ()

independencePrunedByConstructors : SeparateTETMIndependenceReceiptStillRequired → ⊥
independencePrunedByConstructors ()

record Status : Set where
  field
    sourceSpanningCompilerOwned : Bool
    transverseCoverageCompilerOwned : Bool
    longitudinalCoverageCompilerOwned : Bool
    temZeroSectorTyped : Bool
    teZeroUnrepresentable : Bool
    teTmIndependenceByConstruction : Bool
    legacyAdapterOwned : Bool
    onlyFiniteEnergyCarrierWeldRemainsInMaxwellFamily : Bool

    sourceSpanningCompilerOwnedIsTrue : sourceSpanningCompilerOwned ≡ true
    transverseCoverageCompilerOwnedIsTrue : transverseCoverageCompilerOwned ≡ true
    longitudinalCoverageCompilerOwnedIsTrue : longitudinalCoverageCompilerOwned ≡ true
    temZeroSectorTypedIsTrue : temZeroSectorTyped ≡ true
    teZeroUnrepresentableIsTrue : teZeroUnrepresentable ≡ true
    teTmIndependenceByConstructionIsTrue : teTmIndependenceByConstruction ≡ true
    legacyAdapterOwnedIsTrue : legacyAdapterOwned ≡ true
    onlyFiniteEnergyCarrierWeldRemainsInMaxwellFamilyIsTrue :
      onlyFiniteEnergyCarrierWeldRemainsInMaxwellFamily ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { sourceSpanningCompilerOwned = true
  ; transverseCoverageCompilerOwned = true
  ; longitudinalCoverageCompilerOwned = true
  ; temZeroSectorTyped = true
  ; teZeroUnrepresentable = true
  ; teTmIndependenceByConstruction = true
  ; legacyAdapterOwned = true
  ; onlyFiniteEnergyCarrierWeldRemainsInMaxwellFamily = true
  ; sourceSpanningCompilerOwnedIsTrue = refl
  ; transverseCoverageCompilerOwnedIsTrue = refl
  ; longitudinalCoverageCompilerOwnedIsTrue = refl
  ; temZeroSectorTypedIsTrue = refl
  ; teZeroUnrepresentableIsTrue = refl
  ; teTmIndependenceByConstructionIsTrue = refl
  ; legacyAdapterOwnedIsTrue = refl
  ; onlyFiniteEnergyCarrierWeldRemainsInMaxwellFamilyIsTrue = refl
  }
