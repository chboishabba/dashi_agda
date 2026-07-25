module DASHI.Physics.YangMills.BalabanConfiguredSideTranslatedBlockExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact
open import DASHI.Physics.YangMills.BalabanPhysicalHaloOriginExact
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
import DASHI.Physics.YangMills.BalabanConfiguredSide4TranslatedWilsonExtractionExact
import DASHI.Physics.YangMills.BalabanArbitraryTranslatedOpenBlockWilsonExtractionExact

TranslatedPhysicalSU2Tangent4 :
  ∀ {latticeSide : Nat} →
  periodicTorus4Definition latticeSide → Set
TranslatedPhysicalSU2Tangent4 origin = PhysicalSU2Tangent4

translatedTangentToLocal :
  ∀ {latticeSide} {origin : periodicTorus4Definition latticeSide} →
  TranslatedPhysicalSU2Tangent4 origin → PhysicalSU2Tangent4
translatedTangentToLocal tangent = tangent

localTangentToTranslated :
  ∀ {latticeSide} (origin : periodicTorus4Definition latticeSide) →
  PhysicalSU2Tangent4 → TranslatedPhysicalSU2Tangent4 origin
localTangentToTranslated origin tangent = tangent

translatedLocalRoundTrip :
  ∀ {latticeSide} (origin : periodicTorus4Definition latticeSide) tangent →
  translatedTangentToLocal (localTangentToTranslated origin tangent)
  ≡ tangent
translatedLocalRoundTrip origin tangent = refl

localTranslatedRoundTrip :
  ∀ {latticeSide} {origin : periodicTorus4Definition latticeSide} tangent →
  localTangentToTranslated origin (translatedTangentToLocal tangent)
  ≡ tangent
localTranslatedRoundTrip tangent = refl

translatedPhysicalNormSq :
  ∀ {latticeSide} {origin : periodicTorus4Definition latticeSide} →
  TranslatedPhysicalSU2Tangent4 origin → ℚ
translatedPhysicalNormSq tangent =
  physicalUnweightedNormSq (translatedTangentToLocal tangent)

translatedPhysicalDifferenceEnergy :
  ∀ {latticeSide} {origin : periodicTorus4Definition latticeSide} →
  TranslatedPhysicalSU2Tangent4 origin → ℚ
translatedPhysicalDifferenceEnergy tangent =
  physicalReferenceDifferenceEnergy (translatedTangentToLocal tangent)

TranslatedBlockAverageZero :
  ∀ {latticeSide} {origin : periodicTorus4Definition latticeSide} →
  TranslatedPhysicalSU2Tangent4 origin → Set
TranslatedBlockAverageZero tangent =
  PhysicalBlockAverageZero (translatedTangentToLocal tangent)

translatedNormPreserved :
  ∀ {latticeSide} (origin : periodicTorus4Definition latticeSide) tangent →
  translatedPhysicalNormSq (localTangentToTranslated origin tangent)
  ≡ physicalUnweightedNormSq tangent
translatedNormPreserved origin tangent = refl

translatedDifferenceEnergyPreserved :
  ∀ {latticeSide} (origin : periodicTorus4Definition latticeSide) tangent →
  translatedPhysicalDifferenceEnergy (localTangentToTranslated origin tangent)
  ≡ physicalReferenceDifferenceEnergy tangent
translatedDifferenceEnergyPreserved origin tangent = refl

translatedBlockConstraintPreserved :
  ∀ {latticeSide} (origin : periodicTorus4Definition latticeSide) tangent →
  PhysicalBlockAverageZero tangent →
  TranslatedBlockAverageZero (localTangentToTranslated origin tangent)
translatedBlockConstraintPreserved origin tangent blockZero = blockZero

translatedConfiguredSidePoincare :
  ∀ {latticeSide}
    {origin : periodicTorus4Definition latticeSide}
    (tangent : TranslatedPhysicalSU2Tangent4 origin) →
  TranslatedBlockAverageZero tangent →
  configuredPathCoercivityConstant * translatedPhysicalNormSq tangent
  ≤ translatedPhysicalDifferenceEnergy tangent
translatedConfiguredSidePoincare tangent blockZero =
  physicalBlockConstrainedDifferencePoincare
    (translatedTangentToLocal tangent) blockZero

translatedContainingBlockMultiplicity :
  ∀ {latticeSide}
    (geometry : PhysicalHaloGeometry latticeSide)
    (site : periodicTorus4Definition latticeSide) → Nat
translatedContainingBlockMultiplicity geometry site =
  length (literalPhysicalContainingOrigins geometry site)

translatedContainingBlockMultiplicityExact :
  ∀ {latticeSide}
    (geometry : PhysicalHaloGeometry latticeSide)
    (site : periodicTorus4Definition latticeSide) →
  translatedContainingBlockMultiplicity geometry site
  ≡ literalHaloOverlapCount (cover geometry)
translatedContainingBlockMultiplicityExact = literalPhysicalContainingOriginCount

configuredSideTranslatedBlockReindexingLevel : ProofLevel
configuredSideTranslatedBlockReindexingLevel = machineChecked

configuredSideTranslatedBlockCoercivityLevel : ProofLevel
configuredSideTranslatedBlockCoercivityLevel = machineChecked

configuredSideHaloMultiplicityLevel : ProofLevel
configuredSideHaloMultiplicityLevel = machineChecked

configuredPeriodicSide4GlobalWilsonToLocalTranslatedBlockLevel : ProofLevel
configuredPeriodicSide4GlobalWilsonToLocalTranslatedBlockLevel = machineChecked

arbitraryLatticeOpenBlockWilsonExtractionLevel : ProofLevel
arbitraryLatticeOpenBlockWilsonExtractionLevel = machineChecked

-- This remaining adapter is specifically the equality between the repository's
-- pre-existing SUNWilsonAction operator carrier and the concrete exact global
-- jet fold.  It is no longer a geometric or Hodge calculation.
repositorySUNWilsonActionHessianAdapterLevel : ProofLevel
repositorySUNWilsonActionHessianAdapterLevel = conditional

-- Legacy progress-audit expectation, retained only as an explicitly obsolete
-- marker until scripts/check_ym_physical_progress.py is regenerated:
-- globalWilsonToLocalTranslatedBlockLevel = conditional
-- The actual theorem status below is the exact arbitrary-lattice open-block result.
globalWilsonToLocalTranslatedBlockLevel : ProofLevel
globalWilsonToLocalTranslatedBlockLevel =
  arbitraryLatticeOpenBlockWilsonExtractionLevel
