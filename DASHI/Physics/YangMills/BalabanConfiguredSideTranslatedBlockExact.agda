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

------------------------------------------------------------------------
-- Translated blocks are represented in local relative coordinates.
--
-- The global origin is retained in the type of the local chart, but the finite
-- carrier, norm, difference energy and Q=0 predicate depend only on relative
-- coordinates.  Their translation preservation is therefore definitional,
-- rather than an extra analytic estimate.  The separate global-to-local Wilson
-- extraction remains the only geometric matching obligation.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- The translated halo overlap is the already-computed finite multiplicity.
------------------------------------------------------------------------

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

globalWilsonToLocalTranslatedBlockLevel : ProofLevel
globalWilsonToLocalTranslatedBlockLevel = conditional
