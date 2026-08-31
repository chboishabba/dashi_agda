module DASHI.Chemistry.CarbonBackboneReachableChemistryConeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.CarbonChemicalSuitabilityLifeBoundaryExact as Carbon
import DASHI.Governance.OptionConeCoercionExact as Cone

------------------------------------------------------------------------
-- CARBON / ALTERNATIVE-BACKBONE REACHABLE CHEMISTRY CONE
--
-- This is a finite theorem fixture, not a quantitative survey of all possible
-- carbon or silicon chemistry.  It turns the historical 'carbon is special'
-- intuition into the correct proof shape: compare declared reachable chemical
-- capabilities under a stated environment and require explicit witnesses for
-- inclusion plus at least one distinguishing capability.
------------------------------------------------------------------------

data BackboneState : Set where
  carbonCarrier siliconComparison : BackboneState

data ChemistryCapability : Set where
  stableChainFormation
  branchedFrameworkFormation
  multipleBondRepertoire
  heteroatomFunctionalisation
  broadRedoxRepertoire
  macromolecularCombinatorics
  informationPolymerCandidate
  : ChemistryCapability

data ReachableChemistry : BackboneState → ChemistryCapability → Set where
  carbonStableChain : ReachableChemistry carbonCarrier stableChainFormation
  carbonBranched : ReachableChemistry carbonCarrier branchedFrameworkFormation
  carbonMultipleBond : ReachableChemistry carbonCarrier multipleBondRepertoire
  carbonHeteroatom : ReachableChemistry carbonCarrier heteroatomFunctionalisation
  carbonRedox : ReachableChemistry carbonCarrier broadRedoxRepertoire
  carbonMacro : ReachableChemistry carbonCarrier macromolecularCombinatorics
  carbonInfoPolymer : ReachableChemistry carbonCarrier informationPolymerCandidate

  siliconStableChain : ReachableChemistry siliconComparison stableChainFormation
  siliconHeteroatom : ReachableChemistry siliconComparison heteroatomFunctionalisation

chemistryCone : Cone.SafeReachabilitySystem BackboneState ChemistryCapability
chemistryCone = Cone.safeReachabilitySystem ReachableChemistry

siliconConeIncludedInCarbonFixture :
  (capability : ChemistryCapability) →
  ReachableChemistry siliconComparison capability →
  ReachableChemistry carbonCarrier capability
siliconConeIncludedInCarbonFixture stableChainFormation siliconStableChain =
  carbonStableChain
siliconConeIncludedInCarbonFixture heteroatomFunctionalisation siliconHeteroatom =
  carbonHeteroatom

carbonFixtureHasStrictlyLargerDeclaredCone :
  Cone.StrictSafeReachabilityContraction
    chemistryCone carbonCarrier siliconComparison
carbonFixtureHasStrictlyLargerDeclaredCone =
  Cone.strictSafeReachabilityContraction
    siliconConeIncludedInCarbonFixture
    informationPolymerCandidate
    carbonInfoPolymer
    (λ ())

carbonBoundary : Carbon.CarbonChemicalSuitabilityBoundary
carbonBoundary = Carbon.canonicalCarbonChemicalSuitabilityBoundary

record ReachableChemistryConeReceipt : Set where
  constructor reachable-chemistry-cone-receipt
  field
    environmentReference : String
    backboneDefinitionReference : String
    capabilityLanguageReference : String
    carbonReachabilityReference : String
    comparisonReachabilityReference : String
    inclusionValidationReference : String
    distinguishingCapabilityReference : String
    alternativeBackboneReference : String
    provenanceReference : String
    validationReference : String

record CarbonBackboneReachableChemistryConeBoundary : Set where
  constructor carbon-backbone-reachable-chemistry-cone-boundary
  field
    carbonSuitabilityCanBeAskedAsReachableOptionConeQuestion : Bool
    carbonSuitabilityCanBeAskedAsReachableOptionConeQuestionIsTrue :
      carbonSuitabilityCanBeAskedAsReachableOptionConeQuestion ≡ true
    fixtureConeComparisonProvesUniversalCarbonDominance : Bool
    fixtureConeComparisonProvesUniversalCarbonDominanceIsFalse :
      fixtureConeComparisonProvesUniversalCarbonDominance ≡ false
    moreReachableChemistryImpliesAbiogenesis : Bool
    moreReachableChemistryImpliesAbiogenesisIsFalse :
      moreReachableChemistryImpliesAbiogenesis ≡ false
    moreReachableChemistryImpliesConsciousness : Bool
    moreReachableChemistryImpliesConsciousnessIsFalse :
      moreReachableChemistryImpliesConsciousness ≡ false
    moleculeCountAloneDefinesChemicalSuitability : Bool
    moleculeCountAloneDefinesChemicalSuitabilityIsFalse :
      moleculeCountAloneDefinesChemicalSuitability ≡ false
    environmentAndConsumerMustIndexConeComparison : Bool
    environmentAndConsumerMustIndexConeComparisonIsTrue :
      environmentAndConsumerMustIndexConeComparison ≡ true
    reading : String

canonicalCarbonBackboneReachableChemistryConeBoundary :
  CarbonBackboneReachableChemistryConeBoundary
canonicalCarbonBackboneReachableChemistryConeBoundary =
  carbon-backbone-reachable-chemistry-cone-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    "Carbon suitability is represented as a consumer- and environment-indexed reachable chemistry cone, not as a mystical scalar. The finite fixture witnesses a strict declared capability difference relative to one comparison carrier, but does not establish universal carbon dominance, abiogenesis, life inevitability or consciousness."
