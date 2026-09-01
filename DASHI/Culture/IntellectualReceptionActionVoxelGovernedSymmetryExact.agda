module DASHI.Culture.IntellectualReceptionActionVoxelGovernedSymmetryExact where

open import DASHI.Core.Prelude

import DASHI.Culture.IntellectualReceptionParetoIncomparabilityMonster369ActionBridgeExact as Bridge
import DASHI.Culture.IntellectualReceptionTernaryParetoSituatedChoiceExact as Choice
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral

------------------------------------------------------------------------
-- ACTION VOXEL
--
-- Typed coordinate roles:
--   x = comparison outcome
--   y = response policy
--   z = independent-authority status
--
-- The underlying carrier is the merged {-1,0,+1}^3 Base369 voxel, but the
-- semantic roles are not interchangeable merely because the geometry admits
-- coordinate permutations.
------------------------------------------------------------------------

data AuthorityStatus : Set where
  authorityAbsent
  authorityRequired
  authoritySupplied
  : AuthorityStatus

responseTrit : Bridge.IncomparabilityResponse → SSP.SSPTrit
responseTrit Bridge.preserveAlternatives = SSP.sspZero
responseTrit Bridge.seekDiscriminator = SSP.sspPosOne
responseTrit Bridge.useIndependentAuthorisedRule = SSP.sspNegOne

authorityTrit : AuthorityStatus → SSP.SSPTrit
authorityTrit authorityAbsent = SSP.sspNegOne
authorityTrit authorityRequired = SSP.sspZero
authorityTrit authoritySupplied = SSP.sspPosOne

record ActionVoxelState : Set where
  constructor action-voxel-state
  field
    comparisonOutcome : SSP.SSPTrit
    responsePolicy : Bridge.IncomparabilityResponse
    authorityStatus : AuthorityStatus

open ActionVoxelState public

actionVoxelPoint : ActionVoxelState → Geometry.Ternary27Point
actionVoxelPoint state =
  Geometry.ternary27Point
    (comparisonOutcome state)
    (responseTrit (responsePolicy state))
    (authorityTrit (authorityStatus state))

preserveState : ActionVoxelState
preserveState =
  action-voxel-state
    (Bridge.paretoRelationTrit Choice.discriminatorVsGoverned)
    Bridge.preserveAlternatives
    authorityAbsent

seekState : ActionVoxelState
seekState =
  action-voxel-state
    (Bridge.paretoRelationTrit Choice.discriminatorVsGoverned)
    Bridge.seekDiscriminator
    authorityAbsent

authorisedRuleState : ActionVoxelState
authorisedRuleState =
  action-voxel-state
    (Bridge.paretoRelationTrit Choice.discriminatorVsGoverned)
    Bridge.useIndependentAuthorisedRule
    authoritySupplied

preservePointExact :
  actionVoxelPoint preserveState ≡
  Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne
preservePointExact = refl

seekPointExact :
  actionVoxelPoint seekState ≡
  Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne
seekPointExact = refl

authorisedRulePointExact :
  actionVoxelPoint authorisedRuleState ≡
  Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne
authorisedRulePointExact = refl

------------------------------------------------------------------------
-- 1. The preserve -> discriminate escalation is a literal one-coordinate edge.
------------------------------------------------------------------------

preserveToSeekAdjacent :
  Geometry.HypervoxelAdjacent
    (actionVoxelPoint preserveState)
    (actionVoxelPoint seekState)
preserveToSeekAdjacent = Geometry.adjacentY Geometry.zeroToPos

------------------------------------------------------------------------
-- 2. Directional comparison reflection is semantically lawful when it acts
-- only on the comparison coordinate. Response and authority are preserved.
------------------------------------------------------------------------

reflectComparisonOnly : ActionVoxelState → ActionVoxelState
reflectComparisonOnly state =
  action-voxel-state
    (Signed.negateTrit (comparisonOutcome state))
    (responsePolicy state)
    (authorityStatus state)

reflectComparisonOnlyInvolutive :
  (state : ActionVoxelState) →
  reflectComparisonOnly (reflectComparisonOnly state) ≡ state
reflectComparisonOnlyInvolutive
  (action-voxel-state SSP.sspNegOne response authority) = refl
reflectComparisonOnlyInvolutive
  (action-voxel-state SSP.sspZero response authority) = refl
reflectComparisonOnlyInvolutive
  (action-voxel-state SSP.sspPosOne response authority) = refl

reflectComparisonAgreesWithVoxelFlipX :
  (state : ActionVoxelState) →
  actionVoxelPoint (reflectComparisonOnly state)
  ≡ Signed.flipX (actionVoxelPoint state)
reflectComparisonAgreesWithVoxelFlipX
  (action-voxel-state outcome response authority) = refl

incomparabilityStateFixedUnderComparisonReflection :
  reflectComparisonOnly preserveState ≡ preserveState
incomparabilityStateFixedUnderComparisonReflection = refl

------------------------------------------------------------------------
-- 3. Geometric coordinate permutations exist, but typed semantic roles block
-- treating them as automatic governance symmetries.
------------------------------------------------------------------------

geometricSwapXY : Geometry.Ternary27Point → Geometry.Ternary27Point
geometricSwapXY = Spectral.swapXY

geometricRotateXYZ : Geometry.Ternary27Point → Geometry.Ternary27Point
geometricRotateXYZ = Spectral.rotateXYZ

seekPointSwappedXY :
  geometricSwapXY (actionVoxelPoint seekState)
  ≡ Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne
seekPointSwappedXY = refl

data ComparisonResponseRolesInterchangeable : Set where
data ResponseAuthorityRolesInterchangeable : Set where
data GeometricPermutationAutomaticallyGovernanceLawful : Set where

data LawfulActionTransformation :
  (ActionVoxelState → ActionVoxelState) → Set where
  comparisonReflectionLawful :
    LawfulActionTransformation reflectComparisonOnly

comparisonResponseRolesNotInterchangeable :
  ComparisonResponseRolesInterchangeable → ⊥
comparisonResponseRolesNotInterchangeable ()

responseAuthorityRolesNotInterchangeable :
  ResponseAuthorityRolesInterchangeable → ⊥
responseAuthorityRolesNotInterchangeable ()

geometricPermutationDoesNotSelfAuthorise :
  GeometricPermutationAutomaticallyGovernanceLawful → ⊥
geometricPermutationDoesNotSelfAuthorise ()

------------------------------------------------------------------------
-- 4. Independent authority is not generated by response reflection or by
-- voxel symmetry.  The authorised-rule state carries authoritySupplied as an
-- independent coordinate.
------------------------------------------------------------------------

data VoxelSymmetryCreatesIndependentAuthority : Set where
data ResponseCodeCreatesIndependentAuthority : Set where

voxelSymmetryDoesNotCreateAuthority :
  VoxelSymmetryCreatesIndependentAuthority → ⊥
voxelSymmetryDoesNotCreateAuthority ()

responseCodeDoesNotCreateAuthority :
  ResponseCodeCreatesIndependentAuthority → ⊥
responseCodeDoesNotCreateAuthority ()

authorisedRuleCarriesSuppliedAuthority :
  authorityStatus authorisedRuleState ≡ authoritySupplied
authorisedRuleCarriesSuppliedAuthority = refl

------------------------------------------------------------------------
-- 5. Monster/369 symmetry surfaces remain available at carrier level only.
------------------------------------------------------------------------

signedBoundaryRetained : Signed.SignedTernaryVoxelSymmetryBoundary
signedBoundaryRetained = Signed.canonicalSignedTernaryVoxelSymmetryBoundary

spectralBoundaryRetained : Spectral.Base369Ternary27SpectralSymmetryBoundary
spectralBoundaryRetained = Spectral.canonicalBase369Ternary27SpectralSymmetryBoundary

data LawfulActionTransformationIsMonsterAction : Set where
data ActionVoxelIsMonsterRepresentation : Set where

lawfulGovernanceTransformationDoesNotBecomeMonsterAction :
  LawfulActionTransformationIsMonsterAction → ⊥
lawfulGovernanceTransformationDoesNotBecomeMonsterAction ()

actionVoxelDoesNotBecomeMonsterRepresentation :
  ActionVoxelIsMonsterRepresentation → ⊥
actionVoxelDoesNotBecomeMonsterRepresentation ()

record IntellectualReceptionActionVoxelGovernedSymmetryBoundary : Set where
  constructor intellectual-reception-action-voxel-governed-symmetry-boundary
  field
    actionVoxelUsesMergedTwentySevenCarrier : Bool
    coordinateRolesAreTyped : Bool
    preserveToDiscriminateIsOneCoordinateEdge : Bool
    comparisonReflectionIsLawful : Bool
    comparisonReflectionPreservesResponseAndAuthority : Bool
    geometricCoordinatePermutationsExist : Bool
    geometricPermutationAutomaticallyGovernanceLawful : Bool
    coordinateRolesInterchangeable : Bool
    voxelSymmetryCreatesIndependentAuthority : Bool
    lawfulGovernanceTransformationIsMonsterAction : Bool
    actionVoxelIsMonsterRepresentation : Bool
    sourceAttributionBoundarySurvives : Bool

canonicalIntellectualReceptionActionVoxelGovernedSymmetryBoundary :
  IntellectualReceptionActionVoxelGovernedSymmetryBoundary
canonicalIntellectualReceptionActionVoxelGovernedSymmetryBoundary =
  intellectual-reception-action-voxel-governed-symmetry-boundary
    true true true true true true false false false false false true
