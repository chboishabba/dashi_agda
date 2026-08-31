module DASHI.Governance.SexedHistoricalBase369TransitionPathExact where

------------------------------------------------------------------------
-- SEXED HISTORICAL TRANSITION PATHS ON THE BASE369 TERNARY-27 CARRIER
--
-- The finite historical comparison layer has two selected endpoint objects,
-- masculine-coded and feminine-coded, and exactly one abstract construction
-- arrow between each ordered pair.  This gives a tiny path category with four
-- arrow types:
--
--   M -> M    M -> F
--   F -> M    F -> F
--
-- The binary endpoint selection is NOT an ontology of sex/gender.  Each arrow
-- is charted into the canonical Base369 T3 = {-1,0,+1}^3 carrier, where the
-- third coordinate remains ternary path admissibility: reject / unresolved /
-- admit.  The zero coordinate is therefore retained rather than forced into a
-- binary historical pole.
--
-- The Base369 / C3 / Monster material below is a carrier-and-symmetry seam.
-- Shared ternary geometry or an exact phase intertwiner does not promote this
-- historical path category into a Monster representation, gauge connection,
-- or physical holonomy.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed
import DASHI.Governance.SexedHistoricalBinaryTernaryDialecticExact as BT

------------------------------------------------------------------------
-- 1. Two selected historical comparison objects.  This is deliberately a
--    finite comparison chart, not an exhaustive gender ontology.
------------------------------------------------------------------------

data Position2 : Set where
  masculineObject feminineObject : Position2

positionTrit : Position2 → SSP.SSPTrit
positionTrit masculineObject = SSP.sspNegOne
positionTrit feminineObject = SSP.sspPosOne

------------------------------------------------------------------------
-- 2. Ternary path qualification remains orthogonal to endpoint coding.
------------------------------------------------------------------------

data PathAdmissibility : Set where
  rejectedPath unresolvedPath admittedPath : PathAdmissibility

admissibilityTrit : PathAdmissibility → SSP.SSPTrit
admissibilityTrit rejectedPath = SSP.sspNegOne
admissibilityTrit unresolvedPath = SSP.sspZero
admissibilityTrit admittedPath = SSP.sspPosOne

admissibilityDisposition : PathAdmissibility → Suspension.EpistemicDisposition
admissibilityDisposition rejectedPath = Suspension.rejectHere
admissibilityDisposition unresolvedPath = Suspension.suspendAndRefine
admissibilityDisposition admittedPath = Suspension.acceptHere

unresolvedPathRefines :
  admissibilityDisposition unresolvedPath ≡ Suspension.suspendAndRefine
unresolvedPathRefines = refl

------------------------------------------------------------------------
-- 3. Thin two-object path category: one construction arrow for each endpoint
--    pair.  Composition, identities and associativity are exact.
------------------------------------------------------------------------

data ConstructionArrow : Position2 → Position2 → Set where
  arrow : ∀ {a b} → ConstructionArrow a b

idArrow : (a : Position2) → ConstructionArrow a a
idArrow a = arrow

infixr 7 _∘c_
_∘c_ : ∀ {a b c} → ConstructionArrow b c → ConstructionArrow a b → ConstructionArrow a c
arrow ∘c arrow = arrow

leftIdentity :
  ∀ {a b} (f : ConstructionArrow a b) →
  idArrow b ∘c f ≡ f
leftIdentity arrow = refl

rightIdentity :
  ∀ {a b} (f : ConstructionArrow a b) →
  f ∘c idArrow a ≡ f
rightIdentity arrow = refl

associativeComposition :
  ∀ {a b c d}
    (f : ConstructionArrow a b)
    (g : ConstructionArrow b c)
    (h : ConstructionArrow c d) →
  (h ∘c g) ∘c f ≡ h ∘c (g ∘c f)
associativeComposition arrow arrow arrow = refl

mm : ConstructionArrow masculineObject masculineObject
mm = arrow

mf : ConstructionArrow masculineObject feminineObject
mf = arrow

fm : ConstructionArrow feminineObject masculineObject
fm = arrow

ff : ConstructionArrow feminineObject feminineObject
ff = arrow

------------------------------------------------------------------------
-- 4. Base369 chart: source × target × admissibility is one literal ternary-27
--    point.  The full 27-point carrier includes unresolved source/target
--    coordinates beyond the selected four binary endpoint arrows.
------------------------------------------------------------------------

arrowPoint :
  ∀ {a b} → ConstructionArrow a b → PathAdmissibility → Geometry.Ternary27Point
arrowPoint {a} {b} arrow status =
  Geometry.ternary27Point
    (positionTrit a)
    (positionTrit b)
    (admissibilityTrit status)

mmAdmittedPoint : Geometry.Ternary27Point
mmAdmittedPoint = arrowPoint mm admittedPath

mfAdmittedPoint : Geometry.Ternary27Point
mfAdmittedPoint = arrowPoint mf admittedPath

fmAdmittedPoint : Geometry.Ternary27Point
fmAdmittedPoint = arrowPoint fm admittedPath

ffAdmittedPoint : Geometry.Ternary27Point
ffAdmittedPoint = arrowPoint ff admittedPath

mfUnresolvedPoint : Geometry.Ternary27Point
mfUnresolvedPoint = arrowPoint mf unresolvedPath

allFourAdmittedChannelsAreCornerStratum :
  Strata.voxelStratum mmAdmittedPoint ≡ Strata.cornerStratum
  × Strata.voxelStratum mfAdmittedPoint ≡ Strata.cornerStratum
  × Strata.voxelStratum fmAdmittedPoint ≡ Strata.cornerStratum
  × Strata.voxelStratum ffAdmittedPoint ≡ Strata.cornerStratum
allFourAdmittedChannelsAreCornerStratum = refl , refl , refl , refl

unresolvedCrossChannelIsEdgeCentre :
  Strata.voxelStratum mfUnresolvedPoint ≡ Strata.edgeCentreStratum
unresolvedCrossChannelIsEdgeCentre = refl

------------------------------------------------------------------------
-- 5. Ordered cross-paths.  M->F->M and F->M->F have different composite
--    endpoints even though a coarse observer can label both as "cross twice".
------------------------------------------------------------------------

data CrossPath : Set where
  masculineCrossBack feminineCrossBack : CrossPath

data CompositeChannel : Set where
  mmComposite mfComposite fmComposite ffComposite : CompositeChannel

data CrossCountSurface : Set where
  crossedTwice : CrossCountSurface

crossCount : CrossPath → CrossCountSurface
crossCount _ = crossedTwice

compositeChannel : CrossPath → CompositeChannel
compositeChannel masculineCrossBack = mmComposite
compositeChannel feminineCrossBack = ffComposite

masculineCrossCompositeExact : fm ∘c mf ≡ mm
masculineCrossCompositeExact = refl

feminineCrossCompositeExact : mf ∘c fm ≡ ff
feminineCrossCompositeExact = refl

crossOrderChangesComposite :
  compositeChannel masculineCrossBack ≡ compositeChannel feminineCrossBack → ⊥
crossOrderChangesComposite ()

coarseCrossCountCannotRecoverComposite :
  INF.FactorsThrough crossCount compositeChannel → ⊥
coarseCrossCountCannotRecoverComposite =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      masculineCrossBack
      feminineCrossBack
      refl
      (λ ()))

------------------------------------------------------------------------
-- 6. Ternary qualification composition.  Rejection is absorbing; admission
--    requires both legs admitted; every other pair remains unresolved.
------------------------------------------------------------------------

combineAdmissibility : PathAdmissibility → PathAdmissibility → PathAdmissibility
combineAdmissibility rejectedPath _ = rejectedPath
combineAdmissibility _ rejectedPath = rejectedPath
combineAdmissibility admittedPath admittedPath = admittedPath
combineAdmissibility _ _ = unresolvedPath

admittedCompositionRemainsAdmitted :
  combineAdmissibility admittedPath admittedPath ≡ admittedPath
admittedCompositionRemainsAdmitted = refl

unresolvedFirstDoesNotPromoteAdmission :
  combineAdmissibility unresolvedPath admittedPath ≡ unresolvedPath
unresolvedFirstDoesNotPromoteAdmission = refl

unresolvedSecondDoesNotPromoteAdmission :
  combineAdmissibility admittedPath unresolvedPath ≡ unresolvedPath
unresolvedSecondDoesNotPromoteAdmission = refl

------------------------------------------------------------------------
-- 7. Signed Base369 symmetries.  Flipping source or target coordinates swaps
--    the selected endpoint coding exactly.  Flipping the admissibility axis
--    exchanges reject/admit and fixes unresolved as geometry only; it is NOT a
--    semantic theorem that evidence negation is valid.
------------------------------------------------------------------------

flipConstructorOnMF :
  Signed.flipX mfAdmittedPoint ≡ ffAdmittedPoint
flipConstructorOnMF = refl

flipConstructedOnMF :
  Signed.flipY mfAdmittedPoint ≡ mmAdmittedPoint
flipConstructedOnMF = refl

flipAdmissibilityOnMF :
  Signed.flipZ mfAdmittedPoint ≡ arrowPoint mf rejectedPath
flipAdmissibilityOnMF = refl

unresolvedAdmissibilityFixedByReflection :
  Signed.flipZ mfUnresolvedPoint ≡ mfUnresolvedPoint
unresolvedAdmissibilityFixedByReflection = refl

------------------------------------------------------------------------
-- 8. Spectral / Monster seam.  The canonical Base369 owner already proves
--    coordinate reflection -> C3 frequency conjugation -> Monster 3B phase
--    inversion at the phase-intertwiner level.  We reuse that exact theorem as
--    a structural witness only.
------------------------------------------------------------------------

base369MonsterReflectionIntertwiner =
  Signed.monsterAxisReflectionIntertwines

frequencyConjugationRemainsInvolutive :
  (f : Spectral.AxisFrequency) →
  Spectral.conjugateFrequency (Spectral.conjugateFrequency f) ≡ f
frequencyConjugationRemainsInvolutive = Spectral.conjugateFrequencyInvolutive

------------------------------------------------------------------------
-- 9. No-promotion boundaries.
------------------------------------------------------------------------

data BinaryEndpointChartIsExhaustiveGenderOntology : Set where

data Base369CoordinateIsHistoricalEssence : Set where

data AdmissibilityReflectionIsLogicalNegation : Set where

data HistoricalPathCategoryIsMonsterRepresentation : Set where

data HistoricalOrderDefectIsGaugeCurvature : Set where

data SharedTernaryCarrierCreatesCrossDomainAuthority : Set where

binaryEndpointChartDoesNotExhaustGenderOntology :
  BinaryEndpointChartIsExhaustiveGenderOntology → ⊥
binaryEndpointChartDoesNotExhaustGenderOntology ()

base369CoordinateDoesNotCreateHistoricalEssence :
  Base369CoordinateIsHistoricalEssence → ⊥
base369CoordinateDoesNotCreateHistoricalEssence ()

admissibilityReflectionDoesNotCreateLogicalNegation :
  AdmissibilityReflectionIsLogicalNegation → ⊥
admissibilityReflectionDoesNotCreateLogicalNegation ()

historicalPathCategoryDoesNotBecomeMonsterRepresentation :
  HistoricalPathCategoryIsMonsterRepresentation → ⊥
historicalPathCategoryDoesNotBecomeMonsterRepresentation ()

historicalOrderDefectDoesNotBecomeGaugeCurvature :
  HistoricalOrderDefectIsGaugeCurvature → ⊥
historicalOrderDefectDoesNotBecomeGaugeCurvature ()

sharedTernaryCarrierDoesNotCreateCrossDomainAuthority :
  SharedTernaryCarrierCreatesCrossDomainAuthority → ⊥
sharedTernaryCarrierDoesNotCreateCrossDomainAuthority ()

binaryTernaryBoundaryStillAuthoritative :
  BT.BinaryOppositionExhaustsHistoricalPossibility → ⊥
binaryTernaryBoundaryStillAuthoritative =
  BT.binaryOppositionDoesNotExhaustHistoricalPossibility

record SexedHistoricalBase369TransitionPathBoundary : Set where
  constructor sexed-historical-base369-transition-path-boundary
  field
    finiteTwoObjectPathCategoryConstructed : Bool
    identitiesExact : Bool
    associativityExact : Bool
    admissibilityRemainsTernary : Bool
    fourAdmittedComparisonArrowsChartToCorners : Bool
    unresolvedAdmissibilityOccupiesCentralCoordinate : Bool
    coarseCrossCountRecoversComposite : Bool
    sourceTargetReflectionsExactOnCarrier : Bool
    reflectionImpliesHistoricalSemanticNegation : Bool
    monsterPhaseIntertwinerAvailableStructurally : Bool
    historicalCategoryIsMonsterRepresentation : Bool
    historicalOrderDefectIsGaugeCurvature : Bool
    binaryEndpointsExhaustGenderOntology : Bool

canonicalSexedHistoricalBase369TransitionPathBoundary :
  SexedHistoricalBase369TransitionPathBoundary
canonicalSexedHistoricalBase369TransitionPathBoundary =
  sexed-historical-base369-transition-path-boundary
    true true true true true true false true false true false false false
