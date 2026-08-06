module DASHI.Physics.Foundations.FiniteStressConservationGeodesicExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Signed finite current with exact vertex divergence.

data SignedFlux : Set where
  fluxMinusOne : SignedFlux
  fluxZero : SignedFlux
  fluxPlusOne : SignedFlux

negateFlux : SignedFlux → SignedFlux
negateFlux fluxMinusOne = fluxPlusOne
negateFlux fluxZero = fluxZero
negateFlux fluxPlusOne = fluxMinusOne

data DivergenceStatus : Set where
  divergenceZero : DivergenceStatus
  divergenceNonzero : DivergenceStatus

oppositeFluxesCancel : SignedFlux → SignedFlux → DivergenceStatus
oppositeFluxesCancel fluxMinusOne fluxPlusOne = divergenceZero
oppositeFluxesCancel fluxPlusOne fluxMinusOne = divergenceZero
oppositeFluxesCancel fluxZero fluxZero = divergenceZero
oppositeFluxesCancel _ _ = divergenceNonzero

record CycleCurrent : Set where
  constructor cycleCurrent
  field
    edge01Flux : SignedFlux
    edge12Flux : SignedFlux
    edge20Flux : SignedFlux

open CycleCurrent public

canonicalCycleCurrent : CycleCurrent
canonicalCycleCurrent =
  cycleCurrent fluxPlusOne fluxPlusOne fluxPlusOne

vertex0Divergence : CycleCurrent → DivergenceStatus
vertex0Divergence current =
  oppositeFluxesCancel
    (edge01Flux current)
    (negateFlux (edge20Flux current))

vertex1Divergence : CycleCurrent → DivergenceStatus
vertex1Divergence current =
  oppositeFluxesCancel
    (edge12Flux current)
    (negateFlux (edge01Flux current))

vertex2Divergence : CycleCurrent → DivergenceStatus
vertex2Divergence current =
  oppositeFluxesCancel
    (edge20Flux current)
    (negateFlux (edge12Flux current))

canonicalCurrentIsConservedAtEveryVertex :
  vertex0Divergence canonicalCycleCurrent ≡ divergenceZero
  ×
  vertex1Divergence canonicalCycleCurrent ≡ divergenceZero
  ×
  vertex2Divergence canonicalCycleCurrent ≡ divergenceZero
canonicalCurrentIsConservedAtEveryVertex = refl , (refl , refl)

------------------------------------------------------------------------
-- Geometry-dependent path cost.

data PathCandidate : Set where
  upperPath : PathCandidate
  lowerPath : PathCandidate

data GeometryProfile : Set where
  symmetricGeometry : GeometryProfile
  upperPathLoadedGeometry : GeometryProfile

pathCost : GeometryProfile → PathCandidate → Nat
pathCost symmetricGeometry upperPath = 2
pathCost symmetricGeometry lowerPath = 2
pathCost upperPathLoadedGeometry upperPath = 5
pathCost upperPathLoadedGeometry lowerPath = 3

data SelectedPathClass : Set where
  degeneratePathClass : SelectedPathClass
  upperSelected : SelectedPathClass
  lowerSelected : SelectedPathClass

selectPath : GeometryProfile → SelectedPathClass
selectPath symmetricGeometry = degeneratePathClass
selectPath upperPathLoadedGeometry = lowerSelected

symmetricGeometryLeavesPathDegenerate :
  selectPath symmetricGeometry ≡ degeneratePathClass
symmetricGeometryLeavesPathDegenerate = refl

loadedGeometryChangesPathSelection :
  selectPath upperPathLoadedGeometry ≡ lowerSelected
loadedGeometryChangesPathSelection = refl

------------------------------------------------------------------------
-- Two-way finite backreaction: geometry changes path selection and the matter
-- path changes the next geometry candidate.

geometryUpdateFromMatter : PathCandidate → GeometryProfile
geometryUpdateFromMatter upperPath = upperPathLoadedGeometry
geometryUpdateFromMatter lowerPath = symmetricGeometry

upperMatterPathLoadsUpperGeometry :
  geometryUpdateFromMatter upperPath ≡ upperPathLoadedGeometry
upperMatterPathLoadsUpperGeometry = refl

record ClosedBackreactionStep : Set where
  constructor closedBackreactionStep
  field
    currentGeometry : GeometryProfile
    selectedMatterPath : SelectedPathClass
    nextGeometry : GeometryProfile

canonicalBackreactionStep : ClosedBackreactionStep
canonicalBackreactionStep =
  closedBackreactionStep
    upperPathLoadedGeometry
    lowerSelected
    symmetricGeometry

------------------------------------------------------------------------
-- Authority boundary.

record FiniteStressGeodesicBoundary : Set where
  constructor finiteStressGeodesicBoundary
  field
    graphCurrentConservationIsCovariantBianchiIdentity : Bool
    graphCurrentConservationIsCovariantBianchiIdentityIsFalse :
      graphCurrentConservationIsCovariantBianchiIdentity ≡ false

    finitePathCostIsLorentzianGeodesicEquation : Bool
    finitePathCostIsLorentzianGeodesicEquationIsFalse :
      finitePathCostIsLorentzianGeodesicEquation ≡ false

    matterDependentPathCostProvesEquivalencePrinciple : Bool
    matterDependentPathCostProvesEquivalencePrincipleIsFalse :
      matterDependentPathCostProvesEquivalencePrinciple ≡ false

    closedFiniteUpdateProvesSemiclassicalEinsteinEquation : Bool
    closedFiniteUpdateProvesSemiclassicalEinsteinEquationIsFalse :
      closedFiniteUpdateProvesSemiclassicalEinsteinEquation ≡ false

open FiniteStressGeodesicBoundary public

canonicalFiniteStressGeodesicBoundary : FiniteStressGeodesicBoundary
canonicalFiniteStressGeodesicBoundary =
  finiteStressGeodesicBoundary false refl false refl false refl false refl
