module DASHI.Biology.D4IrrepPhysicalRoleExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Symmetry
import DASHI.Biology.EquivariantLaplacianSectorExact as Equivariant

------------------------------------------------------------------------
-- Semantic roles of the five D4 irrep species used by the 3 x 3 sheet.
-- These are representation-theoretic mode roles, not claims that the same
-- concrete irrep realizes every listed physical application.

data D4ModeRole : Set where
  invariantGlobalRole : D4ModeRole
  orientationPseudoscalarRole : D4ModeRole
  axialContrastRole : D4ModeRole
  diagonalContrastRole : D4ModeRole
  directionalPairRole : D4ModeRole

modeRole : Symmetry.D4IrrepKind → D4ModeRole
modeRole Symmetry.A1 = invariantGlobalRole
modeRole Symmetry.A2 = orientationPseudoscalarRole
modeRole Symmetry.B1 = axialContrastRole
modeRole Symmetry.B2 = diagonalContrastRole
modeRole Symmetry.E2 = directionalPairRole

roleDimension : D4ModeRole → Nat
roleDimension invariantGlobalRole = 1
roleDimension orientationPseudoscalarRole = 1
roleDimension axialContrastRole = 1
roleDimension diagonalContrastRole = 1
roleDimension directionalPairRole = 2

roleDimensionMatchesIrrep :
  (kind : Symmetry.D4IrrepKind) →
  roleDimension (modeRole kind) ≡ Symmetry.irrepDimension kind
roleDimensionMatchesIrrep Symmetry.A1 = refl
roleDimensionMatchesIrrep Symmetry.A2 = refl
roleDimensionMatchesIrrep Symmetry.B1 = refl
roleDimensionMatchesIrrep Symmetry.B2 = refl
roleDimensionMatchesIrrep Symmetry.E2 = refl

------------------------------------------------------------------------
-- Candidate readings in the different lanes discussed in the thread.

data CandidateInterpretation : Set where
  globalOrVacuumCandidate : CandidateInterpretation
  chiralityOrCirculationCandidate : CandidateInterpretation
  axialStrainCandidate : CandidateInterpretation
  diagonalShearCandidate : CandidateInterpretation
  directionalDegeneratePairCandidate : CandidateInterpretation
  gaugeInvariantCandidate : CandidateInterpretation
  learnedSymmetryFeatureCandidate : CandidateInterpretation

record SectorApplication : Set where
  constructor sectorApplication
  field
    irrep : Symmetry.D4IrrepKind
    orientation : Symmetry.DialecticalOrientation
    lane : Equivariant.ApplicationLane
    interpretation : CandidateInterpretation
    promotedAsConcretePhysicalIdentification : Bool

open SectorApplication public

DASHIInvariantSector : SectorApplication
DASHIInvariantSector =
  sectorApplication
    Symmetry.A1
    Symmetry.positiveOrientation
    Equivariant.grokkingRepresentationLane
    learnedSymmetryFeatureCandidate
    false

quantumVacuumCandidate : SectorApplication
quantumVacuumCandidate =
  sectorApplication
    Symmetry.A1
    Symmetry.positiveOrientation
    Equivariant.quantumExcitationLane
    globalOrVacuumCandidate
    false

navierStokesPositiveHelicityCandidate : SectorApplication
navierStokesPositiveHelicityCandidate =
  sectorApplication
    Symmetry.A2
    Symmetry.positiveOrientation
    Equivariant.navierStokesFourierLane
    chiralityOrCirculationCandidate
    false

navierStokesNegativeHelicityCandidate : SectorApplication
navierStokesNegativeHelicityCandidate =
  sectorApplication
    Symmetry.A2
    Symmetry.negativeOrientation
    Equivariant.navierStokesFourierLane
    chiralityOrCirculationCandidate
    false

yangMillsInvariantCandidate : SectorApplication
yangMillsInvariantCandidate =
  sectorApplication
    Symmetry.A1
    Symmetry.positiveOrientation
    Equivariant.yangMillsGaugeLane
    gaugeInvariantCandidate
    false

neuralDirectionalPairCandidate : SectorApplication
neuralDirectionalPairCandidate =
  sectorApplication
    Symmetry.E2
    Symmetry.positiveOrientation
    Equivariant.neuralLaplacianLane
    directionalDegeneratePairCandidate
    false

positiveAndNegativeHelicityUseOppositeOrientations :
  orientation navierStokesPositiveHelicityCandidate
  ≡ Symmetry.positiveOrientation
  × orientation navierStokesNegativeHelicityCandidate
    ≡ Symmetry.negativeOrientation
positiveAndNegativeHelicityUseOppositeOrientations = refl , refl

rawNineCellCarrierDoesNotSupplyA2 : Symmetry.rawNineMultiplicity Symmetry.A2 ≡ 0
rawNineCellCarrierDoesNotSupplyA2 = refl

A2RequiresOrientedRefinementCandidate :
  modeRole Symmetry.A2 ≡ orientationPseudoscalarRole
A2RequiresOrientedRefinementCandidate = refl

record D4IrrepPhysicalRoleBoundary : Set where
  constructor d4IrrepPhysicalRoleBoundary
  field
    sameIrrepNameMeansSameConcretePhysicsAcrossLanes : Bool
    sameIrrepNameMeansSameConcretePhysicsAcrossLanesIsFalse :
      sameIrrepNameMeansSameConcretePhysicsAcrossLanes ≡ false

    candidateParticleSectorDerivesBornRule : Bool
    candidateParticleSectorDerivesBornRuleIsFalse :
      candidateParticleSectorDerivesBornRule ≡ false

    helicityCandidateProvesNavierStokesRegularity : Bool
    helicityCandidateProvesNavierStokesRegularityIsFalse :
      helicityCandidateProvesNavierStokesRegularity ≡ false

    gaugeInvariantCandidateProvesYangMillsMassGap : Bool
    gaugeInvariantCandidateProvesYangMillsMassGapIsFalse :
      gaugeInvariantCandidateProvesYangMillsMassGap ≡ false

    orientedIrrepRolesProvideReusableModeTyping : Bool
    orientedIrrepRolesProvideReusableModeTypingIsTrue :
      orientedIrrepRolesProvideReusableModeTyping ≡ true

open D4IrrepPhysicalRoleBoundary public

canonicalD4IrrepPhysicalRoleBoundary : D4IrrepPhysicalRoleBoundary
canonicalD4IrrepPhysicalRoleBoundary =
  d4IrrepPhysicalRoleBoundary false refl false refl false refl false refl true refl
