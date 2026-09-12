module DASHI.Physics.Closure.GeneralGRCosmologyQuantumGravityRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Geometry.DifferentialBianchiTheoremBoundary as Bianchi
import DASHI.Geometry.GeneralLeviCivitaTheoremBoundary as LeviCivita
import DASHI.Physics.Closure.ContinuumEinsteinMatterSolutionBoundary as Continuum
import DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact as DarkDimension
import DASHI.Physics.Closure.EmpiricalCosmologyValidationBoundary as Cosmology
import DASHI.Physics.Closure.QuantumGravityTheoryBoundary as QuantumGravity

------------------------------------------------------------------------
-- Regression surface: target interfaces exist while unsupported promotions stay
-- definitionally blocked.

leviCivitaStillOpenRegression :
  LeviCivita.generalExistenceConstructed
    LeviCivita.canonicalLeviCivitaPromotionBoundary
  ≡ false
leviCivitaStillOpenRegression =
  LeviCivita.canonicalGeneralLeviCivitaNotYetProved

secondBianchiStillOpenRegression :
  Bianchi.generalSecondBianchiProof
    Bianchi.canonicalBianchiPromotionBoundary
  ≡ false
secondBianchiStillOpenRegression =
  Bianchi.canonicalDifferentialBianchiNotYetProved

continuumSolutionStillOpenRegression :
  Continuum.smoothContinuumExistenceProved
    Continuum.canonicalContinuumSolutionPromotionBoundary
  ≡ false
continuumSolutionStillOpenRegression =
  Continuum.canonicalContinuumSolutionNotYetProved

empiricalCosmologyStillBlockedRegression :
  Cosmology.empiricalCosmologyClaimPermitted
    Cosmology.canonicalEmpiricalCosmologyPromotionBoundary
  ≡ false
empiricalCosmologyStillBlockedRegression =
  Cosmology.canonicalEmpiricalCosmologyBlocked

quantumGravityStillBlockedRegression :
  QuantumGravity.quantumGravityClaimPermitted
    QuantumGravity.canonicalQuantumGravityPromotionBoundary
  ≡ false
quantumGravityStillBlockedRegression =
  QuantumGravity.canonicalQuantumGravityBlocked

theoryOfEverythingStillBlockedRegression :
  QuantumGravity.theoryOfEverythingClaimPermitted
    QuantumGravity.canonicalQuantumGravityPromotionBoundary
  ≡ false
theoryOfEverythingStillBlockedRegression =
  QuantumGravity.canonicalTheoryOfEverythingBlocked

------------------------------------------------------------------------
-- Dark-Dimension specialization: a downstream model can be testable while the
-- upstream string-theory / theory-of-everything promotions remain blocked.
------------------------------------------------------------------------

darkDimensionTestableRegression :
  DarkDimension.modelHasFalsifiableTests
    DarkDimension.canonicalDarkDimensionPromotionStatus
  ≡ true
darkDimensionTestableRegression =
  DarkDimension.darkDimensionModelTestable

darkDimensionStringPromotionBlockedRegression :
  DarkDimension.stringTheoryPromotionPermitted
    DarkDimension.canonicalDarkDimensionPromotionStatus
  ≡ false
darkDimensionStringPromotionBlockedRegression =
  DarkDimension.stringTheoryPromotionBlocked

darkDimensionToEBlockedRegression :
  QuantumGravity.theoryOfEverythingClaimPermitted
    QuantumGravity.canonicalQuantumGravityPromotionBoundary
  ≡ false
darkDimensionToEBlockedRegression =
  DarkDimension.theoryOfEverythingPromotionStillBlocked
