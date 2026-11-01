module DASHI.Physics.Closure.CarrierNSSmoothConvergenceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Closure.MillenniumTowerNavierStokesInstanceReceipt as NSInstance
import DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt as NSTower
import DASHI.Physics.Closure.UltrametricSobolevUniformBound as Sobolev

------------------------------------------------------------------------
-- Carrier Navier-Stokes smooth convergence frontier receipt.
--
-- This receipt names the exact Navier-Stokes frontier left after the
-- finite-depth regularity ladder and ultrametric Sobolev uniformity:
-- construct a compactness/convergence theorem strong enough to pass the
-- carrier solutions to a smooth continuum solution.  It does not prove that
-- theorem and it does not promote Clay Navier-Stokes.

data CarrierNSDepthSolution (depth : Nat) : Set where
  finiteDepthCarrierNSSolution :
    CarrierNSDepthSolution depth

data CarrierCinftyNormTarget : Set where
  continuumTimeCinftyNormTarget :
    CarrierCinftyNormTarget

data CarrierNSSequenceCauchyFrontier : Set where
  cauchyInCinftyStillOpen :
    CarrierNSSequenceCauchyFrontier

data ContinuumSmoothNSLimitFrontier : Set where
  smoothContinuumNSLimitStillOpen :
    ContinuumSmoothNSLimitFrontier

data CarrierNSAubinLionsPrerequisite : Set where
  lerayEnergyBoundPrerequisite :
    CarrierNSAubinLionsPrerequisite

  ultrametricSobolevUniformityPrerequisite :
    CarrierNSAubinLionsPrerequisite

  nsEquationTimeDerivativeBoundPrerequisite :
    CarrierNSAubinLionsPrerequisite

  ultrametricAubinLionsCompactnessPrerequisite :
    CarrierNSAubinLionsPrerequisite

canonicalCarrierNSAubinLionsPrerequisites :
  List CarrierNSAubinLionsPrerequisite
canonicalCarrierNSAubinLionsPrerequisites =
  lerayEnergyBoundPrerequisite
  ∷ ultrametricSobolevUniformityPrerequisite
  ∷ nsEquationTimeDerivativeBoundPrerequisite
  ∷ ultrametricAubinLionsCompactnessPrerequisite
  ∷ []

data CarrierNSAubinLionsPrerequisiteStatus : Set where
  derivableFromExistingFiniteReceipt :
    CarrierNSAubinLionsPrerequisiteStatus

  derivableTargetFromNSEquation :
    CarrierNSAubinLionsPrerequisiteStatus

  falseOpenAuthorityBoundary :
    CarrierNSAubinLionsPrerequisiteStatus

ultrametricAubinLionsCitation :
  Authority.CitationAuthorityBoundary
ultrametricAubinLionsCitation =
  Authority.mkAuthorityBoundary
    Authority.CitationAuthority
    refl
    "Ultrametric Aubin-Lions compactness authority boundary"
    "Aubin-Lions compactness plus Taibleson p-adic Sobolev theory; carrier specialization remains an open theorem"
    true
    false
    false
    ( "CitationAuthority only: records the external compactness-method boundary"
      ∷ "No ultrametric Aubin-Lions theorem for the carrier tower is proved here"
      ∷ "No continuum smooth Navier-Stokes solution is constructed by this receipt"
      ∷ []
    )

ultrametricAubinLionsNoArtifact :
  Authority.CitationAuthorityNoArtifact
ultrametricAubinLionsNoArtifact =
  Authority.mkCitationAuthorityNoArtifact
    ultrametricAubinLionsCitation
    refl
    refl
    refl

record CarrierNSAubinLionsPrerequisiteChain : Setω where
  field
    prerequisites :
      List CarrierNSAubinLionsPrerequisite

    prerequisitesAreCanonical :
      prerequisites ≡ canonicalCarrierNSAubinLionsPrerequisites

    regularityTower :
      NSTower.NavierStokesRegularityTowerReceipt

    ultrametricSobolevReceipt :
      Sobolev.UltrametricSobolevUniformBoundReceipt

    lerayEnergyBoundStatus :
      CarrierNSAubinLionsPrerequisiteStatus

    lerayEnergyBoundStatusIsFiniteReceipt :
      lerayEnergyBoundStatus ≡ derivableFromExistingFiniteReceipt

    lerayEnergyBoundRecorded :
      Bool

    lerayEnergyBoundRecordedIsTrue :
      lerayEnergyBoundRecorded ≡ true

    lerayEnergyBoundFromTower :
      NSTower.finiteDepthEnergyEstimateRecorded
        (NSTower.finiteDepthL2EnergyEstimateAtEveryDepth regularityTower zero)
      ≡
      true

    lerayEnergyDoesNotPromoteContinuum :
      NSTower.continuumRegularityPromotedByEnergyEstimate
        (NSTower.finiteDepthL2EnergyEstimateAtEveryDepth regularityTower zero)
      ≡
      false

    ultrametricSobolevStatus :
      CarrierNSAubinLionsPrerequisiteStatus

    ultrametricSobolevStatusIsFiniteReceipt :
      ultrametricSobolevStatus ≡ derivableFromExistingFiniteReceipt

    ultrametricSobolevUniformityRecorded :
      Bool

    ultrametricSobolevUniformityRecordedIsTrue :
      ultrametricSobolevUniformityRecorded ≡ true

    ultrametricSobolevUniformityFromReceipt :
      Sobolev.ultrametricSobolevUniformBounded ultrametricSobolevReceipt
      ≡
      true

    nsEquationTimeDerivativeBoundStatus :
      CarrierNSAubinLionsPrerequisiteStatus

    nsEquationTimeDerivativeBoundStatusIsTarget :
      nsEquationTimeDerivativeBoundStatus ≡ derivableTargetFromNSEquation

    nsEquationTimeDerivativeBoundDerivableTarget :
      Bool

    nsEquationTimeDerivativeBoundDerivableTargetIsTrue :
      nsEquationTimeDerivativeBoundDerivableTarget ≡ true

    nsEquationTimeDerivativeBoundConstructedHere :
      Bool

    nsEquationTimeDerivativeBoundConstructedHereIsFalse :
      nsEquationTimeDerivativeBoundConstructedHere ≡ false

    ultrametricAubinLionsStatus :
      CarrierNSAubinLionsPrerequisiteStatus

    ultrametricAubinLionsStatusIsFalseOpen :
      ultrametricAubinLionsStatus ≡ falseOpenAuthorityBoundary

    ultrametricAubinLionsConstructedHere :
      Bool

    ultrametricAubinLionsConstructedHereIsFalse :
      ultrametricAubinLionsConstructedHere ≡ false

    smoothConvergenceConstructedFromChain :
      Bool

    smoothConvergenceConstructedFromChainIsFalse :
      smoothConvergenceConstructedFromChain ≡ false

    clayNavierStokesPromotedFromChain :
      Bool

    clayNavierStokesPromotedFromChainIsFalse :
      clayNavierStokesPromotedFromChain ≡ false

    chainNotes :
      List String

open CarrierNSAubinLionsPrerequisiteChain public

canonicalCarrierNSAubinLionsPrerequisiteChain :
  CarrierNSAubinLionsPrerequisiteChain
canonicalCarrierNSAubinLionsPrerequisiteChain =
  record
    { prerequisites =
        canonicalCarrierNSAubinLionsPrerequisites
    ; prerequisitesAreCanonical =
        refl
    ; regularityTower =
        NSTower.canonicalNavierStokesRegularityTowerReceipt
    ; ultrametricSobolevReceipt =
        Sobolev.canonicalUltrametricSobolevUniformBoundReceipt
    ; lerayEnergyBoundStatus =
        derivableFromExistingFiniteReceipt
    ; lerayEnergyBoundStatusIsFiniteReceipt =
        refl
    ; lerayEnergyBoundRecorded =
        true
    ; lerayEnergyBoundRecordedIsTrue =
        refl
    ; lerayEnergyBoundFromTower =
        refl
    ; lerayEnergyDoesNotPromoteContinuum =
        refl
    ; ultrametricSobolevStatus =
        derivableFromExistingFiniteReceipt
    ; ultrametricSobolevStatusIsFiniteReceipt =
        refl
    ; ultrametricSobolevUniformityRecorded =
        true
    ; ultrametricSobolevUniformityRecordedIsTrue =
        refl
    ; ultrametricSobolevUniformityFromReceipt =
        refl
    ; nsEquationTimeDerivativeBoundStatus =
        derivableTargetFromNSEquation
    ; nsEquationTimeDerivativeBoundStatusIsTarget =
        refl
    ; nsEquationTimeDerivativeBoundDerivableTarget =
        true
    ; nsEquationTimeDerivativeBoundDerivableTargetIsTrue =
        refl
    ; nsEquationTimeDerivativeBoundConstructedHere =
        false
    ; nsEquationTimeDerivativeBoundConstructedHereIsFalse =
        refl
    ; ultrametricAubinLionsStatus =
        falseOpenAuthorityBoundary
    ; ultrametricAubinLionsStatusIsFalseOpen =
        refl
    ; ultrametricAubinLionsConstructedHere =
        false
    ; ultrametricAubinLionsConstructedHereIsFalse =
        refl
    ; smoothConvergenceConstructedFromChain =
        false
    ; smoothConvergenceConstructedFromChainIsFalse =
        refl
    ; clayNavierStokesPromotedFromChain =
        false
    ; clayNavierStokesPromotedFromChainIsFalse =
        refl
    ; chainNotes =
        "Aubin-Lions prerequisite chain: finite Leray/L2 energy bound is consumed from NavierStokesRegularityTowerReceipt"
        ∷ "Ultrametric Sobolev uniformity is consumed from UltrametricSobolevUniformBound"
        ∷ "The Navier-Stokes equation time-derivative bound is recorded as a derivable target, not constructed here"
        ∷ "The carrier-specialized ultrametric Aubin-Lions compactness theorem remains false/open"
        ∷ "Smooth convergence and Clay Navier-Stokes promotion remain false"
        ∷ []
    }

record CarrierNSSmoothConvergenceReceipt : Setω where
  field
    nsTowerInstance :
      NSInstance.MillenniumTowerNavierStokesInstanceReceipt

    finiteBKMRecorded :
      NSInstance.finiteBKMRecorded nsTowerInstance ≡ true

    regularityTower :
      NSTower.NavierStokesRegularityTowerReceipt

    ultrametricSobolevReceipt :
      Sobolev.UltrametricSobolevUniformBoundReceipt

    ultrametricSobolevUniformityAvailable :
      Sobolev.ultrametricSobolevUniformBounded ultrametricSobolevReceipt
      ≡
      true

    aubinLionsPrerequisiteChainRecorded :
      Bool

    aubinLionsPrerequisitesAreCanonical :
      Bool

    aubinLionsPrerequisitesAreCanonicalIsTrue :
      aubinLionsPrerequisitesAreCanonical ≡ true

    sampleDepth :
      Nat

    sampleCarrierSolution :
      CarrierNSDepthSolution sampleDepth

    cinftyNormTarget :
      CarrierCinftyNormTarget

    carrierNSSequenceCauchyFrontier :
      CarrierNSSequenceCauchyFrontier

    carrierNSSequenceCauchyOpen :
      Bool

    carrierNSSequenceCauchyOpenIsTrue :
      carrierNSSequenceCauchyOpen ≡ true

    continuumSmoothNSLimitFrontier :
      ContinuumSmoothNSLimitFrontier

    continuumSmoothNSLimitOpen :
      Bool

    continuumSmoothNSLimitOpenIsTrue :
      continuumSmoothNSLimitOpen ≡ true

    ultrametricAubinLionsAuthorityBoundary :
      Authority.CitationAuthorityBoundary

    ultrametricAubinLionsAuthorityNoArtifact :
      Authority.CitationAuthorityNoArtifact

    finiteDepthEnstrophyControlAvailable :
      Bool

    finiteDepthEnstrophyControlAvailableIsTrue :
      finiteDepthEnstrophyControlAvailable ≡ true

    finiteDepthRegularityControlStrengthened :
      Bool

    finiteDepthRegularityControlStrengthenedIsTrue :
      finiteDepthRegularityControlStrengthened ≡ true

    regularityTowerContinuumLiftStillFalse :
      NSTower.continuumRegularityLiftConstructed regularityTower
      ≡
      false

    enstrophyBoundSufficesForSmoothContinuumLimit :
      Bool

    enstrophyBoundSufficesForSmoothContinuumLimitIsFalse :
      enstrophyBoundSufficesForSmoothContinuumLimit ≡ false

    carrierNSSequenceCauchyConstructedHere :
      Bool

    carrierNSSequenceCauchyConstructedHereIsFalse :
      carrierNSSequenceCauchyConstructedHere ≡ false

    limitIsSmoothNSSolutionConstructedHere :
      Bool

    limitIsSmoothNSSolutionConstructedHereIsFalse :
      limitIsSmoothNSSolutionConstructedHere ≡ false

    clayNSSmoothnessClosed :
      Bool

    clayNSSmoothnessClosedIsFalse :
      clayNSSmoothnessClosed ≡ false

    receiptNotes :
      List String

open CarrierNSSmoothConvergenceReceipt public

canonicalCarrierNSSmoothConvergenceReceipt :
  CarrierNSSmoothConvergenceReceipt
canonicalCarrierNSSmoothConvergenceReceipt =
  record
    { nsTowerInstance =
        NSInstance.canonicalMillenniumTowerNavierStokesInstanceReceipt
    ; finiteBKMRecorded =
        refl
    ; regularityTower =
        NSTower.canonicalNavierStokesRegularityTowerReceipt
    ; ultrametricSobolevReceipt =
        Sobolev.canonicalUltrametricSobolevUniformBoundReceipt
    ; ultrametricSobolevUniformityAvailable =
        refl
    ; aubinLionsPrerequisiteChainRecorded =
        true
    ; aubinLionsPrerequisitesAreCanonical =
        true
    ; aubinLionsPrerequisitesAreCanonicalIsTrue =
        refl
    ; sampleDepth =
        suc zero
    ; sampleCarrierSolution =
        finiteDepthCarrierNSSolution
    ; cinftyNormTarget =
        continuumTimeCinftyNormTarget
    ; carrierNSSequenceCauchyFrontier =
        cauchyInCinftyStillOpen
    ; carrierNSSequenceCauchyOpen =
        true
    ; carrierNSSequenceCauchyOpenIsTrue =
        refl
    ; continuumSmoothNSLimitFrontier =
        smoothContinuumNSLimitStillOpen
    ; continuumSmoothNSLimitOpen =
        true
    ; continuumSmoothNSLimitOpenIsTrue =
        refl
    ; ultrametricAubinLionsAuthorityBoundary =
        ultrametricAubinLionsCitation
    ; ultrametricAubinLionsAuthorityNoArtifact =
        ultrametricAubinLionsNoArtifact
    ; finiteDepthEnstrophyControlAvailable =
        true
    ; finiteDepthEnstrophyControlAvailableIsTrue =
        refl
    ; finiteDepthRegularityControlStrengthened =
        true
    ; finiteDepthRegularityControlStrengthenedIsTrue =
        refl
    ; regularityTowerContinuumLiftStillFalse =
        refl
    ; enstrophyBoundSufficesForSmoothContinuumLimit =
        false
    ; enstrophyBoundSufficesForSmoothContinuumLimitIsFalse =
        refl
    ; carrierNSSequenceCauchyConstructedHere =
        false
    ; carrierNSSequenceCauchyConstructedHereIsFalse =
        refl
    ; limitIsSmoothNSSolutionConstructedHere =
        false
    ; limitIsSmoothNSSolutionConstructedHereIsFalse =
        refl
    ; clayNSSmoothnessClosed =
        false
    ; clayNSSmoothnessClosedIsFalse =
        refl
    ; receiptNotes =
        "Finite-depth NS enstrophy, Leray/L2 energy, regularity, BKM, and ultrametric Sobolev uniformity are consumed as strengthened internal prerequisites"
        ∷ "The Aubin-Lions prerequisite chain records Leray energy, ultrametric Sobolev uniformity, NS-equation time-derivative target, and false/open ultrametric compactness"
        ∷ "The open frontier is C-infinity Cauchy convergence of carrier NS solutions"
        ∷ "A carrier-specialized ultrametric Aubin-Lions compactness theorem is named as the authority boundary"
        ∷ "Finite enstrophy control is necessary but not sufficient for a smooth continuum Navier-Stokes solution"
        ∷ "Continuum smooth limit construction and Clay Navier-Stokes promotion remain false"
        ∷ []
    }

carrierNSSmoothConvergenceCauchyFrontierOpen :
  carrierNSSequenceCauchyOpen canonicalCarrierNSSmoothConvergenceReceipt
  ≡
  true
carrierNSSmoothConvergenceCauchyFrontierOpen =
  refl

carrierNSSmoothConvergenceContinuumLimitOpen :
  continuumSmoothNSLimitOpen canonicalCarrierNSSmoothConvergenceReceipt
  ≡
  true
carrierNSSmoothConvergenceContinuumLimitOpen =
  refl

enstrophyBoundDoesNotSufficeForSmoothLimit :
  enstrophyBoundSufficesForSmoothContinuumLimit
    canonicalCarrierNSSmoothConvergenceReceipt
  ≡
  false
enstrophyBoundDoesNotSufficeForSmoothLimit =
  refl

aubinLionsPrerequisiteChainCanonical :
  aubinLionsPrerequisiteChainRecorded
    canonicalCarrierNSSmoothConvergenceReceipt
  ≡
  true
aubinLionsPrerequisiteChainCanonical =
  refl

aubinLionsPrerequisiteChainCanonicalFlag :
  aubinLionsPrerequisitesAreCanonical
    canonicalCarrierNSSmoothConvergenceReceipt
  ≡
  true
aubinLionsPrerequisiteChainCanonicalFlag =
  refl

carrierNSLerayEnergyBoundRecorded :
  lerayEnergyBoundRecorded canonicalCarrierNSAubinLionsPrerequisiteChain
  ≡
  true
carrierNSLerayEnergyBoundRecorded =
  refl

carrierNSUltrametricSobolevUniformityRecorded :
  ultrametricSobolevUniformityRecorded
    canonicalCarrierNSAubinLionsPrerequisiteChain
  ≡
  true
carrierNSUltrametricSobolevUniformityRecorded =
  refl

carrierNSTimeDerivativeBoundIsTarget :
  nsEquationTimeDerivativeBoundStatus
    canonicalCarrierNSAubinLionsPrerequisiteChain
  ≡
  derivableTargetFromNSEquation
carrierNSTimeDerivativeBoundIsTarget =
  refl

carrierNSTimeDerivativeBoundNotConstructedHere :
  nsEquationTimeDerivativeBoundConstructedHere
    canonicalCarrierNSAubinLionsPrerequisiteChain
  ≡
  false
carrierNSTimeDerivativeBoundNotConstructedHere =
  refl

carrierNSUltrametricAubinLionsFalseOpen :
  ultrametricAubinLionsConstructedHere
    canonicalCarrierNSAubinLionsPrerequisiteChain
  ≡
  false
carrierNSUltrametricAubinLionsFalseOpen =
  refl

carrierNSSmoothConvergenceDoesNotCloseClay :
  clayNSSmoothnessClosed canonicalCarrierNSSmoothConvergenceReceipt
  ≡
  false
carrierNSSmoothConvergenceDoesNotCloseClay =
  refl
