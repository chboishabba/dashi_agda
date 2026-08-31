module DASHI.Physics.Closure.NSCriticalConeResidualFibre369CrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.ResidualObserverDependencyExact as Residual
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Physics.Closure.NSTriadKNHighestAlphaFrontierRound285Exact as NS285

------------------------------------------------------------------------
-- NS CRITICAL-CONE RESIDUAL FIBRE / 369 CROSS-POLLINATION
--
-- Repository-native finite witness of the generic information geometry that the
-- Base369/Monster work made prominent: a coarse carrier may identify states
-- whose fine phase/residual coordinate differs.  This fixture is NOT asserted
-- to be a Navier-Stokes solution.  It proves only that a shell observer cannot
-- generically reconstruct an independent signed-coherence coordinate.
------------------------------------------------------------------------

data CriticalConeState : Set where
  sameShellPositiveCoherence
  sameShellNegativeCoherence
  : CriticalConeState

data ProbeAction : Set where inspectSignedCoherence : ProbeAction

data InteractionIndex : Set where criticalConeIndex : InteractionIndex

data SignedResidualCode : Set where positiveResidual negativeResidual : SignedResidualCode

data CoarseShellCode : Set where sameCriticalShell : CoarseShellCode

coarseShellObserver : Observer.Observer CriticalConeState CoarseShellCode
coarseShellObserver _ = sameCriticalShell

dependencyCode : CriticalConeState → ProbeAction → SignedResidualCode
dependencyCode sameShellPositiveCoherence inspectSignedCoherence = positiveResidual
dependencyCode sameShellNegativeCoherence inspectSignedCoherence = negativeResidual

signedResidualDependency :
  Residual.ResidualDependencyObserver
    CriticalConeState ProbeAction InteractionIndex SignedResidualCode
signedResidualDependency = record
  { Influences = λ _ _ _ _ → ⊤
  ; dependencyCode = dependencyCode
  }

positiveNegativeResidualDistinct : positiveResidual ≡ negativeResidual → ⊥
positiveNegativeResidualDistinct ()

sameShellHidesSignedResidual :
  Residual.HiddenResidualDependency
    signedResidualDependency coarseShellObserver inspectSignedCoherence
sameShellHidesSignedResidual =
  Residual.hiddenResidualDependency
    sameShellPositiveCoherence
    sameShellNegativeCoherence
    refl
    positiveNegativeResidualDistinct

shellPlusResidualStrictlyRefinesShell :
  Observer.StrictRefinement
    coarseShellObserver
    (Residual.refinedObservationAt
      signedResidualDependency coarseShellObserver inspectSignedCoherence)
shellPlusResidualStrictlyRefinesShell =
  Residual.hiddenResidualDependencyGivesStrictRefinement sameShellHidesSignedResidual

signedResidualCannotDescendThroughShellObserver :
  Residual.DependencyCodeDescendsAt
    signedResidualDependency coarseShellObserver inspectSignedCoherence → ⊥
signedResidualCannotDescendThroughShellObserver =
  Residual.hiddenResidualDependencyBlocksDescent sameShellHidesSignedResidual

------------------------------------------------------------------------
-- Connection to the actual NS frontier is status-only and exact.
------------------------------------------------------------------------

round285ConstantBandShellLocalizationInsufficient :
  NS285.round285ConstantBandLocalizationSufficesForCriticalCone ≡ false
round285ConstantBandShellLocalizationInsufficient = refl

round285SignedCovarianceStillOpen :
  NS285.round285PhysicalCriticalConeSignedCovarianceClosed ≡ false
round285SignedCovarianceStillOpen =
  NS285.round285PhysicalCriticalConeSignedCovarianceClosedIsFalse

record NSResidualFibreBoundary : Set where
  constructor nsResidualFibreBoundary
  field
    coarseShellCanHideIndependentSignedResidual : Bool
    coarseShellCanHideIndependentSignedResidualIsTrue :
      coarseShellCanHideIndependentSignedResidual ≡ true
    finiteFixtureIsPhysicalNSSolution : Bool
    finiteFixtureIsPhysicalNSSolutionIsFalse :
      finiteFixtureIsPhysicalNSSolution ≡ false
    residualFibreAutomaticallyProvesSignedCovariance : Bool
    residualFibreAutomaticallyProvesSignedCovarianceIsFalse :
      residualFibreAutomaticallyProvesSignedCovariance ≡ false
    physicalProducerMustUsePhaseHelicityConvolutionStructure : Bool
    physicalProducerMustUsePhaseHelicityConvolutionStructureIsTrue :
      physicalProducerMustUsePhaseHelicityConvolutionStructure ≡ true

canonicalNSResidualFibreBoundary : NSResidualFibreBoundary
canonicalNSResidualFibreBoundary =
  nsResidualFibreBoundary true refl false refl false refl true refl
