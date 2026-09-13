module DASHI.Physics.Closure.NSTriadKNClayCDDomainResidualBidiRound527Exact where

------------------------------------------------------------------------
-- ROUND527 / CLAY C/D = COMMON NS CORE + NON-ERASABLE DOMAIN RESIDUAL
--
-- R523 keeps Fefferman C and D source conditions distinct.  R526 shows that
-- physical R^3 and physical T^3 can share a 27-sign local Fourier observation
-- without becoming the same domain.  This owner makes that split bidirectional.
--
-- Shared C/D coordinates:
--   positive viscosity; dimension three; smooth divergence-free initial datum;
--   smooth forcing; exact Navier--Stokes equation; no-global-smooth-solution
--   target.
--
-- R^3 residual:
--   rapid initial spatial decay; rapid forcing space-time decay; bounded energy.
--
-- T^3 residual:
--   periodic initial datum; periodic forcing; rapid forcing time decay;
--   periodic-solution requirement.
--
-- Thus a common local/symmetry core can be compared once, while every theorem
-- transport between domains must retain/pay the residual envelope separately.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNClayForcedBreakdownFormulationRound523Exact as R523
import DASHI.Physics.Closure.NSTriadKNTorusEuclideanTernary27IntersectionRound526Exact as R526

data CommonClayCoordinate527 : Set where
  commonPositiveViscosity527 : CommonClayCoordinate527
  commonDimensionThree527 : CommonClayCoordinate527
  commonSmoothDivergenceFreeInitialDatum527 : CommonClayCoordinate527
  commonSmoothForcing527 : CommonClayCoordinate527
  commonExactNavierStokesEquation527 : CommonClayCoordinate527
  commonNoGlobalSmoothSolutionTarget527 : CommonClayCoordinate527

data DomainResidual527 : Set where
  r3RapidInitialSpatialDecay527 : DomainResidual527
  r3RapidForcingSpaceTimeDecay527 : DomainResidual527
  r3BoundedEnergy527 : DomainResidual527
  torusPeriodicInitialDatum527 : DomainResidual527
  torusPeriodicForcing527 : DomainResidual527
  torusRapidForcingTimeDecay527 : DomainResidual527
  torusPeriodicSolution527 : DomainResidual527

data DomainResidualFamily527 : Set where
  r3ResidualFamily527 : DomainResidualFamily527
  torusResidualFamily527 : DomainResidualFamily527

residualRequiredBy527 : DomainResidualFamily527 → DomainResidual527 → Bool
residualRequiredBy527 r3ResidualFamily527 r3RapidInitialSpatialDecay527 = true
residualRequiredBy527 r3ResidualFamily527 r3RapidForcingSpaceTimeDecay527 = true
residualRequiredBy527 r3ResidualFamily527 r3BoundedEnergy527 = true
residualRequiredBy527 r3ResidualFamily527 torusPeriodicInitialDatum527 = false
residualRequiredBy527 r3ResidualFamily527 torusPeriodicForcing527 = false
residualRequiredBy527 r3ResidualFamily527 torusRapidForcingTimeDecay527 = false
residualRequiredBy527 r3ResidualFamily527 torusPeriodicSolution527 = false
residualRequiredBy527 torusResidualFamily527 r3RapidInitialSpatialDecay527 = false
residualRequiredBy527 torusResidualFamily527 r3RapidForcingSpaceTimeDecay527 = false
residualRequiredBy527 torusResidualFamily527 r3BoundedEnergy527 = false
residualRequiredBy527 torusResidualFamily527 torusPeriodicInitialDatum527 = true
residualRequiredBy527 torusResidualFamily527 torusPeriodicForcing527 = true
residualRequiredBy527 torusResidualFamily527 torusRapidForcingTimeDecay527 = true
residualRequiredBy527 torusResidualFamily527 torusPeriodicSolution527 = true

alternativeToDomain527 : R523.ClayBreakdownAlternative523 → R526.PhysicalDomain526
alternativeToDomain527 R523.clayAlternativeC523 = R526.physicalEuclideanR3_526
alternativeToDomain527 R523.clayAlternativeD523 = R526.physicalPeriodicTorus3_526

alternativeToResidualFamily527 :
  R523.ClayBreakdownAlternative523 → DomainResidualFamily527
alternativeToResidualFamily527 R523.clayAlternativeC523 = r3ResidualFamily527
alternativeToResidualFamily527 R523.clayAlternativeD523 = torusResidualFamily527

-- Representation-level BIDI: the alternative determines common core + residual
-- family; conversely the domain residual family determines which C/D source
-- alternative is being targeted.  This is scheduling identity, not proof of its
-- individual source coordinates.
residualFamilyToAlternative527 :
  DomainResidualFamily527 → R523.ClayBreakdownAlternative523
residualFamilyToAlternative527 r3ResidualFamily527 = R523.clayAlternativeC523
residualFamilyToAlternative527 torusResidualFamily527 = R523.clayAlternativeD523

cResidualRoundTrip527 :
  residualFamilyToAlternative527
    (alternativeToResidualFamily527 R523.clayAlternativeC523)
  ≡ R523.clayAlternativeC523
cResidualRoundTrip527 = refl

dResidualRoundTrip527 :
  residualFamilyToAlternative527
    (alternativeToResidualFamily527 R523.clayAlternativeD523)
  ≡ R523.clayAlternativeD523
dResidualRoundTrip527 = refl

------------------------------------------------------------------------
-- Refinement of the local-27 collision.
------------------------------------------------------------------------

data DomainEnvelopeAnswer527 : Set where
  r3Envelope527 : DomainEnvelopeAnswer527
  torusEnvelope527 : DomainEnvelopeAnswer527

refinedDomainObserve527 : R526.DomainWorld526 → DomainEnvelopeAnswer527
refinedDomainObserve527 (R526.domain-world-526 sig R526.physicalEuclideanR3_526) = r3Envelope527
refinedDomainObserve527 (R526.domain-world-526 sig R526.physicalPeriodicTorus3_526) = torusEnvelope527

data SameDomainEnvelope527 : DomainEnvelopeAnswer527 → DomainEnvelopeAnswer527 → Set where
  sameDomainEnvelope527 : {x : DomainEnvelopeAnswer527} → SameDomainEnvelope527 x x

refinedDomainSeparates526Collision527 :
  SameDomainEnvelope527
    (refinedDomainObserve527 R526.r3World526)
    (refinedDomainObserve527 R526.torusWorld526) → ⊥
refinedDomainSeparates526Collision527 ()

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CommonCorePaysR3ResidualPermission527 : Set where
data CommonCorePaysTorusResidualPermission527 : Set where
data Local369SignaturePaysDomainResidualPermission527 : Set where

commonCoreDoesNotPayR3Residual527 : CommonCorePaysR3ResidualPermission527 → ⊥
commonCoreDoesNotPayR3Residual527 ()
commonCoreDoesNotPayTorusResidual527 : CommonCorePaysTorusResidualPermission527 → ⊥
commonCoreDoesNotPayTorusResidual527 ()
local369SignatureDoesNotPayDomainResidual527 :
  Local369SignaturePaysDomainResidualPermission527 → ⊥
local369SignatureDoesNotPayDomainResidual527 ()

round527ClayCDCommonCoreFactored : Bool
round527ClayCDCommonCoreFactored = true
round527DomainResidualRetained : Bool
round527DomainResidualRetained = true
round527Local369PaysDomainEnvelope : Bool
round527Local369PaysDomainEnvelope = false
round527ClayPromotion : Bool
round527ClayPromotion = false

round527ClayCDCommonCoreFactoredIsTrue : round527ClayCDCommonCoreFactored ≡ true
round527ClayCDCommonCoreFactoredIsTrue = refl
round527DomainResidualRetainedIsTrue : round527DomainResidualRetained ≡ true
round527DomainResidualRetainedIsTrue = refl
round527Local369PaysDomainEnvelopeIsFalse : round527Local369PaysDomainEnvelope ≡ false
round527Local369PaysDomainEnvelopeIsFalse = refl
round527ClayPromotionIsFalse : round527ClayPromotion ≡ false
round527ClayPromotionIsFalse = refl
