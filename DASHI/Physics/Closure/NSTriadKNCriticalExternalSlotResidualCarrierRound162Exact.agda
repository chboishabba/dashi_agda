module DASHI.Physics.Closure.NSTriadKNCriticalExternalSlotResidualCarrierRound162Exact where

------------------------------------------------------------------------
-- ROUND162 / EXTERNAL SLOT FORCING = THREE LITERAL SELF-ORBIT-REMOVED FIBRES
--
-- Round161 separates the slot-defect energy forcing into self and external
-- owners.  Round111 already identifies the k-leg external force as the exact
-- output-fibre convolution after deleting the selected (p,q)/(q,p) self orbit.
--
-- The p/q energy legs are themselves literal physical incidences.  Applying
-- Round111 to those two incidences gives the same residual-carrier theorem for
-- all three forcing slots.  Therefore both normalized-curl external forcing
-- differences from R157/R159 can be rewritten on THREE explicit residual
-- incidence lists, with no opaque `N_full-N_self` subtraction left.
--
-- This is high leverage: the remaining external forcing-work owner is now back
-- on the exact finite carriers already used by the pure-commutator/Bony lane.
-- No analytic estimate or matching assumption is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≢_)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as R111
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNCriticalSecondSlotDifferenceTangentRound159Exact as R159

cong₃ :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
    (f : A → B → C → D) {x x' y y' z z'} →
  x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

record ThreeLegExternalResidualWitness
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) : Set where
  constructor three-leg-external-residual-witness
  field
    kMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)
    kSwapMember : Symmetry.swapTriad tau ∈ Audit.concreteTriadsAt system (Physical.k tau)
    kSwapDifferent : Symmetry.swapTriad tau ≢ tau
    pMember : Orbit.pEnergyLeg tau ∈ Audit.concreteTriadsAt system (Physical.k (Orbit.pEnergyLeg tau))
    pSwapMember : Symmetry.swapTriad (Orbit.pEnergyLeg tau) ∈ Audit.concreteTriadsAt system (Physical.k (Orbit.pEnergyLeg tau))
    pSwapDifferent : Symmetry.swapTriad (Orbit.pEnergyLeg tau) ≢ Orbit.pEnergyLeg tau
    qMember : Orbit.qEnergyLeg tau ∈ Audit.concreteTriadsAt system (Physical.k (Orbit.qEnergyLeg tau))
    qSwapMember : Symmetry.swapTriad (Orbit.qEnergyLeg tau) ∈ Audit.concreteTriadsAt system (Physical.k (Orbit.qEnergyLeg tau))
    qSwapDifferent : Symmetry.swapTriad (Orbit.qEnergyLeg tau) ≢ Orbit.qEnergyLeg tau

open ThreeLegExternalResidualWitness public

kResidualVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  ThreeLegExternalResidualWitness system tau → C3.Complex3 F
kResidualVector {system = system} {tau = tau} W =
  R111.externalResidualVector system tau (kMember W) (kSwapMember W) (kSwapDifferent W)

pResidualVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  ThreeLegExternalResidualWitness system tau → C3.Complex3 F
pResidualVector {system = system} {tau = tau} W =
  R111.externalResidualVector system (Orbit.pEnergyLeg tau)
    (pMember W) (pSwapMember W) (pSwapDifferent W)

qResidualVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {tau : Physical.PhysicalTriadIncidence} →
  ThreeLegExternalResidualWitness system tau → C3.Complex3 F
qResidualVector {system = system} {tau = tau} W =
  R111.externalResidualVector system (Orbit.qEnergyLeg tau)
    (qMember W) (qSwapMember W) (qSwapDifferent W)

externalForcingKIsResidualVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (W : ThreeLegExternalResidualWitness system tau) →
  R95.externalForcingK system tau ≡ kResidualVector W
externalForcingKIsResidualVector system tau W =
  R111.externalForcingKIsSelfOrbitRemovedOutputFibre system tau
    (kMember W) (kSwapMember W) (kSwapDifferent W)

externalForcingPIsResidualVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (W : ThreeLegExternalResidualWitness system tau) →
  R95.externalForcingP system tau ≡ pResidualVector W
externalForcingPIsResidualVector system tau W =
  R111.externalForcingKIsSelfOrbitRemovedOutputFibre system (Orbit.pEnergyLeg tau)
    (pMember W) (pSwapMember W) (pSwapDifferent W)

externalForcingQIsResidualVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (W : ThreeLegExternalResidualWitness system tau) →
  R95.externalForcingQ system tau ≡ qResidualVector W
externalForcingQIsResidualVector system tau W =
  R111.externalForcingKIsSelfOrbitRemovedOutputFibre system (Orbit.qEnergyLeg tau)
    (qMember W) (qSwapMember W) (qSwapDifferent W)

externalKQSlotForcingIsLiteralResidualFibres :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (W : ThreeLegExternalResidualWitness system tau) →
  let uK = Audit.velocityAt system (Physical.k tau)
      uP = Audit.velocityAt system (Physical.p tau)
      uQ = Audit.velocityAt system (Physical.q tau)
  in
  R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
    uK uP uQ (R95.externalForcingK system tau) (R95.externalForcingP system tau) (R95.externalForcingQ system tau)
  ≡ R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
    uK uP uQ (kResidualVector W) (pResidualVector W) (qResidualVector W)
externalKQSlotForcingIsLiteralResidualFibres {E = E} S system tau W =
  cong₃
    (R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
      (Audit.velocityAt system (Physical.k tau))
      (Audit.velocityAt system (Physical.p tau))
      (Audit.velocityAt system (Physical.q tau)))
    (externalForcingKIsResidualVector system tau W)
    (externalForcingPIsResidualVector system tau W)
    (externalForcingQIsResidualVector system tau W)

externalPQSlotForcingIsLiteralResidualFibres :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence)
    (W : ThreeLegExternalResidualWitness system tau) →
  let uK = Audit.velocityAt system (Physical.k tau)
      uP = Audit.velocityAt system (Physical.p tau)
      uQ = Audit.velocityAt system (Physical.q tau)
  in
  R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
    uK uP uQ (R95.externalForcingK system tau) (R95.externalForcingP system tau) (R95.externalForcingQ system tau)
  ≡ R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
    uK uP uQ (kResidualVector W) (pResidualVector W) (qResidualVector W)
externalPQSlotForcingIsLiteralResidualFibres {E = E} S system tau W =
  cong₃
    (R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
      (Audit.velocityAt system (Physical.k tau))
      (Audit.velocityAt system (Physical.p tau))
      (Audit.velocityAt system (Physical.q tau)))
    (externalForcingKIsResidualVector system tau W)
    (externalForcingPIsResidualVector system tau W)
    (externalForcingQIsResidualVector system tau W)

round162ThreeLegExternalForcingResidualCarrierClosed : Bool
round162ThreeLegExternalForcingResidualCarrierClosed = true
round162BothExternalSlotForcingDifferencesOnLiteralResidualFibres : Bool
round162BothExternalSlotForcingDifferencesOnLiteralResidualFibres = true
round162OpaqueFullMinusSelfSubtractionRemains : Bool
round162OpaqueFullMinusSelfSubtractionRemains = false
round162ExternalResidualQuadraticVariationPaymentClosed : Bool
round162ExternalResidualQuadraticVariationPaymentClosed = false
round162PackageAClosed : Bool
round162PackageAClosed = false

round162BothExternalSlotForcingDifferencesOnLiteralResidualFibresIsTrue :
  round162BothExternalSlotForcingDifferencesOnLiteralResidualFibres ≡ true
round162BothExternalSlotForcingDifferencesOnLiteralResidualFibresIsTrue = refl
round162PackageAClosedIsFalse : round162PackageAClosed ≡ false
round162PackageAClosedIsFalse = refl
