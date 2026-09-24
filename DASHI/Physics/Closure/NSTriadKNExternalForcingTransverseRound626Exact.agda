{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNExternalForcingTransverseRound626Exact where

------------------------------------------------------------------------
-- ROUND626 / EXTERNAL P/Q FORCING LIVES ON THE CORRECT TRANSVERSE FIBRES
--
-- R95 defines
--
--   ExternalP = FullP - SelfP,
--   ExternalQ = FullQ - SelfQ.
--
-- The full projected nonlinearities are transverse by R30.
--
-- R111 identifies one selected self forcing with the sum of the selected
-- ordered interaction and its swap.  Both summands are literal R30 projected
-- ordered terms at the same output, so the self forcing is transverse as well.
--
-- Hence the external residuals are transverse by exact closure under
-- subtraction.  This is the local hypothesis needed to feed the external
-- p-slot forcing into R307's helicity/slot-kernel compiler.
--
-- No norm or estimate appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityTransverseRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNComplex3TransverseDifference as Difference
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as R111
import DASHI.Physics.Closure.NSTriadKNForcingSlotKernelRound307Exact as R307
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142

------------------------------------------------------------------------
-- One selected pair forcing is transverse at its output.
------------------------------------------------------------------------

selfForcingForIncidenceTransverse :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Z3.NonZeroMode (Physical.k tau) →
  Helical.Transverse E (Physical.k tau)
    (R95.selfForcingForIncidence system tau)
selfForcingForIncidenceTransverse {F = F} {E = E} system tau kNonzero =
  let
    first = Audit.projectedOrderedTerm system tau
    second =
      Audit.projectedOrderedTerm system (Symmetry.swapTriad tau)

    firstTransverse :
      Helical.Transverse E (Physical.k tau) first
    firstTransverse =
      R30.projectedOrderedTermTransverse
        system (Physical.k tau) kNonzero tau refl

    secondTransverse :
      Helical.Transverse E (Physical.k tau) second
    secondTransverse =
      R30.projectedOrderedTermTransverse
        system (Physical.k tau) kNonzero
        (Symmetry.swapTriad tau) refl
  in
  trans
    (cong
      (C3.bilinearDot3
        (C3.modeVector E (Physical.k tau)))
      (R111.selfForcingKIsTwoSelectedOrderedTerms system tau))
    (R30.transverseAdd
      (C3.modeVector E (Physical.k tau))
      first second
      firstTransverse secondTransverse)

------------------------------------------------------------------------
-- P/Q selected self forcings.
------------------------------------------------------------------------

selfForcingPTransverse :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Z3.NonZeroMode (Physical.p tau) →
  Helical.Transverse E (Physical.p tau)
    (R95.selfForcingP system tau)
selfForcingPTransverse system tau pNonzero =
  selfForcingForIncidenceTransverse
    system (Orbit.pEnergyLeg tau) pNonzero

selfForcingQTransverse :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Z3.NonZeroMode (Physical.q tau) →
  Helical.Transverse E (Physical.q tau)
    (R95.selfForcingQ system tau)
selfForcingQTransverse system tau qNonzero =
  selfForcingForIncidenceTransverse
    system (Orbit.qEnergyLeg tau) qNonzero

------------------------------------------------------------------------
-- External residual forcings.
------------------------------------------------------------------------

externalForcingPTransverse :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Z3.NonZeroMode (Physical.p tau) →
  Helical.Transverse E (Physical.p tau)
    (R95.externalForcingP system tau)
externalForcingPTransverse {E = E} system tau pNonzero =
  Difference.transverseSubtract E (Physical.p tau)
    (R95.fullForcingP system tau)
    (R95.selfForcingP system tau)
    (R30.projectedNonlinearityTransverseExact
      system (Physical.p tau) pNonzero)
    (selfForcingPTransverse system tau pNonzero)

externalForcingQTransverse :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Z3.NonZeroMode (Physical.q tau) →
  Helical.Transverse E (Physical.q tau)
    (R95.externalForcingQ system tau)
externalForcingQTransverse {E = E} system tau qNonzero =
  Difference.transverseSubtract E (Physical.q tau)
    (R95.fullForcingQ system tau)
    (R95.selfForcingQ system tau)
    (R30.projectedNonlinearityTransverseExact
      system (Physical.q tau) qNonzero)
    (selfForcingQTransverse system tau qNonzero)

------------------------------------------------------------------------
-- Exact R307 input record for the external p-slot / velocity-q pair.
------------------------------------------------------------------------

externalForcingVelocityPair :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Z3.NonZeroMode (Physical.p tau) →
  Helical.Transverse E (Physical.q tau)
    (Audit.velocity system (Physical.q tau)) →
  R307.TransverseForcingVelocityPair E I S L H
    (Physical.p tau) (Physical.q tau)
    (R95.externalForcingP system tau)
    (Audit.velocity system (Physical.q tau))
externalForcingVelocityPair system tau pNonzero qTransverse =
  R307.transverse-forcing-velocity-pair
    (externalForcingPTransverse system tau pNonzero)
    qTransverse

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round626SelfForcingTransverseClosed : Bool
round626SelfForcingTransverseClosed = true

round626ExternalPForcingTransverseClosed : Bool
round626ExternalPForcingTransverseClosed = true

round626ExternalQForcingTransverseClosed : Bool
round626ExternalQForcingTransverseClosed = true

round626ExternalR307PairConstructed : Bool
round626ExternalR307PairConstructed = true

round626IntroducesEstimate : Bool
round626IntroducesEstimate = false

round626ExternalSlotAnalyticPaymentClosed : Bool
round626ExternalSlotAnalyticPaymentClosed = false

round626SelfForcingTransverseClosedIsTrue :
  round626SelfForcingTransverseClosed ≡ true
round626SelfForcingTransverseClosedIsTrue = refl

round626ExternalPForcingTransverseClosedIsTrue :
  round626ExternalPForcingTransverseClosed ≡ true
round626ExternalPForcingTransverseClosedIsTrue = refl

round626ExternalQForcingTransverseClosedIsTrue :
  round626ExternalQForcingTransverseClosed ≡ true
round626ExternalQForcingTransverseClosedIsTrue = refl

round626ExternalR307PairConstructedIsTrue :
  round626ExternalR307PairConstructed ≡ true
round626ExternalR307PairConstructedIsTrue = refl

round626IntroducesEstimateIsFalse :
  round626IntroducesEstimate ≡ false
round626IntroducesEstimateIsFalse = refl

round626ExternalSlotAnalyticPaymentClosedIsFalse :
  round626ExternalSlotAnalyticPaymentClosed ≡ false
round626ExternalSlotAnalyticPaymentClosedIsFalse = refl
