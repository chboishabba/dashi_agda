module DASHI.Physics.Closure.NSTriadKNCriticalForcingWorkOwnerSplitRound161Exact where

------------------------------------------------------------------------
-- ROUND161 / EXACT OWNER SPLIT OF SLOT-DEFECT FORCING WORK
--
-- Round160 proves the two normalized-curl slot forcing differences split as
--
--   F_full = F_self + F_ext
--
-- on the same physical Galerkin carrier.  Round158's defect-energy ledger uses
--
--   W(z,F) = conj(F) z + conj(z) F.
--
-- This file proves W is exactly additive in F, so the energy ledger itself
-- inherits the owner decomposition BEFORE any absolute value:
--
--   W(z,F_full) = W(z,F_self) + W(z,F_ext).
--
-- It also closes the literal p/q Galerkin specialization omitted in Round160.
-- Thus both R144 residual channels now have the same physical self/external
-- owner split.  The next question is mathematical rather than bookkeeping:
-- pay the self owner from the existing triad-internal Waleffe lane, and attack
-- only the external forcing-work network as the novel A residual.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNCriticalSlotDifferenceEnergyRound158Exact as R158
import DASHI.Physics.Closure.NSTriadKNCriticalSecondSlotDifferenceTangentRound159Exact as R159
import DASHI.Physics.Closure.NSTriadKNCriticalSlotForcingSelfExternalSplitRound160Exact as R160

forcingWorkAdditive :
  ∀ {r} {F : C3.RealField r}
    (z first second : C3.Complex F) →
  R158.forcingWork z (C3.complexAdd first second)
  ≡ C3.complexAdd
      (R158.forcingWork z first)
      (R158.forcingWork z second)
forcingWorkAdditive {F = F} z first second =
  trans
    (cong
      (λ conjugated →
        C3.complexAdd
          (C3.complexMultiply conjugated z)
          (C3.complexMultiply
            (C3.complexConjugate z)
            (C3.complexAdd first second)))
      (Hermitian.complexConjugateAdd first second))
    (R.solve 5
      (λ zbar z fbar gbar f g →
        (((fbar R.⊕ gbar) R.⊗ z)
          R.⊕ (zbar R.⊗ (f R.⊕ g)))
        R.⊜
        (((fbar R.⊗ z) R.⊕ (zbar R.⊗ f))
          R.⊕ ((gbar R.⊗ z) R.⊕ (zbar R.⊗ g))))
      refl
      (C3.complexConjugate z) z
      (C3.complexConjugate first) (C3.complexConjugate second)
      first second)
  where module R = Ring.Solver F

------------------------------------------------------------------------
-- Literal p/q physical specialization of Round160.
------------------------------------------------------------------------

physicalPQFullForcingDifferenceIsSelfPlusExternal :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  let uK = Audit.velocityAt system (Physical.k tau)
      uP = Audit.velocityAt system (Physical.p tau)
      uQ = Audit.velocityAt system (Physical.q tau)
  in
  R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
    uK uP uQ
    (R95.fullForcingK system tau)
    (R95.fullForcingP system tau)
    (R95.fullForcingQ system tau)
  ≡ C3.complexAdd
      (R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
        uK uP uQ
        (R95.selfForcingK system tau)
        (R95.selfForcingP system tau)
        (R95.selfForcingQ system tau))
      (R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
        uK uP uQ
        (R95.externalForcingK system tau)
        (R95.externalForcingP system tau)
        (R95.externalForcingQ system tau))
physicalPQFullForcingDifferenceIsSelfPlusExternal {E = E} S system tau
  rewrite R95.fullKIsSelfPlusExternal system tau
        | R95.fullPIsSelfPlusExternal system tau
        | R95.fullQIsSelfPlusExternal system tau =
  R160.pqForcingDifferenceSplits E S (Physical.p tau) (Physical.q tau)
    (Audit.velocityAt system (Physical.k tau))
    (Audit.velocityAt system (Physical.p tau))
    (Audit.velocityAt system (Physical.q tau))
    (R95.selfForcingK system tau)
    (R95.selfForcingP system tau)
    (R95.selfForcingQ system tau)
    (R95.externalForcingK system tau)
    (R95.externalForcingP system tau)
    (R95.externalForcingQ system tau)

------------------------------------------------------------------------
-- Physical forcing-work owner splits for both R144 residual channels.
------------------------------------------------------------------------

physicalKQForcingWorkIsSelfPlusExternal :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  let uK = Audit.velocityAt system (Physical.k tau)
      uP = Audit.velocityAt system (Physical.p tau)
      uQ = Audit.velocityAt system (Physical.q tau)
      z = R157.slotDifference E S (Physical.k tau) (Physical.q tau) uK uP uQ
      selfF = R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
        uK uP uQ
        (R95.selfForcingK system tau)
        (R95.selfForcingP system tau)
        (R95.selfForcingQ system tau)
      extF = R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
        uK uP uQ
        (R95.externalForcingK system tau)
        (R95.externalForcingP system tau)
        (R95.externalForcingQ system tau)
      fullF = R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
        uK uP uQ
        (R95.fullForcingK system tau)
        (R95.fullForcingP system tau)
        (R95.fullForcingQ system tau)
  in
  R158.forcingWork z fullF
  ≡ C3.complexAdd (R158.forcingWork z selfF) (R158.forcingWork z extF)
physicalKQForcingWorkIsSelfPlusExternal S system tau =
  let
    uK = Audit.velocityAt system (Physical.k tau)
    uP = Audit.velocityAt system (Physical.p tau)
    uQ = Audit.velocityAt system (Physical.q tau)
    z = R157.slotDifference _ S (Physical.k tau) (Physical.q tau) uK uP uQ
    selfF = R157.slotDifferenceNetworkForcing _ S (Physical.k tau) (Physical.q tau)
      uK uP uQ
      (R95.selfForcingK system tau) (R95.selfForcingP system tau) (R95.selfForcingQ system tau)
    extF = R157.slotDifferenceNetworkForcing _ S (Physical.k tau) (Physical.q tau)
      uK uP uQ
      (R95.externalForcingK system tau) (R95.externalForcingP system tau) (R95.externalForcingQ system tau)
    fullF = R157.slotDifferenceNetworkForcing _ S (Physical.k tau) (Physical.q tau)
      uK uP uQ
      (R95.fullForcingK system tau) (R95.fullForcingP system tau) (R95.fullForcingQ system tau)
  in
  trans
    (cong (R158.forcingWork z)
      (R160.physicalKQFullForcingDifferenceIsSelfPlusExternal S system tau))
    (forcingWorkAdditive z selfF extF)

physicalPQForcingWorkIsSelfPlusExternal :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  let uK = Audit.velocityAt system (Physical.k tau)
      uP = Audit.velocityAt system (Physical.p tau)
      uQ = Audit.velocityAt system (Physical.q tau)
      z = R159.slotPQDifference E S (Physical.p tau) (Physical.q tau) uK uP uQ
      selfF = R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
        uK uP uQ
        (R95.selfForcingK system tau)
        (R95.selfForcingP system tau)
        (R95.selfForcingQ system tau)
      extF = R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
        uK uP uQ
        (R95.externalForcingK system tau)
        (R95.externalForcingP system tau)
        (R95.externalForcingQ system tau)
      fullF = R159.slotPQDifferenceNetworkForcing E S (Physical.p tau) (Physical.q tau)
        uK uP uQ
        (R95.fullForcingK system tau)
        (R95.fullForcingP system tau)
        (R95.fullForcingQ system tau)
  in
  R158.forcingWork z fullF
  ≡ C3.complexAdd (R158.forcingWork z selfF) (R158.forcingWork z extF)
physicalPQForcingWorkIsSelfPlusExternal S system tau =
  let
    uK = Audit.velocityAt system (Physical.k tau)
    uP = Audit.velocityAt system (Physical.p tau)
    uQ = Audit.velocityAt system (Physical.q tau)
    z = R159.slotPQDifference _ S (Physical.p tau) (Physical.q tau) uK uP uQ
    selfF = R159.slotPQDifferenceNetworkForcing _ S (Physical.p tau) (Physical.q tau)
      uK uP uQ
      (R95.selfForcingK system tau) (R95.selfForcingP system tau) (R95.selfForcingQ system tau)
    extF = R159.slotPQDifferenceNetworkForcing _ S (Physical.p tau) (Physical.q tau)
      uK uP uQ
      (R95.externalForcingK system tau) (R95.externalForcingP system tau) (R95.externalForcingQ system tau)
  in
  trans
    (cong (R158.forcingWork z)
      (physicalPQFullForcingDifferenceIsSelfPlusExternal S system tau))
    (forcingWorkAdditive z selfF extF)

round161ForcingWorkOwnerAdditivityClosed : Bool
round161ForcingWorkOwnerAdditivityClosed = true

round161BothLiteralSlotForcingOwnersSplitClosed : Bool
round161BothLiteralSlotForcingOwnersSplitClosed = true

round161BothLiteralForcingWorkOwnersSplitClosed : Bool
round161BothLiteralForcingWorkOwnersSplitClosed = true

round161SelfForcingWorkPaymentClosed : Bool
round161SelfForcingWorkPaymentClosed = false

round161ExternalForcingWorkPaymentClosed : Bool
round161ExternalForcingWorkPaymentClosed = false

round161PackageAClosed : Bool
round161PackageAClosed = false

round161BothLiteralForcingWorkOwnersSplitClosedIsTrue :
  round161BothLiteralForcingWorkOwnersSplitClosed ≡ true
round161BothLiteralForcingWorkOwnersSplitClosedIsTrue = refl

round161PackageAClosedIsFalse : round161PackageAClosed ≡ false
round161PackageAClosedIsFalse = refl
