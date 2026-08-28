module DASHI.Physics.Closure.NSTriadKNCriticalSlotForcingSelfExternalSplitRound160Exact where

------------------------------------------------------------------------
-- ROUND160 / EXACT SELF VS EXTERNAL OWNER SPLIT FOR SLOT-DIFFERENCE FORCING
--
-- Round95 proves on the literal Galerkin object N_full=N_self+N_ext in all
-- three modal forcing slots.  Round157 proves normalized curl is additive.
-- Hence each of the two R144 slot-difference forcings splits EXACTLY into a
-- selected-triad self owner plus an external-network owner before abs values.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNCriticalSecondSlotDifferenceTangentRound159Exact as R159

kqForcingDifferenceSplits :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (k q : Z3.FourierMode)
    (uK uP uQ selfK selfP selfQ extK extP extQ : C3.Complex3 F) →
  R157.slotDifferenceNetworkForcing E S k q uK uP uQ
    (C3.complex3Add selfK extK)
    (C3.complex3Add selfP extP)
    (C3.complex3Add selfQ extQ)
  ≡ C3.complexAdd
      (R157.slotDifferenceNetworkForcing E S k q uK uP uQ selfK selfP selfQ)
      (R157.slotDifferenceNetworkForcing E S k q uK uP uQ extK extP extQ)
kqForcingDifferenceSplits {F = F}
    E S k q uK uP uQ selfK selfP selfQ extK extP extQ
  rewrite R157.normalizedCurlAdd E S k selfK extK
        | R157.normalizedCurlAdd E S q selfQ extQ =
  trans
    (cong₂ C3.complexSubtract
      (R95.networkForcingAdditiveInForcingSlots
        (R142.normalizedCurl E S k uK) uP uQ
        (R142.normalizedCurl E S k selfK) selfP selfQ
        (R142.normalizedCurl E S k extK) extP extQ)
      (R95.networkForcingAdditiveInForcingSlots
        uK uP (R142.normalizedCurl E S q uQ)
        selfK selfP (R142.normalizedCurl E S q selfQ)
        extK extP (R142.normalizedCurl E S q extQ)))
    (R.solve 4
      (λ as ae bs be →
        ((as R.⊕ ae) R.⊕ (R.⊝ (bs R.⊕ be)))
        R.⊜ ((as R.⊕ (R.⊝ bs)) R.⊕ (ae R.⊕ (R.⊝ be))))
      refl
      (R94.networkForcing
        (R142.normalizedCurl E S k uK) uP uQ
        (R142.normalizedCurl E S k selfK) selfP selfQ)
      (R94.networkForcing
        (R142.normalizedCurl E S k uK) uP uQ
        (R142.normalizedCurl E S k extK) extP extQ)
      (R94.networkForcing
        uK uP (R142.normalizedCurl E S q uQ)
        selfK selfP (R142.normalizedCurl E S q selfQ))
      (R94.networkForcing
        uK uP (R142.normalizedCurl E S q uQ)
        extK extP (R142.normalizedCurl E S q extQ)))
  where module R = Ring.Solver F

pqForcingDifferenceSplits :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (p q : Z3.FourierMode)
    (uK uP uQ selfK selfP selfQ extK extP extQ : C3.Complex3 F) →
  R159.slotPQDifferenceNetworkForcing E S p q uK uP uQ
    (C3.complex3Add selfK extK)
    (C3.complex3Add selfP extP)
    (C3.complex3Add selfQ extQ)
  ≡ C3.complexAdd
      (R159.slotPQDifferenceNetworkForcing E S p q uK uP uQ selfK selfP selfQ)
      (R159.slotPQDifferenceNetworkForcing E S p q uK uP uQ extK extP extQ)
pqForcingDifferenceSplits {F = F}
    E S p q uK uP uQ selfK selfP selfQ extK extP extQ
  rewrite R157.normalizedCurlAdd E S p selfP extP
        | R157.normalizedCurlAdd E S q selfQ extQ =
  trans
    (cong₂ C3.complexSubtract
      (R95.networkForcingAdditiveInForcingSlots
        uK (R142.normalizedCurl E S p uP) uQ
        selfK (R142.normalizedCurl E S p selfP) selfQ
        extK (R142.normalizedCurl E S p extP) extQ)
      (R95.networkForcingAdditiveInForcingSlots
        uK uP (R142.normalizedCurl E S q uQ)
        selfK selfP (R142.normalizedCurl E S q selfQ)
        extK extP (R142.normalizedCurl E S q extQ)))
    (R.solve 4
      (λ as ae bs be →
        ((as R.⊕ ae) R.⊕ (R.⊝ (bs R.⊕ be)))
        R.⊜ ((as R.⊕ (R.⊝ bs)) R.⊕ (ae R.⊕ (R.⊝ be))))
      refl
      (R94.networkForcing
        uK (R142.normalizedCurl E S p uP) uQ
        selfK (R142.normalizedCurl E S p selfP) selfQ)
      (R94.networkForcing
        uK (R142.normalizedCurl E S p uP) uQ
        extK (R142.normalizedCurl E S p extP) extQ)
      (R94.networkForcing
        uK uP (R142.normalizedCurl E S q uQ)
        selfK selfP (R142.normalizedCurl E S q selfQ))
      (R94.networkForcing
        uK uP (R142.normalizedCurl E S q uQ)
        extK extP (R142.normalizedCurl E S q extQ)))
  where module R = Ring.Solver F

physicalKQFullForcingDifferenceIsSelfPlusExternal :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  let uK = Audit.velocityAt system (Physical.k tau)
      uP = Audit.velocityAt system (Physical.p tau)
      uQ = Audit.velocityAt system (Physical.q tau)
  in
  R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
    uK uP uQ
    (R95.fullForcingK system tau) (R95.fullForcingP system tau) (R95.fullForcingQ system tau)
  ≡ C3.complexAdd
      (R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
        uK uP uQ
        (R95.selfForcingK system tau) (R95.selfForcingP system tau) (R95.selfForcingQ system tau))
      (R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
        uK uP uQ
        (R95.externalForcingK system tau) (R95.externalForcingP system tau) (R95.externalForcingQ system tau))
physicalKQFullForcingDifferenceIsSelfPlusExternal {E = E} S system tau
  rewrite R95.fullKIsSelfPlusExternal system tau
        | R95.fullPIsSelfPlusExternal system tau
        | R95.fullQIsSelfPlusExternal system tau =
  kqForcingDifferenceSplits E S (Physical.k tau) (Physical.q tau)
    (Audit.velocityAt system (Physical.k tau))
    (Audit.velocityAt system (Physical.p tau))
    (Audit.velocityAt system (Physical.q tau))
    (R95.selfForcingK system tau) (R95.selfForcingP system tau) (R95.selfForcingQ system tau)
    (R95.externalForcingK system tau) (R95.externalForcingP system tau) (R95.externalForcingQ system tau)

round160SlotForcingDifferenceSelfExternalSplitClosed : Bool
round160SlotForcingDifferenceSelfExternalSplitClosed = true
round160LiteralGalerkinKQOwnerSplitClosed : Bool
round160LiteralGalerkinKQOwnerSplitClosed = true
round160SelfForcingWorkPaymentClosed : Bool
round160SelfForcingWorkPaymentClosed = false
round160ExternalForcingWorkQuadraticVariationPaymentClosed : Bool
round160ExternalForcingWorkQuadraticVariationPaymentClosed = false
round160PackageAClosed : Bool
round160PackageAClosed = false

round160SlotForcingDifferenceSelfExternalSplitClosedIsTrue :
  round160SlotForcingDifferenceSelfExternalSplitClosed ≡ true
round160SlotForcingDifferenceSelfExternalSplitClosedIsTrue = refl
round160PackageAClosedIsFalse : round160PackageAClosed ≡ false
round160PackageAClosedIsFalse = refl
