module DASHI.Physics.Closure.NSTriadKNCriticalSlotForcingSelfExternalSplitRound160Exact where

------------------------------------------------------------------------
-- ROUND160 / EXACT SELF VS EXTERNAL OWNER SPLIT FOR THE SLOT-DIFFERENCE FORCE
--
-- Cross-pollination with the Yang--Mills owner ledgers: do not tax the whole
-- forcing as one anonymous positive term.  First reopen the exact physical
-- forcing into the selected triad's self contribution plus the external
-- network residual, then preserve signs through the slot commutator.
--
-- Round95 already proves on the SAME Galerkin object
--
--   N_full,j = N_self,j + N_ext,j
--
-- for j=k,p,q, and proves networkForcing is additive in all forcing slots.
-- Round157 proves normalized curl is additive.  Therefore both surviving
-- forcing differences from R157/R159 split exactly as
--
--   Fdiff_full = Fdiff_self + Fdiff_external.
--
-- This matters because the self triad has much stronger exact Waleffe
-- cancellation/payment structure.  Package A should charge only the external
-- residual owner if the self forcing-work contribution can be discharged from
-- the existing internal-payment lane.
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
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNCriticalSecondSlotDifferenceTangentRound159Exact as R159

kqForcingDifferenceSplits :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (k q : Z3.FourierMode)
    (uK uP uQ selfK selfP selfQ extK extP extQ : C3.Complex3 F) →
  R157.slotDifferenceNetworkForcing E S k q uK uP uQ
    (C3.complex3Add selfK extK)
    (C3.complex3Add selfP extP)
    (C3.complex3Add selfQ extQ)
  ≡
  C3.complexAdd
    (R157.slotDifferenceNetworkForcing E S k q uK uP uQ
      selfK selfP selfQ)
    (R157.slotDifferenceNetworkForcing E S k q uK uP uQ
      extK extP extQ)
kqForcingDifferenceSplits {F = F}
    E S k q uK uP uQ selfK selfP selfQ extK extP extQ
  rewrite R157.normalizedCurlAdd E S k selfK extK
        | R157.normalizedCurlAdd E S q selfQ extQ =
  trans
    (cong₂ C3.complexSubtract
      (R95.networkForcingAdditiveInForcingSlots
        (R157.R142.normalizedCurl E S k uK) uP uQ
        (R157.R142.normalizedCurl E S k selfK) selfP selfQ
        (R157.R142.normalizedCurl E S k extK) extP extQ)
      (R95.networkForcingAdditiveInForcingSlots
        uK uP (R157.R142.normalizedCurl E S q uQ)
        selfK selfP (R157.R142.normalizedCurl E S q selfQ)
        extK extP (R157.R142.normalizedCurl E S q extQ)))
    regroup
  where
  selfA = R157.slotDifferenceNetworkForcing E S k q uK uP uQ selfK selfP selfQ
  extA  = R157.slotDifferenceNetworkForcing E S k q uK uP uQ extK extP extQ
  -- The two Round95 equations give (Aself+Aext) - (Bself+Bext).
  regroup =
    R.solve 4
      (λ as ae bs be →
        ((as R.⊕ ae) R.⊕ (R.⊝ (bs R.⊕ be)))
        R.⊜ ((as R.⊕ (R.⊝ bs)) R.⊕ (ae R.⊕ (R.⊝ be))))
      refl
      (R95.Tangent.networkForcing
        (R157.R142.normalizedCurl E S k uK) uP uQ
        (R157.R142.normalizedCurl E S k selfK) selfP selfQ)
      (R95.Tangent.networkForcing
        (R157.R142.normalizedCurl E S k uK) uP uQ
        (R157.R142.normalizedCurl E S k extK) extP extQ)
      (R95.Tangent.networkForcing
        uK uP (R157.R142.normalizedCurl E S q uQ)
        selfK selfP (R157.R142.normalizedCurl E S q selfQ))
      (R95.Tangent.networkForcing
        uK uP (R157.R142.normalizedCurl E S q uQ)
        extK extP (R157.R142.normalizedCurl E S q extQ))
    where module R = Ring.Solver F

pqForcingDifferenceSplits :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (p q : Z3.FourierMode)
    (uK uP uQ selfK selfP selfQ extK extP extQ : C3.Complex3 F) →
  R159.slotPQDifferenceNetworkForcing E S p q uK uP uQ
    (C3.complex3Add selfK extK)
    (C3.complex3Add selfP extP)
    (C3.complex3Add selfQ extQ)
  ≡
  C3.complexAdd
    (R159.slotPQDifferenceNetworkForcing E S p q uK uP uQ
      selfK selfP selfQ)
    (R159.slotPQDifferenceNetworkForcing E S p q uK uP uQ
      extK extP extQ)
pqForcingDifferenceSplits {F = F}
    E S p q uK uP uQ selfK selfP selfQ extK extP extQ
  rewrite R157.normalizedCurlAdd E S p selfP extP
        | R157.normalizedCurlAdd E S q selfQ extQ =
  trans
    (cong₂ C3.complexSubtract
      (R95.networkForcingAdditiveInForcingSlots
        uK (R157.R142.normalizedCurl E S p uP) uQ
        selfK (R157.R142.normalizedCurl E S p selfP) selfQ
        extK (R157.R142.normalizedCurl E S p extP) extQ)
      (R95.networkForcingAdditiveInForcingSlots
        uK uP (R157.R142.normalizedCurl E S q uQ)
        selfK selfP (R157.R142.normalizedCurl E S q selfQ)
        extK extP (R157.R142.normalizedCurl E S q extQ)))
    regroup
  where
  regroup =
    R.solve 4
      (λ as ae bs be →
        ((as R.⊕ ae) R.⊕ (R.⊝ (bs R.⊕ be)))
        R.⊜ ((as R.⊕ (R.⊝ bs)) R.⊕ (ae R.⊕ (R.⊝ be))))
      refl
      (R95.Tangent.networkForcing
        uK (R157.R142.normalizedCurl E S p uP) uQ
        selfK (R157.R142.normalizedCurl E S p selfP) selfQ)
      (R95.Tangent.networkForcing
        uK (R157.R142.normalizedCurl E S p uP) uQ
        extK (R157.R142.normalizedCurl E S p extP) extQ)
      (R95.Tangent.networkForcing
        uK uP (R157.R142.normalizedCurl E S q uQ)
        selfK selfP (R157.R142.normalizedCurl E S q selfQ))
      (R95.Tangent.networkForcing
        uK uP (R157.R142.normalizedCurl E S q uQ)
        extK extP (R157.R142.normalizedCurl E S q extQ))
    where module R = Ring.Solver F

------------------------------------------------------------------------
-- Literal Galerkin specialization using Round95's exact owner split.
------------------------------------------------------------------------

physicalKQFullForcingDifferenceIsSelfPlusExternal :
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
  R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
    uK uP uQ
    (R95.fullForcingK system tau)
    (R95.fullForcingP system tau)
    (R95.fullForcingQ system tau)
  ≡
  C3.complexAdd
    (R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
      uK uP uQ
      (R95.selfForcingK system tau)
      (R95.selfForcingP system tau)
      (R95.selfForcingQ system tau))
    (R157.slotDifferenceNetworkForcing E S (Physical.k tau) (Physical.q tau)
      uK uP uQ
      (R95.externalForcingK system tau)
      (R95.externalForcingP system tau)
      (R95.externalForcingQ system tau))
physicalKQFullForcingDifferenceIsSelfPlusExternal S system tau
  rewrite R95.fullKIsSelfPlusExternal system tau
        | R95.fullPIsSelfPlusExternal system tau
        | R95.fullQIsSelfPlusExternal system tau =
  kqForcingDifferenceSplits _ S (Physical.k tau) (Physical.q tau)
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
