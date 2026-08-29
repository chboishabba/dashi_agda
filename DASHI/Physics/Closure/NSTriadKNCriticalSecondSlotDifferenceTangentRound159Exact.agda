module DASHI.Physics.Closure.NSTriadKNCriticalSecondSlotDifferenceTangentRound159Exact where

------------------------------------------------------------------------
-- ROUND159 / CLOSE THE SECOND PHYSICAL SLOT-DIFFERENCE DYNAMICS
--
-- Round144's complete critical production contains TWO surviving normalized-
-- curl differences: B_k-B_q and B_p-B_q.  Round157 derives the exact damped-
-- forced equation for B_k-B_q.  This file closes the cyclic companion B_p-B_q
-- and then composes both equations with Round158's defect-energy identity.
--
-- Therefore every slot difference appearing in the exact R144 double
-- commutator now has an explicit same-network evolution and energy ledger.
-- The only new analytic producer left in A is the global signed payment of the
-- two forcing-work families after summing the literal Galerkin network.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNCriticalSlotDifferenceEnergyRound158Exact as R158

slotPAmplitude :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
slotPAmplitude E S p uK uP uQ =
  R94.complexAmplitude uK (R142.normalizedCurl E S p uP) uQ

slotPQDifference :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
slotPQDifference E S p q uK uP uQ =
  C3.complexSubtract
    (slotPAmplitude E S p uK uP uQ)
    (R157.slotQAmplitude E S q uK uP uQ)

slotPQDifferenceTangent :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
slotPQDifferenceTangent E S p q uK uP uQ dK dP dQ =
  C3.complexSubtract
    (R94.amplitudeTangent
      uK (R142.normalizedCurl E S p uP) uQ
      dK (R142.normalizedCurl E S p dP) dQ)
    (R94.amplitudeTangent
      uK uP (R142.normalizedCurl E S q uQ)
      dK dP (R142.normalizedCurl E S q dQ))

slotPQDifferenceNetworkForcing :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
slotPQDifferenceNetworkForcing E S p q uK uP uQ fK fP fQ =
  C3.complexSubtract
    (R94.networkForcing
      uK (R142.normalizedCurl E S p uP) uQ
      fK (R142.normalizedCurl E S p fP) fQ)
    (R94.networkForcing
      uK uP (R142.normalizedCurl E S q uQ)
      fK fP (R142.normalizedCurl E S q fQ))

slotPQDifferenceDampedNetworkEquation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (p q : Z3.FourierMode)
    (rhoK rhoP rhoQ : C3.Carrier F)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  slotPQDifferenceTangent E S p q uK uP uQ
    (R94.dampedPlusForcing rhoK uK fK)
    (R94.dampedPlusForcing rhoP uP fP)
    (R94.dampedPlusForcing rhoQ uQ fQ)
  ≡
  C3.complexAdd
    (C3.complexMultiply
      (R94.totalNegativeDecay rhoK rhoP rhoQ)
      (slotPQDifference E S p q uK uP uQ))
    (slotPQDifferenceNetworkForcing E S p q uK uP uQ fK fP fQ)
slotPQDifferenceDampedNetworkEquation {F = F}
    E S p q rhoK rhoP rhoQ uK uP uQ fK fP fQ
  rewrite R157.normalizedCurlDampedPlusForcing E S p rhoP uP fP
        | R157.normalizedCurlDampedPlusForcing E S q rhoQ uQ fQ =
  trans
    (cong₂ C3.complexSubtract
      (R94.amplitudeTangentDampedNetwork
        rhoK rhoP rhoQ
        uK (R142.normalizedCurl E S p uP) uQ
        fK (R142.normalizedCurl E S p fP) fQ)
      (R94.amplitudeTangentDampedNetwork
        rhoK rhoP rhoQ
        uK uP (R142.normalizedCurl E S q uQ)
        fK fP (R142.normalizedCurl E S q fQ)))
    regroup
  where
  decay = R94.totalNegativeDecay rhoK rhoP rhoQ
  aP = slotPAmplitude E S p uK uP uQ
  aQ = R157.slotQAmplitude E S q uK uP uQ
  fPS = R94.networkForcing
    uK (R142.normalizedCurl E S p uP) uQ
    fK (R142.normalizedCurl E S p fP) fQ
  fQS = R94.networkForcing
    uK uP (R142.normalizedCurl E S q uQ)
    fK fP (R142.normalizedCurl E S q fQ)

  regroup :
    C3.complexSubtract
      (C3.complexAdd (C3.complexMultiply decay aP) fPS)
      (C3.complexAdd (C3.complexMultiply decay aQ) fQS)
    ≡
    C3.complexAdd
      (C3.complexMultiply decay (C3.complexSubtract aP aQ))
      (C3.complexSubtract fPS fQS)
  regroup =
    R.solve 5
      (λ decay aP aQ fP fQ →
        (((decay R.⊗ aP) R.⊕ fP)
          R.⊕ (R.⊝ ((decay R.⊗ aQ) R.⊕ fQ)))
        R.⊜
        ((decay R.⊗ (aP R.⊕ (R.⊝ aQ)))
          R.⊕ (fP R.⊕ (R.⊝ fQ))))
      refl decay aP aQ fPS fQS
    where module R = Ring.Solver F

------------------------------------------------------------------------
-- Both surviving slot differences now have exact energy ledgers.
------------------------------------------------------------------------

kqSlotDifferenceEnergyLedger :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (k q : Z3.FourierMode)
    (rhoK rhoP rhoQ : C3.Carrier F)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  let z = R157.slotDifference E S k q uK uP uQ
      forcing = R157.slotDifferenceNetworkForcing E S k q uK uP uQ fK fP fQ
      decay = R94.totalNegativeDecay rhoK rhoP rhoQ
  in
  R158.slotDefectEnergyTangent z
    (R157.slotDifferenceTangent E S k q uK uP uQ
      (R94.dampedPlusForcing rhoK uK fK)
      (R94.dampedPlusForcing rhoP uP fP)
      (R94.dampedPlusForcing rhoQ uQ fQ))
  ≡ C3.complexAdd
      (C3.complexMultiply (C3.complexAdd decay decay)
        (R158.slotDefectEnergy z))
      (R158.forcingWork z forcing)
kqSlotDifferenceEnergyLedger E S k q rhoK rhoP rhoQ uK uP uQ fK fP fQ =
  let
    z = R157.slotDifference E S k q uK uP uQ
    forcing = R157.slotDifferenceNetworkForcing E S k q uK uP uQ fK fP fQ
    decay = R94.totalNegativeDecay rhoK rhoP rhoQ
  in
  trans
    (cong (R158.slotDefectEnergyTangent z)
      (R157.slotDifferenceDampedNetworkEquation
        E S k q rhoK rhoP rhoQ uK uP uQ fK fP fQ))
    (R158.dampedForcedEnergyIdentity decay z forcing
      (R158.totalNegativeDecayIsConjugationFixed rhoK rhoP rhoQ))

pqSlotDifferenceEnergyLedger :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (p q : Z3.FourierMode)
    (rhoK rhoP rhoQ : C3.Carrier F)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  let z = slotPQDifference E S p q uK uP uQ
      forcing = slotPQDifferenceNetworkForcing E S p q uK uP uQ fK fP fQ
      decay = R94.totalNegativeDecay rhoK rhoP rhoQ
  in
  R158.slotDefectEnergyTangent z
    (slotPQDifferenceTangent E S p q uK uP uQ
      (R94.dampedPlusForcing rhoK uK fK)
      (R94.dampedPlusForcing rhoP uP fP)
      (R94.dampedPlusForcing rhoQ uQ fQ))
  ≡ C3.complexAdd
      (C3.complexMultiply (C3.complexAdd decay decay)
        (R158.slotDefectEnergy z))
      (R158.forcingWork z forcing)
pqSlotDifferenceEnergyLedger E S p q rhoK rhoP rhoQ uK uP uQ fK fP fQ =
  let
    z = slotPQDifference E S p q uK uP uQ
    forcing = slotPQDifferenceNetworkForcing E S p q uK uP uQ fK fP fQ
    decay = R94.totalNegativeDecay rhoK rhoP rhoQ
  in
  trans
    (cong (R158.slotDefectEnergyTangent z)
      (slotPQDifferenceDampedNetworkEquation
        E S p q rhoK rhoP rhoQ uK uP uQ fK fP fQ))
    (R158.dampedForcedEnergyIdentity decay z forcing
      (R158.totalNegativeDecayIsConjugationFixed rhoK rhoP rhoQ))

round159BothPhysicalSlotDifferenceDynamicsClosed : Bool
round159BothPhysicalSlotDifferenceDynamicsClosed = true

round159BothPhysicalSlotDifferenceEnergyLedgersClosed : Bool
round159BothPhysicalSlotDifferenceEnergyLedgersClosed = true

round159GlobalSignedForcingWorkPaymentClosed : Bool
round159GlobalSignedForcingWorkPaymentClosed = false

round159PackageAClosed : Bool
round159PackageAClosed = false

round159BothPhysicalSlotDifferenceEnergyLedgersClosedIsTrue :
  round159BothPhysicalSlotDifferenceEnergyLedgersClosed ≡ true
round159BothPhysicalSlotDifferenceEnergyLedgersClosedIsTrue = refl

round159PackageAClosedIsFalse : round159PackageAClosed ≡ false
round159PackageAClosedIsFalse = refl
