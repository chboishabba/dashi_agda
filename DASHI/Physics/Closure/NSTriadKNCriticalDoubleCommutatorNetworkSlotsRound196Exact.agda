module DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorNetworkSlotsRound196Exact where

------------------------------------------------------------------------
-- ROUND196 / COMPLETE FORCING IS A CYCLIC THREE-SLOT NETWORK COMMUTATOR
--
-- R195 reopens the two-difference complex expression into the symmetric
-- critical three-slot form.  Here the three complex amplitudes are identified
-- literally as Round94 NETWORK FORCINGS with normalized curl inserted in the
-- k, p, or q slot respectively.
--
-- Therefore the complete forcing driving the R190/R191 dynamic production is
--
--   c_k N_k^S + c_p N_p^S + c_q N_q^S,
--
-- not two unrelated difference forcings.  Every term of N_j^S carries exactly
-- one insertion of S_j = |j|^-1 curl_j, either in the state or forcing argument
-- of slot j.  This is the surface on which the radius in c_j can cancel the
-- inverse radius of normalized curl.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact as R138
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorTangentRound190Exact as R190
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorSymmetricSlotsRound195Exact as R195

networkSlotK :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
networkSlotK E S k uK uP uQ fK fP fQ =
  R94.networkForcing
    (R142.normalizedCurl E S k uK) uP uQ
    (R142.normalizedCurl E S k fK) fP fQ

networkSlotP :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
networkSlotP E S p uK uP uQ fK fP fQ =
  R94.networkForcing
    uK (R142.normalizedCurl E S p uP) uQ
    fK (R142.normalizedCurl E S p fP) fQ

networkSlotQ :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
networkSlotQ E S q uK uP uQ fK fP fQ =
  R94.networkForcing
    uK uP (R142.normalizedCurl E S q uQ)
    fK fP (R142.normalizedCurl E S q fQ)

completeDoubleCommutatorForcingIsCyclicThreeSlot :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (rk rp rq : C3.Carrier F)
    (k p q : Z3.FourierMode)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  R190.doubleCommutatorForcing E S
    (R138.criticalRadialCoefficientK rk rp rq)
    (R138.criticalRadialCoefficientP rk rp rq)
    k p q uK uP uQ fK fP fQ
  ≡
  R195.complexCriticalSlotProduction rk rp rq
    (networkSlotK E S k uK uP uQ fK fP fQ)
    (networkSlotP E S p uK uP uQ fK fP fQ)
    (networkSlotQ E S q uK uP uQ fK fP fQ)
completeDoubleCommutatorForcingIsCyclicThreeSlot
    E S rk rp rq k p q uK uP uQ fK fP fQ =
  R195.criticalTwoDifferenceIsComplexThreeSlot
    rk rp rq
    (networkSlotK E S k uK uP uQ fK fP fQ)
    (networkSlotP E S p uK uP uQ fK fP fQ)
    (networkSlotQ E S q uK uP uQ fK fP fQ)

round196CompleteNetworkForcingCyclicThreeSlotClosed : Bool
round196CompleteNetworkForcingCyclicThreeSlotClosed = true

round196NegativeQDifferencePiecesRemainIndependent : Bool
round196NegativeQDifferencePiecesRemainIndependent = false

round196RadiusCancellationSurfaceExposed : Bool
round196RadiusCancellationSurfaceExposed = true

round196PackageAClosed : Bool
round196PackageAClosed = false

round196ClayPromotion : Bool
round196ClayPromotion = false
