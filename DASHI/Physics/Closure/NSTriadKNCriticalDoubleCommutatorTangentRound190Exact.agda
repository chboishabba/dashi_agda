module DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorTangentRound190Exact where

------------------------------------------------------------------------
-- ROUND190 / ONE DAMPED-FORCED EQUATION FOR THE COMPLETE DOUBLE COMMUTATOR
--
-- R144 reduces the critical production to two normalized-curl slot
-- differences.  R157 and R159 prove that BOTH differences evolve with the
-- same triad decay scalar and their own signed network-forcing differences.
-- Since the radial coefficients are time-independent Fourier multipliers, the
-- COMPLETE two-channel double commutator therefore obeys one exact equation
--
--   dP = sigma P + (c_k F_kq + c_p F_pq).
--
-- This is the dynamic object the arbitrary-data payment should act on.  It
-- preserves the two slot cancellations and does not require estimating the two
-- channels separately or taking absolute values before they recombine.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNCriticalSecondSlotDifferenceTangentRound159Exact as R159

weightedTwoChannel :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F →
  C3.Complex F → C3.Complex F → C3.Complex F
weightedTwoChannel {F = F} cK cP zKQ zPQ =
  C3.complexAdd
    (C3.complexMultiply (C3.realEmbed F cK) zKQ)
    (C3.complexMultiply (C3.realEmbed F cP) zPQ)

doubleCommutatorAmplitude :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  C3.Carrier F → C3.Carrier F →
  Z3.FourierMode → Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
doubleCommutatorAmplitude E S cK cP k p q uK uP uQ =
  weightedTwoChannel cK cP
    (R157.slotDifference E S k q uK uP uQ)
    (R159.slotPQDifference E S p q uK uP uQ)

doubleCommutatorForcing :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  C3.Carrier F → C3.Carrier F →
  Z3.FourierMode → Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
doubleCommutatorForcing E S cK cP k p q uK uP uQ fK fP fQ =
  weightedTwoChannel cK cP
    (R157.slotDifferenceNetworkForcing E S k q uK uP uQ fK fP fQ)
    (R159.slotPQDifferenceNetworkForcing E S p q uK uP uQ fK fP fQ)

doubleCommutatorTangent :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  C3.Carrier F → C3.Carrier F →
  Z3.FourierMode → Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
doubleCommutatorTangent E S cK cP k p q uK uP uQ dK dP dQ =
  weightedTwoChannel cK cP
    (R157.slotDifferenceTangent E S k q uK uP uQ dK dP dQ)
    (R159.slotPQDifferenceTangent E S p q uK uP uQ dK dP dQ)

doubleCommutatorDampedNetworkEquation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (cK cP : C3.Carrier F)
    (k p q : Z3.FourierMode)
    (rhoK rhoP rhoQ : C3.Carrier F)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  doubleCommutatorTangent E S cK cP k p q uK uP uQ
    (R94.dampedPlusForcing rhoK uK fK)
    (R94.dampedPlusForcing rhoP uP fP)
    (R94.dampedPlusForcing rhoQ uQ fQ)
  ≡
  C3.complexAdd
    (C3.complexMultiply
      (R94.totalNegativeDecay rhoK rhoP rhoQ)
      (doubleCommutatorAmplitude E S cK cP k p q uK uP uQ))
    (doubleCommutatorForcing E S cK cP k p q uK uP uQ fK fP fQ)
doubleCommutatorDampedNetworkEquation {F = F}
    E S cK cP k p q rhoK rhoP rhoQ uK uP uQ fK fP fQ
  rewrite R157.slotDifferenceDampedNetworkEquation
      E S k q rhoK rhoP rhoQ uK uP uQ fK fP fQ
        | R159.slotPQDifferenceDampedNetworkEquation
      E S p q rhoK rhoP rhoQ uK uP uQ fK fP fQ =
  R.solve 7
    (λ a b d z1 z2 f1 f2 →
      ((a R.⊗ ((d R.⊗ z1) R.⊕ f1))
        R.⊕ (b R.⊗ ((d R.⊗ z2) R.⊕ f2)))
      R.⊜
      ((d R.⊗ ((a R.⊗ z1) R.⊕ (b R.⊗ z2)))
        R.⊕ ((a R.⊗ f1) R.⊕ (b R.⊗ f2))))
    refl
    (C3.realEmbed F cK)
    (C3.realEmbed F cP)
    (R94.totalNegativeDecay rhoK rhoP rhoQ)
    (R157.slotDifference E S k q uK uP uQ)
    (R159.slotPQDifference E S p q uK uP uQ)
    (R157.slotDifferenceNetworkForcing E S k q uK uP uQ fK fP fQ)
    (R159.slotPQDifferenceNetworkForcing E S p q uK uP uQ fK fP fQ)
  where module R = Ring.Solver F

round190CompleteDoubleCommutatorDynamicsClosed : Bool
round190CompleteDoubleCommutatorDynamicsClosed = true

round190TwoChannelsNeedSeparateAbsolutePayment : Bool
round190TwoChannelsNeedSeparateAbsolutePayment = false

round190CombinedForcingQuadraticBudgetClosed : Bool
round190CombinedForcingQuadraticBudgetClosed = false

round190PackageAClosed : Bool
round190PackageAClosed = false

round190ClayPromotion : Bool
round190ClayPromotion = false
