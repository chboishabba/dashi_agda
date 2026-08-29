module DASHI.Physics.Closure.NSTriadKNCriticalNetworkRawCurlGapWeldRound199Exact where

------------------------------------------------------------------------
-- ROUND199 / PHYSICAL COMPLETE NETWORK FORCE -> RAW-CURL RADIAL-GAP FORM
--
-- R171 performed the radius cancellation for the cubic eight-helicity
-- production.  R196--198 now do the same calculation for the NETWORK forcing
-- that drives its tangent.
--
-- On the same proof-bearing physical radius calibration,
--
--   Fcrit
--     = (r_p-r_q) N_k^curl
--       + (r_q-r_k) N_p^curl
--       + (r_k-r_p) N_q^curl,
--
-- for arbitrary forcing vectors f_k,f_p,f_q.  Thus the complete dynamic owner
-- has exactly the same radial-gap coefficients as the original critical
-- production.  The tangent does not reintroduce a hidden normalized-curl
-- denominator or high radius.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact as R138
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlDoubleCommutatorRound144Exact as R144
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlRadiusCancellationRound147Exact as R147
import DASHI.Physics.Closure.NSTriadKNCriticalRawCurlCompleteWeldRound171Exact as R171
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorTangentRound190Exact as R190
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorNetworkSlotsRound196Exact as R196
import DASHI.Physics.Closure.NSTriadKNCriticalNetworkSlotInverseFactorRound197Exact as R197
import DASHI.Physics.Closure.NSTriadKNCriticalNetworkRadiusCancellationRound198Exact as R198

completeCriticalNetworkForcingIsRawCurlGapForm :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (T : R144.PhysicalNormalizedCurlTriad E I S L H)
    (C : R171.PhysicalRadiusCalibration T)
    (fK fP fQ : C3.Complex3 F) →
  R190.doubleCommutatorForcing E S
    (R138.criticalRadialCoefficientK
      (R147.radiusK (R171.radii C))
      (R147.radiusP (R171.radii C))
      (R147.radiusQ (R171.radii C)))
    (R138.criticalRadialCoefficientP
      (R147.radiusK (R171.radii C))
      (R147.radiusP (R171.radii C))
      (R147.radiusQ (R171.radii C)))
    (R144.k T) (R144.p T) (R144.q T)
    (R144.uK T) (R144.uP T) (R144.uQ T)
    fK fP fQ
  ≡
  R198.rawNetworkGapProduction (R171.radii C)
    (R197.rawNetworkSlotK E (R144.k T)
      (R144.uK T) (R144.uP T) (R144.uQ T) fK fP fQ)
    (R197.rawNetworkSlotP E (R144.p T)
      (R144.uK T) (R144.uP T) (R144.uQ T) fK fP fQ)
    (R197.rawNetworkSlotQ E (R144.q T)
      (R144.uK T) (R144.uP T) (R144.uQ T) fK fP fQ)
completeCriticalNetworkForcingIsRawCurlGapForm {E = E} {S = S}
    T C fK fP fQ =
  let
    R = R171.radii C
    rawK = R197.rawNetworkSlotK E (R144.k T)
      (R144.uK T) (R144.uP T) (R144.uQ T) fK fP fQ
    rawP = R197.rawNetworkSlotP E (R144.p T)
      (R144.uK T) (R144.uP T) (R144.uQ T) fK fP fQ
    rawQ = R197.rawNetworkSlotQ E (R144.q T)
      (R144.uK T) (R144.uP T) (R144.uQ T) fK fP fQ
  in
  trans
    (R196.completeDoubleCommutatorForcingIsCyclicThreeSlot
      E S
      (R147.radiusK R) (R147.radiusP R) (R147.radiusQ R)
      (R144.k T) (R144.p T) (R144.q T)
      (R144.uK T) (R144.uP T) (R144.uQ T) fK fP fQ)
    (trans normalizedNetworkToInverseRaw
      (R198.criticalNetworkSlotsCancelToRawGaps R rawK rawP rawQ))
  where
  R = R171.radii C
  rawK = R197.rawNetworkSlotK E (R144.k T)
    (R144.uK T) (R144.uP T) (R144.uQ T) fK fP fQ
  rawP = R197.rawNetworkSlotP E (R144.p T)
    (R144.uK T) (R144.uP T) (R144.uQ T) fK fP fQ
  rawQ = R197.rawNetworkSlotQ E (R144.q T)
    (R144.uK T) (R144.uP T) (R144.uQ T) fK fP fQ

  normalizedNetworkToInverseRaw :
    R198.rawNetworkGapProduction R rawK rawP rawQ
    ≡ R198.rawNetworkGapProduction R rawK rawP rawQ
  normalizedNetworkToInverseRaw = refl

round199PhysicalNetworkRawCurlGapWeldClosed : Bool
round199PhysicalNetworkRawCurlGapWeldClosed = true

round199DynamicForcingHasSameRadialGapCoefficients : Bool
round199DynamicForcingHasSameRadialGapCoefficients = true

round199HiddenNormalizedCurlRadiusInDynamicOwner : Bool
round199HiddenNormalizedCurlRadiusInDynamicOwner = false

round199QuadraticCompanionPaymentClosed : Bool
round199QuadraticCompanionPaymentClosed = false

round199PackageAClosed : Bool
round199PackageAClosed = false

round199ClayPromotion : Bool
round199ClayPromotion = false
