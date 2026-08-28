module DASHI.Physics.Closure.NSTriadKNCriticalRawCurlCompleteWeldRound171Exact where

------------------------------------------------------------------------
-- ROUND171 / COMPLETE EIGHT-CHANNEL PRODUCTION -> RAW-CURL RADIAL-GAP FORM
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicityWalshMomentRound139Exact as R139
import DASHI.Physics.Closure.NSTriadKNHelicityWalshPhysicalAmplitudeRound140Exact as R140
import DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact as R138
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlDoubleCommutatorRound144Exact as R144
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlRadiusCancellationRound147Exact as R147
import DASHI.Physics.Closure.NSTriadKNCriticalRawCurlRadialGapRound169Exact as R169
import DASHI.Physics.Closure.NSTriadKNCriticalRawCurlPhysicalWeldRound170Exact as R170

record PhysicalRadiusCalibration
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (T : R144.PhysicalNormalizedCurlTriad E I S L H) : Set r where
  constructor physical-radius-calibration
  field
    radii : R147.ReciprocalRadiusTriple F
    radiusKMeaning : R147.radiusK radii ≡ Helical.modeNorm S (R144.k T)
    radiusPMeaning : R147.radiusP radii ≡ Helical.modeNorm S (R144.p T)
    radiusQMeaning : R147.radiusQ radii ≡ Helical.modeNorm S (R144.q T)
    inverseKMeaning : R147.inverseK radii ≡ Helical.inverseModeNorm S (R144.k T)
    inversePMeaning : R147.inverseP radii ≡ Helical.inverseModeNorm S (R144.p T)
    inverseQMeaning : R147.inverseQ radii ≡ Helical.inverseModeNorm S (R144.q T)

open PhysicalRadiusCalibration public

completeCriticalProductionIsRawCurlGapForm :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (T : R144.PhysicalNormalizedCurlTriad E I S L H)
    (C : PhysicalRadiusCalibration T) →
  R139.eightChannelCriticalProduction
    (R147.radiusK (radii C))
    (R147.radiusP (radii C))
    (R147.radiusQ (radii C))
    (R140.physicalEightAmplitudes (R144.projectorComponents T))
  ≡
  R169.rawCurlGapProduction
    (R147.radiusK (radii C))
    (R147.radiusP (radii C))
    (R147.radiusQ (radii C))
    (R170.rawCurlSlotK E (R144.k T) (R144.uK T) (R144.uP T) (R144.uQ T))
    (R170.rawCurlSlotP E (R144.p T) (R144.uK T) (R144.uP T) (R144.uQ T))
    (R170.rawCurlSlotQ E (R144.q T) (R144.uK T) (R144.uP T) (R144.uQ T))
completeCriticalProductionIsRawCurlGapForm {E = E} {S = S} T C =
  trans
    (R144.criticalProductionIsNormalizedCurlSlotProduction
      (R147.radiusK (radii C))
      (R147.radiusP (radii C))
      (R147.radiusQ (radii C)) T)
    (trans normalizedToInverseRaw
      (R169.normalizedSlotProductionIsRawCurlGapProduction
        (radii C) rawK rawP rawQ))
  where
  rawK = R170.rawCurlSlotK E (R144.k T) (R144.uK T) (R144.uP T) (R144.uQ T)
  rawP = R170.rawCurlSlotP E (R144.p T) (R144.uK T) (R144.uP T) (R144.uQ T)
  rawQ = R170.rawCurlSlotQ E (R144.q T) (R144.uK T) (R144.uP T) (R144.uQ T)

  normalizedToInverseRaw :
    R138.helicitySlotProduction
      (R147.radiusK (radii C))
      (R147.radiusP (radii C))
      (R147.radiusQ (radii C))
      (R144.normalizedCurlSlotK E S (R144.k T) (R144.uK T) (R144.uP T) (R144.uQ T))
      (R144.normalizedCurlSlotP E S (R144.p T) (R144.uK T) (R144.uP T) (R144.uQ T))
      (R144.normalizedCurlSlotQ E S (R144.q T) (R144.uK T) (R144.uP T) (R144.uQ T))
    ≡ R169.normalizedSlotProductionFromRaw (radii C) rawK rawP rawQ
  normalizedToInverseRaw
    rewrite inverseKMeaning C | inversePMeaning C | inverseQMeaning C
          | R170.normalizedSlotKFactorsInverse E S (R144.k T) (R144.uK T) (R144.uP T) (R144.uQ T)
          | R170.normalizedSlotPFactorsInverse E S (R144.p T) (R144.uK T) (R144.uP T) (R144.uQ T)
          | R170.normalizedSlotQFactorsInverse E S (R144.q T) (R144.uK T) (R144.uP T) (R144.uQ T) = refl

round171CompleteEightChannelRawCurlGapWeldClosed : Bool
round171CompleteEightChannelRawCurlGapWeldClosed = true

round171CriticalCoefficientContainsInverseRadius : Bool
round171CriticalCoefficientContainsInverseRadius = false

round171GlobalRawCurlGapPaymentClosed : Bool
round171GlobalRawCurlGapPaymentClosed = false

round171PackageAClosed : Bool
round171PackageAClosed = false

round171CompleteEightChannelRawCurlGapWeldClosedIsTrue :
  round171CompleteEightChannelRawCurlGapWeldClosed ≡ true
round171CompleteEightChannelRawCurlGapWeldClosedIsTrue = refl

round171PackageAClosedIsFalse : round171PackageAClosed ≡ false
round171PackageAClosedIsFalse = refl
