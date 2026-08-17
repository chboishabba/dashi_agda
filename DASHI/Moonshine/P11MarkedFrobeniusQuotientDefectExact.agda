module DASHI.Moonshine.P11MarkedFrobeniusQuotientDefectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Adel Betina and Emmanuel Lecouturier,
-- "Congruence formulae for Legendre modular polynomials",
-- Journal of Number Theory 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton, 1985.
-- DOI: 10.1515/9781400881710.
--
-- DASHI CONTRIBUTION
--
-- Compute the exact Frobenius orbit spectrum on the source-native p=11 full
-- level-2 five-state carrier:
--
--   fixed  = b0,b1,b2  (3),
--   paired = {a0,a1}   (1),
--   total  = 5.
--
-- Forgetting level 2 sends a0 and a1 to the same coarse j=0 supersingular
-- class.  Thus the quotient erases the marked Frobenius two-orbit and the
-- coarse carrier becomes fully fixed.  This is an arithmetic instance of the
-- general rule that quotient-observable agreement does not identify fine
-- states or preserve every dynamical orbit defect.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (zero; suc)
open import Data.Sum using (inj₁; inj₂)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Foundations.FibreConstantObservableExact as Fibre
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11MarkedX2FrobeniusFrickeExact as MarkedF
import DASHI.Moonshine.P11GeometricFrobeniusRealizationExact as CoarseF
import DASHI.Moonshine.P11Fine5FibreObservableBridgeExact as Fibre5

------------------------------------------------------------------------
-- Exact marked normal form: fixed=3, paired=1.
------------------------------------------------------------------------

p11MarkedFrobeniusSpectrum : Orbit.InvolutionOrbitSpectrum
p11MarkedFrobeniusSpectrum = Orbit.involution-orbit-spectrum 3 1 5 refl

P11MarkedNormal : Set
P11MarkedNormal = Orbit.OrbitNormalFormCarrier 3 1

markedToNormal : Fine.P11Fine5 → P11MarkedNormal
markedToNormal Fine.b0 = inj₁ zero
markedToNormal Fine.b1 = inj₁ (suc zero)
markedToNormal Fine.b2 = inj₁ (suc (suc zero))
markedToNormal Fine.a0 = inj₂ (zero , Orbit.bit0)
markedToNormal Fine.a1 = inj₂ (zero , Orbit.bit1)

markedFromNormal : P11MarkedNormal → Fine.P11Fine5
markedFromNormal (inj₁ zero) = Fine.b0
markedFromNormal (inj₁ (suc zero)) = Fine.b1
markedFromNormal (inj₁ (suc (suc zero))) = Fine.b2
markedFromNormal (inj₂ (zero , Orbit.bit0)) = Fine.a0
markedFromNormal (inj₂ (zero , Orbit.bit1)) = Fine.a1

markedFromAfterTo :
  (x : Fine.P11Fine5) → markedFromNormal (markedToNormal x) ≡ x
markedFromAfterTo Fine.a0 = refl
markedFromAfterTo Fine.a1 = refl
markedFromAfterTo Fine.b0 = refl
markedFromAfterTo Fine.b1 = refl
markedFromAfterTo Fine.b2 = refl

markedToAfterFrom :
  (x : P11MarkedNormal) → markedToNormal (markedFromNormal x) ≡ x
markedToAfterFrom (inj₁ zero) = refl
markedToAfterFrom (inj₁ (suc zero)) = refl
markedToAfterFrom (inj₁ (suc (suc zero))) = refl
markedToAfterFrom (inj₂ (zero , Orbit.bit0)) = refl
markedToAfterFrom (inj₂ (zero , Orbit.bit1)) = refl

markedIntertwinesFrobenius :
  (x : Fine.P11Fine5) →
  markedToNormal (MarkedF.markedFrobenius x)
  ≡ Orbit.orbitInvolution (markedToNormal x)
markedIntertwinesFrobenius Fine.a0 = refl
markedIntertwinesFrobenius Fine.a1 = refl
markedIntertwinesFrobenius Fine.b0 = refl
markedIntertwinesFrobenius Fine.b1 = refl
markedIntertwinesFrobenius Fine.b2 = refl

p11MarkedNormalFormRealization :
  Orbit.InvolutionNormalFormRealization
    Fine.P11Fine5
    MarkedF.markedFrobenius
    p11MarkedFrobeniusSpectrum
p11MarkedNormalFormRealization = record
  { Orbit.toNormal = markedToNormal
  ; Orbit.fromNormal = markedFromNormal
  ; Orbit.fromAfterTo = markedFromAfterTo
  ; Orbit.toAfterFrom = markedToAfterFrom
  ; Orbit.intertwinesInvolution = markedIntertwinesFrobenius
  }

p11MarkedFixedCountIsThree :
  Orbit.fixedOrbitCount p11MarkedFrobeniusSpectrum ≡ 3
p11MarkedFixedCountIsThree = refl

p11MarkedPairCountIsOne :
  Orbit.pairedOrbitCount p11MarkedFrobeniusSpectrum ≡ 1
p11MarkedPairCountIsOne = refl

p11MarkedNotFullyFixed : Orbit.fullyFixed p11MarkedFrobeniusSpectrum ≡ false
p11MarkedNotFullyFixed = refl

------------------------------------------------------------------------
-- Forgetting level 2 collapses the marked pair to one coarse fixed class.
------------------------------------------------------------------------

a0a1SameCoarseClass : Fine.projectFine5 Fine.a0 ≡ Fine.projectFine5 Fine.a1
a0a1SameCoarseClass = refl

a0a1DistinctMarkedPoints : Fine.a0 ≡ Fine.a1 → ⊥
a0a1DistinctMarkedPoints ()

markedFrobeniusPairProjectsToSameClass :
  Fine.projectFine5 (MarkedF.markedFrobenius Fine.a0)
  ≡ Fine.projectFine5 Fine.a0
markedFrobeniusPairProjectsToSameClass =
  MarkedF.markedFrobeniusPreservesJClass Fine.a0

coarseP11FullyFixed :
  Orbit.fullyFixed CoarseF.p11NormalFormRealization.spectrum ≡ true
coarseP11FullyFixed = refl

-- Use the generic quotient theorem directly: every coarse class code is
-- constant on the marked fibres even though the marked Frobenius pair survives
-- upstairs.
coarseObservableErasesPairDistinction :
  Fibre5.fineClassCode Fine.a0 ≡ Fibre5.fineClassCode Fine.a1
coarseObservableErasesPairDistinction = refl

record P11MarkedFrobeniusQuotientBoundary : Set where
  field
    markedThreeFixedOnePairRealized : Bool
    markedThreeFixedOnePairRealizedIsTrue :
      markedThreeFixedOnePairRealized ≡ true

    markedPairCollapsedByCoarseProjection : Bool
    markedPairCollapsedByCoarseProjectionIsTrue :
      markedPairCollapsedByCoarseProjection ≡ true

    coarseCarrierFullyFixed : Bool
    coarseCarrierFullyFixedIsTrue : coarseCarrierFullyFixed ≡ true

    markedAllFixedPromotedToOggSelector : Bool
    markedAllFixedPromotedToOggSelectorIsFalse :
      markedAllFixedPromotedToOggSelector ≡ false

canonicalP11MarkedFrobeniusQuotientBoundary :
  P11MarkedFrobeniusQuotientBoundary
canonicalP11MarkedFrobeniusQuotientBoundary = record
  { markedThreeFixedOnePairRealized = true
  ; markedThreeFixedOnePairRealizedIsTrue = refl
  ; markedPairCollapsedByCoarseProjection = true
  ; markedPairCollapsedByCoarseProjectionIsTrue = refl
  ; coarseCarrierFullyFixed = true
  ; coarseCarrierFullyFixedIsTrue = refl
  ; markedAllFixedPromotedToOggSelector = false
  ; markedAllFixedPromotedToOggSelectorIsFalse = refl
  }
