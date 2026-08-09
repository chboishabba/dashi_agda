module DASHI.Moonshine.MonsterOggNonarySSPTritBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine",
-- Bulletin of the London Mathematical Society 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- DASHI CONTRIBUTION
--
-- Connect the exact p = 9q+r Ogg table to the repository's canonical signed
-- SSP trit.  This proves a carrier-level statement only: residue modulo three
-- supplies the low trit, primes above three are nonneutral, p=3 is neutral,
-- and additive complement reverses polarity.  No Monster representation or
-- genus-zero operation is inferred from this projection.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using
  ( NonaryTruth
  ; non-1; non-2; non-3; non-4; non-5; non-7; non-8
  )

open import DASHI.Foundations.SSPTritCarrier using
  ( SSPTrit
  ; sspNegOne
  ; sspZero
  ; sspPosOne
  )

open import DASHI.Foundations.Base369NonaryTritSquareExact using
  ( TritSquare
  ; nonaryDigitToTritSquare
  ; nonaryDigitToLowTrit
  ; negateSSPTrit
  )

import DASHI.Moonshine.MonsterOggNonaryProbeAuthorityExact as Probe
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

oggPrimeResidueDigit : Lane.MonsterPrimeLane → NonaryTruth
oggPrimeResidueDigit Lane.p2 = non-2
oggPrimeResidueDigit Lane.p3 = non-3
oggPrimeResidueDigit Lane.p5 = non-5
oggPrimeResidueDigit Lane.p7 = non-7
oggPrimeResidueDigit Lane.p11 = non-2
oggPrimeResidueDigit Lane.p13 = non-4
oggPrimeResidueDigit Lane.p17 = non-8
oggPrimeResidueDigit Lane.p19 = non-1
oggPrimeResidueDigit Lane.p23 = non-5
oggPrimeResidueDigit Lane.p29 = non-2
oggPrimeResidueDigit Lane.p31 = non-4
oggPrimeResidueDigit Lane.p41 = non-5
oggPrimeResidueDigit Lane.p47 = non-2
oggPrimeResidueDigit Lane.p59 = non-5
oggPrimeResidueDigit Lane.p71 = non-8

oggPrimeResidueSquare : Lane.MonsterPrimeLane → TritSquare
oggPrimeResidueSquare prime =
  nonaryDigitToTritSquare (oggPrimeResidueDigit prime)

oggPrimeResidueTrit : Lane.MonsterPrimeLane → SSPTrit
oggPrimeResidueTrit prime =
  nonaryDigitToLowTrit (oggPrimeResidueDigit prime)

data NonNeutralSSPTrit : SSPTrit → Set where
  negativeNonNeutral : NonNeutralSSPTrit sspNegOne
  positiveNonNeutral : NonNeutralSSPTrit sspPosOne

primeAboveThreeResidueTritNonneutral :
  (prime : Probe.OggPrimeAboveThree) →
  NonNeutralSSPTrit
    (oggPrimeResidueTrit (Probe.toPrime prime))
primeAboveThreeResidueTritNonneutral Probe.above5 = negativeNonNeutral
primeAboveThreeResidueTritNonneutral Probe.above7 = positiveNonNeutral
primeAboveThreeResidueTritNonneutral Probe.above11 = negativeNonNeutral
primeAboveThreeResidueTritNonneutral Probe.above13 = positiveNonNeutral
primeAboveThreeResidueTritNonneutral Probe.above17 = negativeNonNeutral
primeAboveThreeResidueTritNonneutral Probe.above19 = positiveNonNeutral
primeAboveThreeResidueTritNonneutral Probe.above23 = negativeNonNeutral
primeAboveThreeResidueTritNonneutral Probe.above29 = negativeNonNeutral
primeAboveThreeResidueTritNonneutral Probe.above31 = positiveNonNeutral
primeAboveThreeResidueTritNonneutral Probe.above41 = negativeNonNeutral
primeAboveThreeResidueTritNonneutral Probe.above47 = negativeNonNeutral
primeAboveThreeResidueTritNonneutral Probe.above59 = negativeNonNeutral
primeAboveThreeResidueTritNonneutral Probe.above71 = negativeNonNeutral

threeResidueTritNeutral :
  oggPrimeResidueTrit Lane.p3 ≡ sspZero
threeResidueTritNeutral = refl

unitResidueDigit :
  ∀ {residue} → Probe.UnitResidue9 residue → NonaryTruth
unitResidueDigit Probe.unit1 = non-1
unitResidueDigit Probe.unit2 = non-2
unitResidueDigit Probe.unit4 = non-4
unitResidueDigit Probe.unit5 = non-5
unitResidueDigit Probe.unit7 = non-7
unitResidueDigit Probe.unit8 = non-8

unitResidueTrit :
  ∀ {residue} → Probe.UnitResidue9 residue → SSPTrit
unitResidueTrit unit =
  nonaryDigitToLowTrit (unitResidueDigit unit)

complementReversesResidueTrit :
  ∀ {residue} →
  (unit : Probe.UnitResidue9 residue) →
  unitResidueTrit (Probe.complementUnitWitness unit)
  ≡ negateSSPTrit (unitResidueTrit unit)
complementReversesResidueTrit Probe.unit1 = refl
complementReversesResidueTrit Probe.unit2 = refl
complementReversesResidueTrit Probe.unit4 = refl
complementReversesResidueTrit Probe.unit5 = refl
complementReversesResidueTrit Probe.unit7 = refl
complementReversesResidueTrit Probe.unit8 = refl

-- The existing direct/counter orientation is defined inside each complement
-- mode.  Its conversion to the low residue trit is therefore mode-dependent:
-- mode27 carries the opposite local convention from modes18 and45.
modeOrientationToSSPTrit :
  Probe.UnitComplementMode → Probe.UnitOrientation → SSPTrit
modeOrientationToSSPTrit Probe.mode18 Probe.directOrientation = sspPosOne
modeOrientationToSSPTrit Probe.mode18 Probe.counterOrientation = sspNegOne
modeOrientationToSSPTrit Probe.mode27 Probe.directOrientation = sspNegOne
modeOrientationToSSPTrit Probe.mode27 Probe.counterOrientation = sspPosOne
modeOrientationToSSPTrit Probe.mode45 Probe.directOrientation = sspPosOne
modeOrientationToSSPTrit Probe.mode45 Probe.counterOrientation = sspNegOne

modeOrientationRecoversResidueTrit :
  ∀ {residue} →
  (unit : Probe.UnitResidue9 residue) →
  modeOrientationToSSPTrit
    (Probe.unitComplementMode unit)
    (Probe.unitOrientation unit)
  ≡ unitResidueTrit unit
modeOrientationRecoversResidueTrit Probe.unit1 = refl
modeOrientationRecoversResidueTrit Probe.unit2 = refl
modeOrientationRecoversResidueTrit Probe.unit4 = refl
modeOrientationRecoversResidueTrit Probe.unit5 = refl
modeOrientationRecoversResidueTrit Probe.unit7 = refl
modeOrientationRecoversResidueTrit Probe.unit8 = refl
