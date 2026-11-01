module DASHI.Physics.Closure.NSTriadKNFixedOutputConcreteSlotCollisionWitnessValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Closure.NSTriadKNFixedOutputConcreteSlotCollisionWitnessExact as Witness

concreteDistinctCCCollisionWitnessIsClosed :
  Witness.roundFixedOutputConcreteDistinctCCCollisionWitnessConstructed ≡ true
concreteDistinctCCCollisionWitnessIsClosed = refl

incidenceOnlyRadialPlueckerNoGoRemainsFailClosed :
  Witness.roundFixedOutputIncidenceOnlyRadialPlueckerCoercivityRefuted ≡ false
incidenceOnlyRadialPlueckerNoGoRemainsFailClosed = refl

clayPromotionRemainsFalse :
  Witness.roundFixedOutputConcreteCollisionClayPromotion ≡ false
clayPromotionRemainsFalse = refl
