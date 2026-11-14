module DASHI.Physics.Chemistry.AmmoniaC3RegularRepresentationValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaC3RegularRepresentationExact as R

nh3RegularBlockPaid :
  R.RegularC3CrossDomainBoundary.nh3A1PlusERestrictsToOneRegularC3
    R.canonicalRegularC3CrossDomainBoundary ≡ true
nh3RegularBlockPaid = refl

oneBlockCancels : R.ammoniaA1PlusEGeneratorAmplitude ≡ R.zeroAmplitude
oneBlockCancels = R.ammoniaA1PlusEGeneratorCancels

monsterBulkUses65610Copies : R.monsterRegularBlockMultiplicity ≡ 65610
monsterBulkUses65610Copies = refl

monsterResidualIs53 : R.monsterResidualMultiplicity ≡ 53
monsterResidualIs53 = refl

sameMotifNotSameModule :
  R.RegularC3CrossDomainBoundary.sameRegularC3MotifCreatesMonsterModule
    R.canonicalRegularC3CrossDomainBoundary ≡ false
sameMotifNotSameModule = refl
