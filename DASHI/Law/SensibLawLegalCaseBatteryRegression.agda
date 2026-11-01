module DASHI.Law.SensibLawLegalCaseBatteryRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.SensibLawLegalCaseBatteryExact as Battery

boundary : Battery.LegalCaseBatteryBoundary
boundary = Battery.canonicalLegalCaseBatteryBoundary

differentBehaviours :
  Battery.batteryTestsDifferentJoinBehaviours boundary ≡ true
differentBehaviours =
  Battery.batteryTestsDifferentJoinBehavioursIsTrue boundary

noPreloadedMabo :
  Battery.batteryPreloadsDesiredMaboJoins boundary ≡ false
noPreloadedMabo =
  Battery.batteryPreloadsDesiredMaboJoinsIsFalse boundary

citationNotJoin :
  Battery.yindjibarndiCitationSeedEqualsReviewedJoin boundary ≡ false
citationNotJoin =
  Battery.yindjibarndiCitationSeedEqualsReviewedJoinIsFalse boundary

munkaraWrongTypePreserved :
  Battery.munkaraSharedContextPaysUnrelatedStatutoryElement boundary ≡ false
munkaraWrongTypePreserved =
  Battery.munkaraSharedContextPaysUnrelatedStatutoryElementIsFalse boundary

pabaiNoDoctrineTransfer :
  Battery.pabaiStructuralAnalogyTransfersSubstantiveDoctrine boundary ≡ false
pabaiNoDoctrineTransfer =
  Battery.pabaiStructuralAnalogyTransfersSubstantiveDoctrineIsFalse boundary

murujugaOpenDiscovery :
  Battery.murujugaMustDiscoverMabo boundary ≡ false
murujugaOpenDiscovery =
  Battery.murujugaMustDiscoverMaboIsFalse boundary
