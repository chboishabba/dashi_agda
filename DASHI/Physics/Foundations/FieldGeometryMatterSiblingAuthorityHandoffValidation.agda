module DASHI.Physics.Foundations.FieldGeometryMatterSiblingAuthorityHandoffValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)

import DASHI.Physics.Foundations.FieldGeometryMatterSiblingAuthorityHandoffExact as H

magno-open : H.openSiblingObserved H.magnoThermRoute ≡ true
magno-open = refl

fusion-no-import : H.theoremAuthorityImportedHere H.fusionPropulsionRoute ≡ false
fusion-no-import = refl

rocketdyne-no-empirical-import : H.empiricalAuthorityImportedHere H.rocketdyneRoute ≡ false
rocketdyne-no-empirical-import = refl

scientist-handoff-not-promotion : H.scientistAdjacencyDoesNotPromoteCommonProgramme H.canonicalSiblingAuthorityHandoffBoundary ≡ true
scientist-handoff-not-promotion = refl

common-programme-not-targeting : H.commonProgrammeDoesNotPromoteTargeting H.canonicalSiblingAuthorityHandoffBoundary ≡ true
common-programme-not-targeting = refl
