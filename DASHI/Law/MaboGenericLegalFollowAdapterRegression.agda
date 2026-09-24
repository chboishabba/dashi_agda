module DASHI.Law.MaboGenericLegalFollowAdapterRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.MaboGenericLegalFollowAdapterExact as Mabo

boundary : Mabo.MaboGenericLegalFollowAdapterBoundary
boundary = Mabo.canonicalMaboGenericLegalFollowAdapterBoundary

reusesGenericKernel :
  Mabo.maboUsesGenericReviewedDeltaKernel boundary ≡ true
reusesGenericKernel =
  Mabo.maboUsesGenericReviewedDeltaKernelIsTrue boundary

doesNotRequireContractDoctrine :
  Mabo.maboRequiresContractDoctrine boundary ≡ false
doesNotRequireContractDoctrine =
  Mabo.maboRequiresContractDoctrineIsFalse boundary

rawSourceCannotPromote :
  Mabo.maboRawSourceMayBecomeReviewedDelta boundary ≡ false
rawSourceCannotPromote =
  Mabo.maboRawSourceMayBecomeReviewedDeltaIsFalse boundary

missingReviewCannotBeFabricated :
  Mabo.missingMaboIdentityReviewMayBeFabricated boundary ≡ false
missingReviewCannotBeFabricated =
  Mabo.missingMaboIdentityReviewMayBeFabricatedIsFalse boundary
