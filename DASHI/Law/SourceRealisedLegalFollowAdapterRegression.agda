module DASHI.Law.SourceRealisedLegalFollowAdapterRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.SourceRealisedLegalFollowAdapterExact as Adapter

boundary : Adapter.SourceRealisedLegalFollowAdapterBoundary
boundary = Adapter.canonicalSourceRealisedLegalFollowAdapterBoundary

usesGenericKernel :
  Adapter.sourceRealisedLegalDomainUsesGenericKernel boundary ≡ true
usesGenericKernel =
  Adapter.sourceRealisedLegalDomainUsesGenericKernelIsTrue boundary

negligenceSharesKernel :
  Adapter.negligenceMayUseSameKernelAsNativeTitle boundary ≡ true
negligenceSharesKernel =
  Adapter.negligenceMayUseSameKernelAsNativeTitleIsTrue boundary

reviewPaysSelectedResidual :
  Adapter.reviewedDeltaMustPaySelectedResidual boundary ≡ true
reviewPaysSelectedResidual =
  Adapter.reviewedDeltaMustPaySelectedResidualIsTrue boundary

noSilentWorldChange :
  Adapter.reviewedDeltaMaySilentlyChangeWorldCoordinate boundary ≡ false
noSilentWorldChange =
  Adapter.reviewedDeltaMaySilentlyChangeWorldCoordinateIsFalse boundary

noAuthorityPromotion :
  Adapter.reviewedDeltaCreatesSemanticAuthority boundary ≡ false
noAuthorityPromotion =
  Adapter.reviewedDeltaCreatesSemanticAuthorityIsFalse boundary
