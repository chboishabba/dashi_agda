module DASHI.Interop.LocalGlobalBundleGluingRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.StageValuationBundleAtlas as Stage
import DASHI.Interop.LocalGlobalBundleGluingExact as Gluing
import DASHI.Combinatorics.GraphColouringBundleGluingAdapterExact as Colouring
import DASHI.ComputerScience.RSA260BundleGluingAdapterExact as RSA
import DASHI.Reasoning.WavePantsBundleGluingAdapterExact as Wave

------------------------------------------------------------------------
-- RED/GREEN contract: reuse BundleSheaf as the local/global canonical owner;
-- domain adapters must report their actual promotion strength instead of
-- manufacturing exact gluing from local validity.
------------------------------------------------------------------------

compatibleLocalFamilyGluesAndRestrictsSurface =
  Gluing.compatibleLocalFamilyGluesAndRestricts

localValidityAutomaticallyCreatesGlobalSection : Bool
localValidityAutomaticallyCreatesGlobalSection =
  Gluing.LocalGlobalGluingBoundary.localValidityAutomaticallyCreatesGlobalSection
    Gluing.canonicalLocalGlobalGluingBoundary

localValidityAutomaticallyCreatesGlobalSectionIsFalse :
  localValidityAutomaticallyCreatesGlobalSection ≡ false
localValidityAutomaticallyCreatesGlobalSectionIsFalse = refl

graphColouringBundlePromotionPaid : Bool
graphColouringBundlePromotionPaid =
  Colouring.GraphColouringBundleStatus.bundleSheafPromotionPaid
    Colouring.graphColouringBundleStatus

graphColouringBundlePromotionPaidIsFalse :
  graphColouringBundlePromotionPaid ≡ false
graphColouringBundlePromotionPaidIsFalse = refl

rsaBundlePromotionPaid : Bool
rsaBundlePromotionPaid =
  RSA.RSA260BundleStatus.bundleSheafPromotionPaid
    RSA.rsa260BundleStatus

rsaBundlePromotionPaidIsFalse : rsaBundlePromotionPaid ≡ false
rsaBundlePromotionPaidIsFalse = refl

wavePantsBundlePromotionPaid : Bool
wavePantsBundlePromotionPaid =
  Wave.WavePantsBundleStatus.bundleSheafPromotionPaid
    Wave.wavePantsBundleStatus

wavePantsBundlePromotionPaidIsFalse :
  wavePantsBundlePromotionPaid ≡ false
wavePantsBundlePromotionPaidIsFalse = refl
