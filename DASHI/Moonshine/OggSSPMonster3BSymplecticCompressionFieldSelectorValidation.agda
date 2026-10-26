module DASHI.Moonshine.OggSSPMonster3BSymplecticCompressionFieldSelectorValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Moonshine.OggSSPMonster3BSymplecticCompressionFieldSelectorExact as Cut

compressionRouteDoesNotRequireInvariantX6 :
  Cut.wholeNormalizerX6InvariantSubmoduleRequired
    Cut.canonicalSymplecticCompressionFieldSelectorBoundary
  ≡ false
compressionRouteDoesNotRequireInvariantX6 = refl

compressionRouteDoesNotRequireStabilizer :
  Cut.lagrangianStabilizerRequiredForFieldSelector
    Cut.canonicalSymplecticCompressionFieldSelectorBoundary
  ≡ false
compressionRouteDoesNotRequireStabilizer = refl

genericCompressionLinearityPaid :
  Cut.compressionLinearityPaidGenerically
    Cut.canonicalSymplecticCompressionFieldSelectorBoundary
  ≡ true
genericCompressionLinearityPaid = refl

selectedCompressionCanCompileToExistingK6Selector :
  Cut.selectedCompressionCompilesToK6Selector
    Cut.canonicalSymplecticCompressionFieldSelectorBoundary
  ≡ true
selectedCompressionCanCompileToExistingK6Selector = refl
