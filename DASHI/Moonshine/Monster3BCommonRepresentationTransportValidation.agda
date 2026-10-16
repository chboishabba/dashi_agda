module DASHI.Moonshine.Monster3BCommonRepresentationTransportValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BCommonRepresentationTransportExact as Target

open Target

modelBoundary : Boundary
modelBoundary = canonicalBoundary

modelAttachmentTyped : modelSideAttachmentTyped modelBoundary ≡ true
modelAttachmentTyped = refl

actualAttachmentStillOpen : actualConstituentAttachmentInhabited modelBoundary ≡ false
actualAttachmentStillOpen = refl

commonTheoryStillOpen : commonRepresentationTheoryInhabited modelBoundary ≡ false
commonTheoryStillOpen = refl

sameObjectHZetaStillOpen : actualHZetaSameObjectInhabited modelBoundary ≡ false
sameObjectHZetaStillOpen = refl
