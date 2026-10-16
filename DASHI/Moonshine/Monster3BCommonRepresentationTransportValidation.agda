module DASHI.Moonshine.Monster3BCommonRepresentationTransportValidation where

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
