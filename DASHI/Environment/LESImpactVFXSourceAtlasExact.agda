module DASHI.Environment.LESImpactVFXSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION FOR IMPACT / MARINE / VFX OPERATIONS
--
-- Each source has a bounded role.  A citation does not supply a constitutive
-- calibration, a numerical receipt, or validation for the fictional scene.
------------------------------------------------------------------------

record ImpactVFXSource : Set where
  constructor impact-vfx-source
  field
    authorsOrInstitution : String
    title : String
    venueOrPublisher : String
    identifier : String
    boundedRole : String

open ImpactVFXSource public

newmanMarineHydrodynamics : ImpactVFXSource
newmanMarineHydrodynamics = impact-vfx-source
  "J. N. Newman"
  "Marine Hydrodynamics"
  "The MIT Press, 1977"
  "DOI 10.7551/mitpress/4443.001.0001"
  "marine hydrodynamics, viscous/ideal flow, waves and hydrodynamic loading context; not a scene-specific hull or slamming calibration"

baraffWitkinPhysicallyBasedModeling : ImpactVFXSource
baraffWitkinPhysicallyBasedModeling = impact-vfx-source
  "Andrew Witkin and David Baraff"
  "Physically Based Modeling: Principles and Practice"
  "SIGGRAPH 1997 course notes"
  "stable institutional course-notes source; no DOI asserted"
  "rigid-body, constrained dynamics and contact-simulation method context; not constitutive-material authority"

stamStableFluids : ImpactVFXSource
stamStableFluids = impact-vfx-source
  "Jos Stam"
  "Stable Fluids"
  "Proceedings of SIGGRAPH 1999"
  "DOI 10.1145/311535.311548"
  "graphics fluid numerical-method precedent; not an exact Navier-Stokes solution or hydrodynamic validation"

mullerPositionBasedDynamics : ImpactVFXSource
mullerPositionBasedDynamics = impact-vfx-source
  "Matthias Muller; Bruno Heidelberger; Marcus Hennix; John Ratcliff"
  "Position Based Dynamics"
  "Journal of Visual Communication and Image Representation 18(2), 2007"
  "DOI 10.1016/j.jvcir.2007.01.005"
  "position-based constraint technique precedent; not a physical contact or material law"

record SourceUseBoundary : Set where
  constructor source-use-boundary
  field
    marineTextbookDefinesThisFrigateGeometry : Bool
    marineTextbookDefinesThisFrigateGeometryIsFalse : marineTextbookDefinesThisFrigateGeometry ≡ false
    graphicsAlgorithmCertifiesPhysicalAccuracy : Bool
    graphicsAlgorithmCertifiesPhysicalAccuracyIsFalse : graphicsAlgorithmCertifiesPhysicalAccuracy ≡ false
    citationPaysMaterialCalibration : Bool
    citationPaysMaterialCalibrationIsFalse : citationPaysMaterialCalibration ≡ false
    citationPaysNumericalConvergence : Bool
    citationPaysNumericalConvergenceIsFalse : citationPaysNumericalConvergence ≡ false

canonicalSourceUseBoundary : SourceUseBoundary
canonicalSourceUseBoundary =
  source-use-boundary false refl false refl false refl false refl
