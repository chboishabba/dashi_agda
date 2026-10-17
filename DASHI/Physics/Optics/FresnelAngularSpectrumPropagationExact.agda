module DASHI.Physics.Optics.FresnelAngularSpectrumPropagationExact where

-- DASHI physical propagation seam for diffraction-coded 3D imaging.
--
-- This module deliberately separates two wave-propagation producers from the
-- downstream camera codec.  A Fresnel/paraxial prediction and an angular-
-- spectrum prediction may be compared only when an explicit same-field
-- receipt is supplied on the selected geometry/wavelength/validity region.
-- No numerical diffraction integral is manufactured by the type layer.

open import Agda.Primitive using (Set; Set₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

record FresnelPropagationReceipt
    (Geometry Wavelength Distance Field : Set) : Set₁ where
  field
    geometry : Geometry
    wavelength : Wavelength
    distance : Distance
    inputField : Field
    fresnelPropagate : Geometry → Wavelength → Distance → Field → Field
    propagatedField : Field
    fresnelWeld :
      propagatedField ≡
      fresnelPropagate geometry wavelength distance inputField
    paraxialValidity : Set
    paraxialValidityReceipt : paraxialValidity

open FresnelPropagationReceipt public

record AngularSpectrumPropagationReceipt
    (Geometry Wavelength Distance Field : Set) : Set₁ where
  field
    geometryAS : Geometry
    wavelengthAS : Wavelength
    distanceAS : Distance
    inputFieldAS : Field
    angularSpectrumPropagate :
      Geometry → Wavelength → Distance → Field → Field
    propagatedFieldAS : Field
    angularSpectrumWeld :
      propagatedFieldAS ≡
      angularSpectrumPropagate
        geometryAS wavelengthAS distanceAS inputFieldAS
    samplingValidity : Set
    samplingValidityReceipt : samplingValidity

open AngularSpectrumPropagationReceipt public

record PropagationAgreement
    {Geometry Wavelength Distance Field : Set}
    (F : FresnelPropagationReceipt Geometry Wavelength Distance Field)
    (A : AngularSpectrumPropagationReceipt Geometry Wavelength Distance Field) : Set₁ where
  field
    sameGeometry : geometry F ≡ geometryAS A
    sameWavelength : wavelength F ≡ wavelengthAS A
    sameDistance : distance F ≡ distanceAS A
    sameInputField : inputField F ≡ inputFieldAS A
    fresnelAngularSpectrumSameField :
      propagatedField F ≡ propagatedFieldAS A
    agreementValidity : Set
    agreementValidityReceipt : agreementValidity

open PropagationAgreement public

-- Important boundary: an approximation-agreement receipt does not make the
-- two propagation algorithms definitionally identical outside its validity
-- region, and neither one by itself identifies a measured camera PSF.
