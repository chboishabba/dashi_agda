module DASHI.Physics.Electromagnetism.MagnetocaloricFieldConsumerExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as U1
import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial as MCE
import DASHI.Physics.Units.MagnetocaloricSIConsumerExact as MSI

------------------------------------------------------------------------
-- Electromagnetic application consumer for magnetocaloric systems.
--
-- U(1)/Maxwell application fields are kept separate from the non-abelian
-- Yang-Mills Clay lane by the existing U1 socket.  This bridge additionally
-- keeps measured B (tesla) separate from H (A/m); a concrete material law must
-- state which field convention it consumes and provide the constitutive link.
------------------------------------------------------------------------

record MagnetocaloricU1FieldBridge
  (M : MCE.MagnetocaloricMaterial) : Set₁ where
  open MCE.MagnetocaloricMaterial M
  field
    socket : U1.U1ElectromagneticFieldSocket
    metrology : MSI.AMRMeasurementBundle

    fieldState : U1.U1ElectromagneticFieldSocket.FieldState socket
    materialState : MaterialState

    FieldConvention : Set
    ConstitutiveBHRelation : Set
    GeometryIdentification : Set
    FieldWorkIdentification : Set

    fieldConvention : FieldConvention
    constitutiveBHRelation : ConstitutiveBHRelation
    geometryIdentification : GeometryIdentification
    fieldWorkIdentification : FieldWorkIdentification

    maxwellReference : String
    magnetGeometryReference : String
    materialBHReference : String
    validationReference : String

record MagnetocaloricElectromagneticBoundary : Set where
  constructor magnetocaloric-electromagnetic-boundary
  field
    fluxDensityAndFieldStrengthAreDistinct : Bool
    u1FieldSocketDoesNotSupplyMaterialConstitutiveLaw : Bool
    permanentMagnetGeometryRequiresFieldMap : Bool
    superconductingMagnetRequiresFieldMap : Bool
    nonAbelianYMDoesNotProveApplicationMagnetism : Bool
    fieldWorkRequiresMechanicalElectromagneticAccounting : Bool

canonicalMagnetocaloricElectromagneticBoundary : MagnetocaloricElectromagneticBoundary
canonicalMagnetocaloricElectromagneticBoundary =
  magnetocaloric-electromagnetic-boundary true true true true true true
