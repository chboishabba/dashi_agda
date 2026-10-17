module DASHI.Analysis.CollatzSyracuseCylinderInterfaceMatchExact where

------------------------------------------------------------------------
-- FULL CYLINDER INTERFACE MATCH
--
-- Hyperfabric-style seam certificate: every coordinate needed by downstream
-- transport is matched explicitly.  Partial agreement never promotes itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

record CylinderInterface : Set where
  constructor cylinderInterface
  field
    cylinderCode : Nat
    branchOrientation : Nat
    normalizationCode : Nat
    timeAlignment : Nat
    observableOrientation : Nat

open CylinderInterface public

record CollatzCylinderInterfaceMatch
    (left right : CylinderInterface) : Set where
  constructor collatzCylinderInterfaceMatch
  field
    cylinderMatches : cylinderCode left ≡ cylinderCode right
    branchMatches : branchOrientation left ≡ branchOrientation right
    normalizationMatches : normalizationCode left ≡ normalizationCode right
    timeMatches : timeAlignment left ≡ timeAlignment right
    observableMatches : observableOrientation left ≡ observableOrientation right

open CollatzCylinderInterfaceMatch public

identityInterfaceMatch :
  (interface : CylinderInterface) →
  CollatzCylinderInterfaceMatch interface interface
identityInterfaceMatch interface =
  collatzCylinderInterfaceMatch refl refl refl refl refl

record CylinderInterfaceBoundary : Set where
  constructor cylinderInterfaceBoundary
  field
    oneCoordinateAgreementSuffices : Nat
    allFiveCoordinatesRequired : Nat
    seamRewritesDynamicsAutomatically : Nat

canonicalCylinderInterfaceBoundary : CylinderInterfaceBoundary
canonicalCylinderInterfaceBoundary = cylinderInterfaceBoundary 0 1 0
