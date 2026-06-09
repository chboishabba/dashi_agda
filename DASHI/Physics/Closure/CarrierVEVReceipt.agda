module DASHI.Physics.Closure.CarrierVEVReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MassiveSubspaceOSPositivity as Massive

data CarrierVEVStatus : Set where
  w4HiggsSectorVEVCandidate : CarrierVEVStatus

vevBoundaryStatement : String
vevBoundaryStatement =
  "The carrier needs a Higgs/VEV calibration before bare Yukawa receipts can become physical Hamiltonian or mass-matrix entries."

record CarrierVEVReceipt : Setω where
  field
    massiveSubspaceReceipt :
      Massive.MassiveSubspaceOSPositivityReceipt

    physicalMassMatrixRequiresVEV :
      Massive.physicalMassMatrixRequiresVEV massiveSubspaceReceipt ≡ true

    status :
      CarrierVEVStatus

    vevFromW4Sector :
      Bool

    vevFromW4SectorIsCandidate :
      vevFromW4Sector ≡ true

    higgsExpectationValueIdentified :
      Bool

    higgsExpectationValueIdentifiedIsFalse :
      higgsExpectationValueIdentified ≡ false

    vevNumericalValueConstructed :
      Bool

    vevNumericalValueConstructedIsFalse :
      vevNumericalValueConstructed ≡ false

    physicalMassMatrixFromVEV :
      Bool

    physicalMassMatrixFromVEVIsFalse :
      physicalMassMatrixFromVEV ≡ false

    os3ReflectionPositivityResolved :
      Bool

    os3ReflectionPositivityResolvedIsFalse :
      os3ReflectionPositivityResolved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ vevBoundaryStatement

    receiptBoundary :
      List String

open CarrierVEVReceipt public

canonicalCarrierVEVReceipt : CarrierVEVReceipt
canonicalCarrierVEVReceipt =
  record
    { massiveSubspaceReceipt =
        Massive.canonicalMassiveSubspaceOSPositivityReceipt
    ; physicalMassMatrixRequiresVEV =
        refl
    ; status =
        w4HiggsSectorVEVCandidate
    ; vevFromW4Sector =
        true
    ; vevFromW4SectorIsCandidate =
        refl
    ; higgsExpectationValueIdentified =
        false
    ; higgsExpectationValueIdentifiedIsFalse =
        refl
    ; vevNumericalValueConstructed =
        false
    ; vevNumericalValueConstructedIsFalse =
        refl
    ; physicalMassMatrixFromVEV =
        false
    ; physicalMassMatrixFromVEVIsFalse =
        refl
    ; os3ReflectionPositivityResolved =
        false
    ; os3ReflectionPositivityResolvedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; boundaryStatement =
        vevBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; receiptBoundary =
        "The W4/Higgs lane is recorded as the carrier VEV candidate"
        ∷ "No numerical VEV, physical mass matrix, or OS3 reflection-positive Hamiltonian is constructed"
        ∷ "The VEV candidate does not promote Yang-Mills or any Clay flag"
        ∷ []
    }

carrierVEVStillOpen :
  physicalMassMatrixFromVEV canonicalCarrierVEVReceipt ≡ false
carrierVEVStillOpen =
  refl

