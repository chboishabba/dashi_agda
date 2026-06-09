module DASHI.Physics.Closure.CKMUnitarityFromCarrier where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMExactWitnesses as Exact
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.YM.BiunitaryDiagonalization as Biunitary

------------------------------------------------------------------------
-- Exact CKM unitarity from the carrier-derived witness chain.
--
-- The repository already exposes a concrete diagonal biunitary witness and
-- an exact unitarity residual witness for the carrier-derived CKM lane.  The
-- role of this module is to package those concrete witnesses into a single
-- receipt that records the carrier-level identity closure directly, without
-- adding any postulates or synthetic algebra.

record CKMUnitaryReceipt : Setω where
  field
    exactWitnessChain :
      Exact.CKMExactWitnessChain

    exactBiunitaryDiagonalization :
      Exact.ExactBiunitaryDiagonalizationWitness

    diagonalBiunitaryWitness :
      Biunitary.DiagonalBiunitaryWitness

    residualWitness :
      Exact.UnitarityResidualWitness

    carrierCKMMatrix :
      Matter.MixingMatrix

    carrierCKMMatrixIsIdentity :
      carrierCKMMatrix ≡ Matter.identityMixingMatrix

    carrierUnitarityClosure :
      Matter.leftIdentityMixingProduct carrierCKMMatrix ≡ carrierCKMMatrix

    splittingFieldEigenbasisLedger :
      Exact.CKMSplittingFieldEigenbasisFailClosedLedger

    weakMassBasisIdentificationConstructed :
      Bool

    weakMassBasisIdentificationConstructedIsFalse :
      weakMassBasisIdentificationConstructed ≡ false

    physicalCKMPromotionConstructed :
      Bool

    physicalCKMPromotionConstructedIsFalse :
      physicalCKMPromotionConstructed ≡ false

    unitaryBoundary :
      List String

open CKMUnitaryReceipt public

canonicalCKMUnitary : CKMUnitaryReceipt
canonicalCKMUnitary = record
  { exactWitnessChain = Exact.canonicalCKMExactWitnessChain
  ; exactBiunitaryDiagonalization =
      Exact.canonicalExactBiunitaryDiagonalizationWitness
  ; diagonalBiunitaryWitness =
      Biunitary.canonicalDiagonalBiunitaryWitness
  ; residualWitness = Exact.canonicalUnitarityResidualWitness
  ; carrierCKMMatrix = Matter.identityMixingMatrix
  ; carrierCKMMatrixIsIdentity = refl
  ; carrierUnitarityClosure = refl
  ; splittingFieldEigenbasisLedger =
      Exact.canonicalCKMSplittingFieldEigenbasisFailClosedLedger
  ; weakMassBasisIdentificationConstructed = false
  ; weakMassBasisIdentificationConstructedIsFalse = refl
  ; physicalCKMPromotionConstructed = false
  ; physicalCKMPromotionConstructedIsFalse = refl
  ; unitaryBoundary =
      "The exact CKM witness chain is concrete in the repository"
      ∷ "The diagonal biunitary witness closes on the identity matrix case"
      ∷ "The residual witness records exact unitarity at the carrier surface"
      ∷ "Splitting-field/eigenbasis and physical weak-to-mass basis promotion remain fail-closed blockers"
      ∷ []
  }

canonicalCKMUnitaryKeepsPhysicalPromotionClosed :
  physicalCKMPromotionConstructed canonicalCKMUnitary
  ≡
  false
canonicalCKMUnitaryKeepsPhysicalPromotionClosed =
  refl
