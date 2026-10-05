{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3DistinctF2MarkedSourceSameCarrierExact where

------------------------------------------------------------------------
-- S3a CORRECTION: SAME COMPOSITE CARRIER DOES NOT MEAN SAME MARKED SOURCE.
--
-- The R129 export is the completed marked source selected by the stress lane.
-- A curvature/F^2 insertion is a different composite insertion.  What the
-- preferred Local-C construction needs is that BOTH operators live in the same
-- completed Composite carrier, not that their `SameFamilyMarkedSourceData`
-- records are propositionally equal.
--
-- Consequently the physical F^2 task is constructive:
--
--   construct a MarkedCurvatureCompositeFamily on the exact R129/R109
--   CompletedState/Composite carrier, with the selected polynomial denoting
--   the physical F^2 insertion.
--
-- Once that family exists, recharting Local-C uses its operator map directly,
-- so selected Local-C F^2 = completed marked-curvature F^2 is definitional.
-- No equality with the R129 STRESS marked source is consumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyP3MarkedCurvatureLocalCRechartExact as Rechart

import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact as Curvature
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local

------------------------------------------------------------------------
-- Carrier-level compiler.
------------------------------------------------------------------------

record PhysicalF2MarkedSourceOnLocalCCarrier
    {ContinuumFamily CurvaturePolynomial Position OPECoefficient
     StressTensor Hamiltonian CompletedState Composite : Set}
    {continuityScale : Nuclear.ContinuityScale}
    (baseLocalC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial Composite Position
        OPECoefficient StressTensor Hamiltonian)
    : Set₁ where
  field
    fieldStrengthSquarePolynomial : CurvaturePolynomial

    -- Physical construction target.  The family may contain marked sources for
    -- all curvature polynomials; in particular the selected F^2 source is NOT
    -- constrained to equal any independently selected stress marked source.
    curvatureFamily :
      Curvature.MarkedCurvatureCompositeFamily
        CurvaturePolynomial Position continuityScale CompletedState Composite

open PhysicalF2MarkedSourceOnLocalCCarrier public

physicalF2LocalC :
  ∀ {ContinuumFamily CurvaturePolynomial Position OPECoefficient
      StressTensor Hamiltonian CompletedState Composite continuityScale}
    {baseLocalC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial Composite Position
        OPECoefficient StressTensor Hamiltonian} →
  PhysicalF2MarkedSourceOnLocalCCarrier
    {continuityScale = continuityScale}
    {CompletedState = CompletedState}
    baseLocalC →
  Local.ContinuumLocalOperatorOPEStressTensor
    ContinuumFamily CurvaturePolynomial Composite Position
    OPECoefficient StressTensor Hamiltonian
physicalF2LocalC {baseLocalC = baseLocalC} data =
  Rechart.rechartLocalCOnMarkedCurvature baseLocalC (curvatureFamily data)

selectedLocalCF2IsSelectedMarkedF2 :
  ∀ {ContinuumFamily CurvaturePolynomial Position OPECoefficient
      StressTensor Hamiltonian CompletedState Composite continuityScale}
    {baseLocalC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial Composite Position
        OPECoefficient StressTensor Hamiltonian}
    (data :
      PhysicalF2MarkedSourceOnLocalCCarrier
        {continuityScale = continuityScale}
        {CompletedState = CompletedState}
        baseLocalC) →
  Local.localOperator (physicalF2LocalC data)
    (fieldStrengthSquarePolynomial data)
  ≡
  Curvature.localOperator (curvatureFamily data)
    (fieldStrengthSquarePolynomial data)
selectedLocalCF2IsSelectedMarkedF2 data = refl

------------------------------------------------------------------------
-- Max-cut accounting.
------------------------------------------------------------------------

sameCompositeCarrierDoesNotForceSameMarkedSource : Bool
sameCompositeCarrierDoesNotForceSameMarkedSource = true

r129StressMarkedSourceEqualityNotRequiredForLocalCRechart : Bool
r129StressMarkedSourceEqualityNotRequiredForLocalCRechart = true

remainingF2WorkIsConstructPhysicalMarkedF2Source : Bool
remainingF2WorkIsConstructPhysicalMarkedF2Source = true

oldS3aStressSourceEqualityIsRequired : Bool
oldS3aStressSourceEqualityIsRequired = false
