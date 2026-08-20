module DASHI.Physics.Closure.NSTriadKNViscousWeightedHHLowTensorFactorizationRound89Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- ROUND89 / MOVE THE VISCOUS GEOMETRY INSIDE THE HH TENSOR
--
-- The dead far-gap route estimated the relative-growth factor (p dot q)
-- separately from the HH->low transfer.  That exposes two high-frequency
-- powers before absolute-value majorization and produces a divergent gap
-- ledger.
--
-- The literal ordered advective value is
--
--     w(p,q) = (u_p dot q) u_q.
--
-- For a resonant triad p+q=k and a transverse left input, the already-proved
-- exact relocation gives
--
--     u_p dot q = u_p dot k.
--
-- Therefore the viscously weighted ordered value is exactly
--
--     (p dot q) w(p,q)
--       = (u_p dot k) ((p dot q) u_q).
--
-- This is the Fourier divergence of the rank-one tensor
--
--     (p dot q) u_p tensor u_q,
--
-- and p dot q is itself the contraction obtained from one derivative on each
-- input.  Thus the two derivative powers can be placed INSIDE the tensor
-- before applying the repository's finite periodic HH->low H^{-1} theorem.
--
-- This file proves the exact literal C3 algebra.  It introduces no shell
-- estimate and no positivity/sign hypothesis.  The remaining analytic weld is
-- to realize the derivative-weighted tensor in the existing closed periodic
-- HH->low carrier and identify its two L2 input masses with dissipation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3RelocationInstantiation as Relocation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralAdvectivePressureRHSSplitRound84Exact as AP

inputFrequencyDot :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) →
  Physical.PhysicalTriadIncidence → C3.Complex F
inputFrequencyDot E incidence =
  C3.bilinearDot3
    (C3.modeVector E (Physical.p incidence))
    (C3.modeVector E (Physical.q incidence))

viscousWeightedOrderedValue :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
viscousWeightedOrderedValue {E = E} system incidence =
  C3.complex3Scale
    (inputFrequencyDot E incidence)
    (AP.rawOrderedValue system incidence)

rankOneTensorDivergenceValue :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
rankOneTensorDivergenceValue {E = E} system incidence =
  let
    uP = Audit.velocity system (Physical.p incidence)
    uQ = Audit.velocity system (Physical.q incidence)
    k = Physical.k incidence
    pDotQ = inputFrequencyDot E incidence
    outputDerivative = C3.bilinearDot3 uP (C3.modeVector E k)
  in
  C3.complex3Scale outputDerivative
    (C3.complex3Scale pDotQ uQ)

complex3ScaleAssociative :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Complex F)
    (value : C3.Complex3 F) →
  C3.complex3Scale left (C3.complex3Scale right value)
  ≡ C3.complex3Scale (C3.complexMultiply left right) value
complex3ScaleAssociative left right (C3.complex3 x y z)
  rewrite Scaling.complexMultiplyAssociative left right x
        | Scaling.complexMultiplyAssociative left right y
        | Scaling.complexMultiplyAssociative left right z = refl

complex3ScaleScalarCommute :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Complex F)
    (value : C3.Complex3 F) →
  C3.complex3Scale left (C3.complex3Scale right value)
  ≡ C3.complex3Scale right (C3.complex3Scale left value)
complex3ScaleScalarCommute left right value =
  trans
    (complex3ScaleAssociative left right value)
    (trans
      (cong (λ scalar → C3.complex3Scale scalar value)
        (Algebra.complexMultiplyCommutative left right))
      (sym (complex3ScaleAssociative right left value)))

viscousWeightedOrderedValueIsTensorDivergence :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  Helical.Transverse E
    (Physical.p incidence)
    (Audit.velocity system (Physical.p incidence)) →
  viscousWeightedOrderedValue system incidence
  ≡ rankOneTensorDivergenceValue system incidence
viscousWeightedOrderedValueIsTensorDivergence {E = E}
    system incidence transverse =
  let
    p = Physical.p incidence
    q = Physical.q incidence
    k = Physical.k incidence
    uP = Audit.velocity system p
    uQ = Audit.velocity system q
    pDotQ = inputFrequencyDot E incidence
    qDerivative = C3.bilinearDot3 uP (C3.modeVector E q)
    kDerivative = C3.bilinearDot3 uP (C3.modeVector E k)

    derivativeRelocation : qDerivative ≡ kDerivative
    derivativeRelocation =
      Relocation.complex3OutputDerivativeRelocation E
        (record { closes = Physical.resonance incidence })
        transverse
  in
  trans
    (cong (C3.complex3Scale pDotQ)
      (cong (λ derivative → C3.complex3Scale derivative uQ)
        derivativeRelocation))
    (complex3ScaleScalarCommute pDotQ kDerivative uQ)

round89ViscousHHGeometryMovedInsideTensorExactly : Bool
round89ViscousHHGeometryMovedInsideTensorExactly = true

round89WeightedHHTensorDivergenceIdentityClosed : Bool
round89WeightedHHTensorDivergenceIdentityClosed = true

round89DerivativeWeightedTensorRealizedInClosedHHCarrier : Bool
round89DerivativeWeightedTensorRealizedInClosedHHCarrier = false

round89DissipationMassesWeldedToDerivativeTensorInputs : Bool
round89DissipationMassesWeldedToDerivativeTensorInputs = false

round89ViscousHHGeometryMovedInsideTensorExactlyIsTrue :
  round89ViscousHHGeometryMovedInsideTensorExactly ≡ true
round89ViscousHHGeometryMovedInsideTensorExactlyIsTrue = refl

round89WeightedHHTensorDivergenceIdentityClosedIsTrue :
  round89WeightedHHTensorDivergenceIdentityClosed ≡ true
round89WeightedHHTensorDivergenceIdentityClosedIsTrue = refl
