module DASHI.Physics.Closure.NSTriadKNOrderedInteractionSourceFactorizationRound73Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- ROUND73 / SOURCE-NATIVE ORDERED-INTERACTION FACTORIZATION
--
-- On the exact finite Galerkin carrier the literal ordered term is
--
--   -i P_k [ (u_p dot q) u_q ].
--
-- Round73 now proves on the SAME PhysicalTriadIncidence that this equals
--
--   (-i (u_p dot q)) P_k u_q.
--
-- Thus the complex source-native roles are explicit before any scalar
-- majorization:
--
--   low/transport scalar = -i (u_p dot q),
--   high response        = P_k u_q.
--
-- Testing against an output vector then gives the exact complex product
--
--   <test_k, ordered term>
--     = (-i (u_p dot q)) <test_k, P_k u_q>.
--
-- IMPORTANT BOUNDARY: the repository's final signed coefficient applies
-- complex realPart to this product.  In general Re(z w) is NOT the product of
-- Re(z) and Re(w).  Therefore this theorem closes the literal complex
-- factorization seam but deliberately does not manufacture the rational
-- Round73 x_tau*y_tau factorization.  A phase/polarisation or real-alignment
-- theorem is still required to cross that boundary source-natively.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as LerayLinear

interactionScalar :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
interactionScalar system incidence =
  C3.bilinearDot3
    (Audit.velocityAt system (Physical.p incidence))
    (C3.modeVector
      (Audit.integerEmbedding system) (Physical.q incidence))

projectedHighResponse :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
projectedHighResponse system incidence =
  C3.lerayProject3
    (Audit.integerEmbedding system)
    (Audit.inverseSquare system)
    (Physical.k incidence)
    (Audit.velocityAt system (Physical.q incidence))

transportScalar :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → C3.Complex F
transportScalar system incidence =
  C3.complexMultiply
    (Signed.minusImaginary (Audit.galerkinLaws system))
    (interactionScalar system incidence)

orderedInteractionSourceFactorization :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  Audit.projectedOrderedTerm system incidence
  ≡ C3.complex3Scale
      (transportScalar system incidence)
      (projectedHighResponse system incidence)
orderedInteractionSourceFactorization system incidence =
  let
    minusI = Signed.minusImaginary (Audit.galerkinLaws system)
    scalar = interactionScalar system incidence
    output = Physical.k incidence
    response = Audit.velocityAt system (Physical.q incidence)
  in
  trans
    (cong
      (C3.complex3Scale minusI)
      (LerayLinear.lerayProjectComplexScale
        (Audit.integerEmbedding system)
        (Audit.inverseSquare system)
        output scalar response))
    (LerayLinear.complex3ScaleAssociative
      minusI scalar (projectedHighResponse system incidence))

testedComplexInteraction :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence →
  C3.Complex3 F → C3.Complex F
testedComplexInteraction system incidence testK =
  C3.hermitianPairing3 testK (Audit.projectedOrderedTerm system incidence)

testedHighResponse :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence →
  C3.Complex3 F → C3.Complex F
testedHighResponse system incidence testK =
  C3.hermitianPairing3 testK (projectedHighResponse system incidence)

testedComplexInteractionFactorization :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence)
    (testK : C3.Complex3 F) →
  testedComplexInteraction system incidence testK
  ≡ C3.complexMultiply
      (transportScalar system incidence)
      (testedHighResponse system incidence testK)
testedComplexInteractionFactorization system incidence testK =
  trans
    (cong (C3.hermitianPairing3 testK)
      (orderedInteractionSourceFactorization system incidence))
    (Scaling.hermitianPairingScaleRight
      (transportScalar system incidence)
      testK
      (projectedHighResponse system incidence))

signedCoefficientIsRealPartOfSourceProduct :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence)
    (testK : C3.Complex3 F) →
  Signed.testedSignedCoefficient
    (Audit.galerkinLaws system)
    (Physical.k incidence)
    (Physical.p incidence)
    (Physical.q incidence)
    (Audit.velocityAt system (Physical.p incidence))
    (Audit.velocityAt system (Physical.q incidence))
    testK
  ≡ C3.complexRealPart
      (C3.complexMultiply
        (transportScalar system incidence)
        (testedHighResponse system incidence testK))
signedCoefficientIsRealPartOfSourceProduct system incidence testK =
  cong C3.complexRealPart
    (testedComplexInteractionFactorization system incidence testK)

round73LiteralComplexOrderedFactorizationConstructed : Bool
round73LiteralComplexOrderedFactorizationConstructed = true

round73TestedComplexProductFactorizationConstructed : Bool
round73TestedComplexProductFactorizationConstructed = true

round73RationalLowHighProductDerivedWithoutPhaseTheorem : Bool
round73RationalLowHighProductDerivedWithoutPhaseTheorem = false

round73LiteralComplexOrderedFactorizationConstructedIsTrue :
  round73LiteralComplexOrderedFactorizationConstructed ≡ true
round73LiteralComplexOrderedFactorizationConstructedIsTrue = refl

round73RationalLowHighProductDerivedWithoutPhaseTheoremIsFalse :
  round73RationalLowHighProductDerivedWithoutPhaseTheorem ≡ false
round73RationalLowHighProductDerivedWithoutPhaseTheoremIsFalse = refl
