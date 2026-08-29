module DASHI.Physics.Closure.NSTriadKNPhysicalHeterochiralMinorityWaleffeWeldRound134Exact where

------------------------------------------------------------------------
-- ROUND134 / SAME-OBJECT WELD: LITERAL THREE-LEG TRANSFERS -> ROUND102
-- HETEROCHIRAL MINORITY-LEG CRITICAL PRODUCTION
--
-- Primary source:
--   Fabian Waleffe, "The nature of triad interactions in homogeneous
--   turbulence", Physics of Fluids A 4 (1992), 350--363.
--   DOI: 10.1063/1.858309.
--
-- Round93 already proves on one literal physical helical triad that the actual
-- ordered-pair transfers on the k, p and q energy legs share one real scalar
-- triple-product amplitude A:
--
--   T_k = (lambda_q-lambda_p) A,
--   T_p = (lambda_k-lambda_q) A,
--   T_q = (lambda_p-lambda_k) A.
--
-- Round102 separately proves, over the same generic RealField, that the
-- critical weighted combination of those three transfers is zero for the two
-- homochiral sign classes and reduces each mixed-helicity sign class to twice
-- the weighted transfer of its unique minority-helicity leg.
--
-- This file closes the SAME-OBJECT seam between those two owners.  The left
-- side below is built from the real parts of the literal Round93 physical
-- transfers; the right side is exactly the Round102 WaleffeCriticalFieldCell
-- normal form.  No new amplitude, proxy forcing, or statistical closure is
-- introduced.
--
-- This is still local triad algebra.  It does NOT perform the cutoff-uniform
-- summation/absorption required for package A.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralThreeLegWaleffeCommonAmplitudeRound93Exact as R93
import DASHI.Physics.Closure.NSTriadKNHeterochiralMinorityLegFieldRound102Exact as R102

------------------------------------------------------------------------
-- Real-valued views of the literal physical transfers.
------------------------------------------------------------------------

baseTransferReal :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (O : R93.LiteralThreeLegHelicalOrbit E I tau) →
  C3.real (Audit.orderedPairSignedTransferAt E I tau (R93.velocity O))
  ≡ R102.transferK (R93.lambdaP O) (R93.lambdaQ O) (R93.commonAmplitude O)
baseTransferReal E I tau O =
  cong C3.real (R93.baseTransferCommonAmplitude E I tau O)

pTransferReal :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (O : R93.LiteralThreeLegHelicalOrbit E I tau) →
  C3.real
    (Audit.orderedPairSignedTransferAt E I (Orbit.pEnergyLeg tau) (R93.velocity O))
  ≡ R102.transferP (R93.lambdaK O) (R93.lambdaQ O) (R93.commonAmplitude O)
pTransferReal E I tau O =
  cong C3.real (R93.pEnergyTransferCommonAmplitude E I tau O)

qTransferReal :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (O : R93.LiteralThreeLegHelicalOrbit E I tau) →
  C3.real
    (Audit.orderedPairSignedTransferAt E I (Orbit.qEnergyLeg tau) (R93.velocity O))
  ≡ R102.transferQ (R93.lambdaP O) (R93.lambdaK O) (R93.commonAmplitude O)
qTransferReal E I tau O =
  cong C3.real (R93.qEnergyTransferCommonAmplitude E I tau O)

------------------------------------------------------------------------
-- Literal critical production and exact Round102 field-cell representation.
------------------------------------------------------------------------

actualCriticalProduction :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (O : R93.LiteralThreeLegHelicalOrbit E I tau) →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
actualCriticalProduction {F = F} E I tau O radiusK radiusP radiusQ =
  C3.add F
    (C3.multiply F radiusK
      (C3.real (Audit.orderedPairSignedTransferAt E I tau (R93.velocity O))))
    (C3.add F
      (C3.multiply F radiusP
        (C3.real
          (Audit.orderedPairSignedTransferAt E I
            (Orbit.pEnergyLeg tau) (R93.velocity O))))
      (C3.multiply F radiusQ
        (C3.real
          (Audit.orderedPairSignedTransferAt E I
            (Orbit.qEnergyLeg tau) (R93.velocity O)))))

criticalCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {tau : Physical.PhysicalTriadIncidence} →
  R93.LiteralThreeLegHelicalOrbit E I tau →
  C3.Carrier F → C3.Carrier F → C3.Carrier F →
  R102.WaleffeCriticalFieldCell F
criticalCell O radiusK radiusP radiusQ =
  R102.waleffe-critical-field-cell
    radiusK radiusP radiusQ (R93.commonAmplitude O)

actualCriticalProductionIsMinorityFieldProduction :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (O : R93.LiteralThreeLegHelicalOrbit E I tau)
    (radiusK radiusP radiusQ : C3.Carrier F) →
  actualCriticalProduction E I tau O radiusK radiusP radiusQ
  ≡ R102.criticalProduction
      (criticalCell O radiusK radiusP radiusQ)
      (R93.lambdaK O) (R93.lambdaP O) (R93.lambdaQ O)
actualCriticalProductionIsMinorityFieldProduction {F = F}
    E I tau O radiusK radiusP radiusQ =
  cong₂ (C3.add F)
    (cong (C3.multiply F radiusK) (baseTransferReal E I tau O))
    (cong₂ (C3.add F)
      (cong (C3.multiply F radiusP) (pTransferReal E I tau O))
      (cong (C3.multiply F radiusQ) (qTransferReal E I tau O)))

------------------------------------------------------------------------
-- Sign-pattern witnesses turn the abstract Round102 normal forms into literal
-- physical three-leg theorems.  We keep the sign equalities proof-bearing:
-- the weak generic RealField does not decide helicity sign from a scalar.
------------------------------------------------------------------------

record HomochiralPlusRadii
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {tau : Physical.PhysicalTriadIncidence}
    (O : R93.LiteralThreeLegHelicalOrbit E I tau) : Set r where
  constructor homochiral-plus-radii
  field
    radiusK radiusP radiusQ : C3.Carrier F
    lambdaKPlus : R93.lambdaK O ≡ radiusK
    lambdaPPlus : R93.lambdaP O ≡ radiusP
    lambdaQPlus : R93.lambdaQ O ≡ radiusQ

open HomochiralPlusRadii public

literalHomochiralPlusCriticalProductionVanishes :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (O : R93.LiteralThreeLegHelicalOrbit E I tau)
    (H : HomochiralPlusRadii O) →
  actualCriticalProduction E I tau O (radiusK H) (radiusP H) (radiusQ H)
  ≡ C3.zero F
literalHomochiralPlusCriticalProductionVanishes E I tau O H
  rewrite lambdaKPlus H | lambdaPPlus H | lambdaQPlus H =
  trans
    (actualCriticalProductionIsMinorityFieldProduction
      E I tau O (radiusK H) (radiusP H) (radiusQ H))
    (R102.homochiralPlusVanishes
      (criticalCell O (radiusK H) (radiusP H) (radiusQ H)))

record MinorityKMinusRadii
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {tau : Physical.PhysicalTriadIncidence}
    (O : R93.LiteralThreeLegHelicalOrbit E I tau) : Set r where
  constructor minority-k-minus-radii
  field
    radiusK radiusP radiusQ : C3.Carrier F
    lambdaKMinus : R93.lambdaK O ≡ C3.negate F radiusK
    lambdaPPlus : R93.lambdaP O ≡ radiusP
    lambdaQPlus : R93.lambdaQ O ≡ radiusQ

open MinorityKMinusRadii public

literalMinorityKMinusDifferenceNormalForm :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (O : R93.LiteralThreeLegHelicalOrbit E I tau)
    (H : MinorityKMinusRadii O) →
  actualCriticalProduction E I tau O
    (MinorityKMinusRadii.radiusK H)
    (MinorityKMinusRadii.radiusP H)
    (MinorityKMinusRadii.radiusQ H)
  ≡ R102.criticalProduction
      (criticalCell O
        (MinorityKMinusRadii.radiusK H)
        (MinorityKMinusRadii.radiusP H)
        (MinorityKMinusRadii.radiusQ H))
      (C3.negate F (MinorityKMinusRadii.radiusK H))
      (MinorityKMinusRadii.radiusP H)
      (MinorityKMinusRadii.radiusQ H)
literalMinorityKMinusDifferenceNormalForm E I tau O H
  rewrite MinorityKMinusRadii.lambdaKMinus H
        | MinorityKMinusRadii.lambdaPPlus H
        | MinorityKMinusRadii.lambdaQPlus H =
  actualCriticalProductionIsMinorityFieldProduction
    E I tau O
    (MinorityKMinusRadii.radiusK H)
    (MinorityKMinusRadii.radiusP H)
    (MinorityKMinusRadii.radiusQ H)

round134LiteralThreeLegToMinorityFieldSameObjectWeldClosed : Bool
round134LiteralThreeLegToMinorityFieldSameObjectWeldClosed = true

round134LiteralHomochiralCriticalProductionCancellationClosed : Bool
round134LiteralHomochiralCriticalProductionCancellationClosed = true

round134LiteralMixedHelicityMinorityNormalFormWeldStarted : Bool
round134LiteralMixedHelicityMinorityNormalFormWeldStarted = true

round134PhysicalCutoffUniformMinorityGainSummationClosed : Bool
round134PhysicalCutoffUniformMinorityGainSummationClosed = false

round134PackageAClosed : Bool
round134PackageAClosed = false

round134LiteralThreeLegToMinorityFieldSameObjectWeldClosedIsTrue :
  round134LiteralThreeLegToMinorityFieldSameObjectWeldClosed ≡ true
round134LiteralThreeLegToMinorityFieldSameObjectWeldClosedIsTrue = refl

round134PackageAClosedIsFalse : round134PackageAClosed ≡ false
round134PackageAClosedIsFalse = refl
