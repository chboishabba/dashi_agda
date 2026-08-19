module DASHI.Physics.Closure.NSTriadKNLiteralThreeLegWaleffeCommonAmplitudeRound93Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND93 / LITERAL THREE-LEG COMMON AMPLITUDE
--
-- Combine the exact ordered-pair Waleffe factor, Fourier reality, negative-mode
-- curl-eigenvalue transport, and the scalar-triple orbit.  For one literal
-- physical triad p+q=k with real signed curl eigenvalues lambda_p, lambda_q,
-- lambda_k, define
--
--   A = Re <u_k , u_p x u_q>.
--
-- Then the SAME literal ordered-pair transfer on the three energy legs obeys
--
--   T_k = (lambda_q-lambda_p) A,
--   T_p = (lambda_k-lambda_q) A,
--   T_q = (lambda_p-lambda_k) A.
--
-- This closes the same-object common-amplitude seam left open in Round92.  The
-- theorem is local Fourier algebra only; no statistical cascade direction or
-- global coercivity conclusion is imported from Waleffe.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNConvectiveRotationalTriadIdentityRound93Exact as Conv
import DASHI.Physics.Closure.NSTriadKNLiteralOrderedPairWaleffeFactorRound93Exact as Local
import DASHI.Physics.Closure.NSTriadKNComplex3ScalarTripleOrbitRound93Exact as Triple
import DASHI.Physics.Closure.NSTriadKNCurlRealityHelicalTransportRound93Exact as CurlReality

realSubtract :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F
realSubtract {F = F} a b = C3.add F a (C3.negate F b)

realEmbedSubtract :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Carrier F) →
  C3.complexSubtract (C3.realEmbed F a) (C3.realEmbed F b)
  ≡ C3.realEmbed F (realSubtract a b)
realEmbedSubtract {F = F} a b
  rewrite C3.negateZero F
        | C3.addZeroLeft F (C3.zero F) = refl

realPartRealScale :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Carrier F)
    (z : C3.Complex F) →
  C3.complexRealPart
    (C3.complexMultiply (C3.realEmbed F a) z)
  ≡ C3.realEmbed F (C3.multiply F a (C3.real z))
realPartRealScale {F = F} a (C3.complex zr zi)
  rewrite Algebra.realMultiplyZeroLeft F zi
        | C3.negateZero F
        | Algebra.realAddZeroRight F (C3.multiply F a zr) = refl

realOfConjugate :
  ∀ {r} {F : C3.RealField r} (z : C3.Complex F) →
  C3.real (C3.complexConjugate z) ≡ C3.real z
realOfConjugate (C3.complex zr zi) = refl

realOfNegativeConjugate :
  ∀ {r} {F : C3.RealField r} (z : C3.Complex F) →
  C3.real (C3.complexNegate (C3.complexConjugate z))
  ≡ C3.negate F (C3.real z)
realOfNegativeConjugate (C3.complex zr zi) = refl

reverseDifferenceTimes :
  ∀ {r} (F : C3.RealField r)
    (a b x : C3.Carrier F) →
  C3.multiply F (realSubtract {F = F} a b) (C3.negate F x)
  ≡ C3.multiply F (realSubtract {F = F} b a) x
reverseDifferenceTimes F a b x =
  P.R.solve 3
    (λ a b x → (a P.R.⊕ (P.R.⊝ b)) P.R.⊗ (P.R.⊝ x)
      P.R.⊜ (b P.R.⊕ (P.R.⊝ a)) P.R.⊗ x)
    refl a b x
  where module P = Algebra.Polynomial F

record LiteralThreeLegHelicalOrbit
    {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence) : Set r where
  constructor literal-three-leg-helical-orbit
  field
    velocity : Z3.FourierMode → C3.Complex3 F
    reality : Audit.RealityCondition velocity
    divergenceFree : Audit.DivergenceFreeCondition E velocity

    lambdaP lambdaQ lambdaK : C3.Carrier F

    curlEigenP :
      Conv.curlFromWave
        (C3.modeVector E (Physical.p tau))
        (velocity (Physical.p tau))
      ≡ C3.complex3Scale
          (C3.realEmbed F lambdaP)
          (velocity (Physical.p tau))

    curlEigenQ :
      Conv.curlFromWave
        (C3.modeVector E (Physical.q tau))
        (velocity (Physical.q tau))
      ≡ C3.complex3Scale
          (C3.realEmbed F lambdaQ)
          (velocity (Physical.q tau))

    curlEigenK :
      Conv.curlFromWave
        (C3.modeVector E (Physical.k tau))
        (velocity (Physical.k tau))
      ≡ C3.complex3Scale
          (C3.realEmbed F lambdaK)
          (velocity (Physical.k tau))

open LiteralThreeLegHelicalOrbit public

baseLocalData :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {tau : Physical.PhysicalTriadIncidence} →
  LiteralThreeLegHelicalOrbit E I tau →
  Local.LiteralHelicalOrderedPairData E I tau
baseLocalData O = record
  { Local.velocity = velocity O
  ; Local.divergenceFree = divergenceFree O
  ; Local.signedEigenP = C3.realEmbed _ (lambdaP O)
  ; Local.signedEigenQ = C3.realEmbed _ (lambdaQ O)
  ; Local.curlEigenP = curlEigenP O
  ; Local.curlEigenQ = curlEigenQ O
  }

pEnergyLocalData :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {tau : Physical.PhysicalTriadIncidence} →
  (O : LiteralThreeLegHelicalOrbit E I tau) →
  Local.LiteralHelicalOrderedPairData E I (Orbit.pEnergyLeg tau)
pEnergyLocalData {F = F} {E = E} {tau = tau} O = record
  { Local.velocity = velocity O
  ; Local.divergenceFree = divergenceFree O
  ; Local.signedEigenP = C3.realEmbed F (lambdaK O)
  ; Local.signedEigenQ = C3.realEmbed F (lambdaQ O)
  ; Local.curlEigenP = curlEigenK O
  ; Local.curlEigenQ =
      CurlReality.negativeModePreservesRealHelicalEigenvalue
        E (velocity O) (reality O) (Physical.q tau) (lambdaQ O)
        (curlEigenQ O)
  }

qEnergyLocalData :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {tau : Physical.PhysicalTriadIncidence} →
  (O : LiteralThreeLegHelicalOrbit E I tau) →
  Local.LiteralHelicalOrderedPairData E I (Orbit.qEnergyLeg tau)
qEnergyLocalData {F = F} {E = E} {tau = tau} O = record
  { Local.velocity = velocity O
  ; Local.divergenceFree = divergenceFree O
  ; Local.signedEigenP = C3.realEmbed F (lambdaK O)
  ; Local.signedEigenQ = C3.realEmbed F (lambdaP O)
  ; Local.curlEigenP = curlEigenK O
  ; Local.curlEigenQ =
      CurlReality.negativeModePreservesRealHelicalEigenvalue
        E (velocity O) (reality O) (Physical.p tau) (lambdaP O)
        (curlEigenP O)
  }

commonAmplitude :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {tau : Physical.PhysicalTriadIncidence} →
  LiteralThreeLegHelicalOrbit E I tau → C3.Carrier F
commonAmplitude {tau = tau} O =
  C3.real
    (Triple.baseGeometricAmplitude
      (velocity O (Physical.p tau))
      (velocity O (Physical.q tau))
      (velocity O (Physical.k tau)))

baseTransferCommonAmplitude :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (O : LiteralThreeLegHelicalOrbit E I tau) →
  Audit.orderedPairSignedTransferAt E I tau (velocity O)
  ≡ C3.realEmbed F
      (C3.multiply F
        (realSubtract (lambdaQ O) (lambdaP O))
        (commonAmplitude O))
baseTransferCommonAmplitude {F = F} E I tau O =
  trans
    (Local.literalOrderedPairWaleffeFactor E I tau (baseLocalData O))
    (trans
      (cong
        (λ coefficient →
          C3.complexRealPart
            (C3.complexMultiply coefficient
              (Triple.baseGeometricAmplitude
                (velocity O (Physical.p tau))
                (velocity O (Physical.q tau))
                (velocity O (Physical.k tau)))))
        (realEmbedSubtract (lambdaQ O) (lambdaP O)))
      (realPartRealScale
        (realSubtract (lambdaQ O) (lambdaP O))
        (Triple.baseGeometricAmplitude
          (velocity O (Physical.p tau))
          (velocity O (Physical.q tau))
          (velocity O (Physical.k tau)))))

pEnergyActualAmplitude :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {tau : Physical.PhysicalTriadIncidence}
    (O : LiteralThreeLegHelicalOrbit E I tau) →
  C3.hermitianPairing3
    (velocity O (Physical.p tau))
    (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
      (velocity O (Physical.k tau))
      (velocity O (Z3.negateMode (Physical.q tau))))
  ≡
  Triple.pEnergyGeometricAmplitude
    (velocity O (Physical.p tau))
    (velocity O (Physical.q tau))
    (velocity O (Physical.k tau))
pEnergyActualAmplitude {tau = tau} O =
  cong
    (λ selected →
      C3.hermitianPairing3
        (velocity O (Physical.p tau))
        (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
          (velocity O (Physical.k tau)) selected))
    (reality O (Physical.q tau))

qEnergyActualAmplitude :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {tau : Physical.PhysicalTriadIncidence}
    (O : LiteralThreeLegHelicalOrbit E I tau) →
  C3.hermitianPairing3
    (velocity O (Physical.q tau))
    (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
      (velocity O (Physical.k tau))
      (velocity O (Z3.negateMode (Physical.p tau))))
  ≡
  Triple.qEnergyGeometricAmplitude
    (velocity O (Physical.p tau))
    (velocity O (Physical.q tau))
    (velocity O (Physical.k tau))
qEnergyActualAmplitude {tau = tau} O =
  cong
    (λ selected →
      C3.hermitianPairing3
        (velocity O (Physical.q tau))
        (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
          (velocity O (Physical.k tau)) selected))
    (reality O (Physical.p tau))

pEnergyTransferCommonAmplitude :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (O : LiteralThreeLegHelicalOrbit E I tau) →
  Audit.orderedPairSignedTransferAt E I (Orbit.pEnergyLeg tau) (velocity O)
  ≡ C3.realEmbed F
      (C3.multiply F
        (realSubtract (lambdaK O) (lambdaQ O))
        (commonAmplitude O))
pEnergyTransferCommonAmplitude {F = F} E I tau O =
  let
    baseA = Triple.baseGeometricAmplitude
      (velocity O (Physical.p tau))
      (velocity O (Physical.q tau))
      (velocity O (Physical.k tau))
    pA = Triple.pEnergyGeometricAmplitude
      (velocity O (Physical.p tau))
      (velocity O (Physical.q tau))
      (velocity O (Physical.k tau))
    dQK = realSubtract (lambdaQ O) (lambdaK O)
  in
  trans
    (Local.literalOrderedPairWaleffeFactor
      E I (Orbit.pEnergyLeg tau) (pEnergyLocalData O))
    (trans
      (cong
        (λ coefficient →
          C3.complexRealPart
            (C3.complexMultiply coefficient
              (C3.hermitianPairing3
                (velocity O (Physical.p tau))
                (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
                  (velocity O (Physical.k tau))
                  (velocity O (Z3.negateMode (Physical.q tau)))))))
        (realEmbedSubtract (lambdaQ O) (lambdaK O)))
      (trans
        (cong
          (λ amplitude →
            C3.complexRealPart
              (C3.complexMultiply (C3.realEmbed F dQK) amplitude))
          (trans
            (pEnergyActualAmplitude O)
            (Triple.pEnergyAmplitudeIsNegativeConjugateBase
              (velocity O (Physical.p tau))
              (velocity O (Physical.q tau))
              (velocity O (Physical.k tau)))))
        (trans
          (realPartRealScale dQK
            (C3.complexNegate (C3.complexConjugate baseA)))
          (cong (C3.realEmbed F)
            (trans
              (cong (C3.multiply F dQK)
                (realOfNegativeConjugate baseA))
              (reverseDifferenceTimes F
                (lambdaQ O) (lambdaK O) (commonAmplitude O)))))))

qEnergyTransferCommonAmplitude :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (O : LiteralThreeLegHelicalOrbit E I tau) →
  Audit.orderedPairSignedTransferAt E I (Orbit.qEnergyLeg tau) (velocity O)
  ≡ C3.realEmbed F
      (C3.multiply F
        (realSubtract (lambdaP O) (lambdaK O))
        (commonAmplitude O))
qEnergyTransferCommonAmplitude {F = F} E I tau O =
  let
    baseA = Triple.baseGeometricAmplitude
      (velocity O (Physical.p tau))
      (velocity O (Physical.q tau))
      (velocity O (Physical.k tau))
    qA = Triple.qEnergyGeometricAmplitude
      (velocity O (Physical.p tau))
      (velocity O (Physical.q tau))
      (velocity O (Physical.k tau))
    dPK = realSubtract (lambdaP O) (lambdaK O)
  in
  trans
    (Local.literalOrderedPairWaleffeFactor
      E I (Orbit.qEnergyLeg tau) (qEnergyLocalData O))
    (trans
      (cong
        (λ coefficient →
          C3.complexRealPart
            (C3.complexMultiply coefficient
              (C3.hermitianPairing3
                (velocity O (Physical.q tau))
                (DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact.complex3Cross
                  (velocity O (Physical.k tau))
                  (velocity O (Z3.negateMode (Physical.p tau)))))))
        (realEmbedSubtract (lambdaP O) (lambdaK O)))
      (trans
        (cong
          (λ amplitude →
            C3.complexRealPart
              (C3.complexMultiply (C3.realEmbed F dPK) amplitude))
          (trans
            (qEnergyActualAmplitude O)
            (Triple.qEnergyAmplitudeIsConjugateBase
              (velocity O (Physical.p tau))
              (velocity O (Physical.q tau))
              (velocity O (Physical.k tau)))))
        (trans
          (realPartRealScale dPK (C3.complexConjugate baseA))
          (cong (C3.realEmbed F)
            (cong (C3.multiply F dPK) (realOfConjugate baseA))))))

round93LiteralThreeLegWaleffeCommonAmplitudeClosed : Bool
round93LiteralThreeLegWaleffeCommonAmplitudeClosed = true

round93LiteralThreeLegWaleffeCommonAmplitudeClosedIsTrue :
  round93LiteralThreeLegWaleffeCommonAmplitudeClosed ≡ true
round93LiteralThreeLegWaleffeCommonAmplitudeClosedIsTrue = refl
