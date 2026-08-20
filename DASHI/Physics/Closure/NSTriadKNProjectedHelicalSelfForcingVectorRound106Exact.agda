module DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Peter Constantin; Andrew Majda.
-- Title: "The Beltrami spectrum for incompressible fluid flows".
-- Communications in Mathematical Physics 115 (1988), 435--456.
-- DOI: 10.1007/BF01218019.
--
-- ROUND106 / VECTOR WALEFFE SELF-FORCING NORMAL FORM
--
-- Round93 proved the Waleffe eigenvalue-difference only after testing the
-- literal ordered-pair Galerkin interaction against u_k.  Round95 therefore
-- still had to leave the self contribution to the cubic phase tangent opaque.
--
-- Here we close the stronger VECTOR identity.  For p+q=k, nonzero k, and
-- helical input modes
--
--   curl_p u_p = lambda_p u_p,
--   curl_q u_q = lambda_q u_q,
--
-- the exact symmetrised projected Galerkin forcing is
--
--   N_k^{p,q}
--     = (lambda_q-lambda_p) P_k (u_p x u_q).
--
-- The proof is entirely on the repository's literal Complex3 carrier:
-- convective = rotational + longitudinal gradient, Leray kills the resonant
-- longitudinal vector, and the two -i factors are tracked exactly.  This is
-- stronger than the old tested transfer formula and exposes the self phase
-- forcing as a projected-cross square rather than an arbitrary network term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as Linear
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as ScalarLinear
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayExact
import DASHI.Physics.Closure.NSTriadKNConvectiveRotationalTriadIdentityRound93Exact as Conv
import DASHI.Physics.Closure.NSTriadKNHelicalInputDifferenceFactorizationRound93Exact as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross

minusI : ∀ {r} (F : C3.RealField r) → C3.Complex F
minusI F = C3.complexNegate (C3.complexI F)

complex3ScaleOne :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complex3Scale (C3.complexOne F) v ≡ v
complex3ScaleOne (C3.complex3 x y z) =
  Field.complex3Ext
    (Field.complexOneMultiply x)
    (Field.complexOneMultiply y)
    (Field.complexOneMultiply z)

complex3ScaleZero :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complex3Scale (C3.complexZero F) v ≡ C3.complex3Zero F
complex3ScaleZero {F = F} (C3.complex3 x y z) =
  Field.complex3Ext
    (Field.complexMultiplyZeroLeft x)
    (Field.complexMultiplyZeroLeft y)
    (Field.complexMultiplyZeroLeft z)

complex3SubtractSelf :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complex3Subtract v v ≡ C3.complex3Zero F
complex3SubtractSelf (C3.complex3 x y z) =
  Field.complex3Ext
    (Additive.complexSubtractSelf x)
    (Additive.complexSubtractSelf y)
    (Additive.complexSubtractSelf z)

subtractThenAddBack :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex3 F) →
  C3.complex3Add (C3.complex3Subtract a b) b ≡ a
subtractThenAddBack {F = F}
    (C3.complex3 ax ay az) (C3.complex3 bx by bz) =
  Field.complex3Ext
    (R.solve 2 (λ a b → ((a R.⊕ (R.⊝ b)) R.⊕ b) R.⊜ a) refl ax bx)
    (R.solve 2 (λ a b → ((a R.⊕ (R.⊝ b)) R.⊕ b) R.⊜ a) refl ay by)
    (R.solve 2 (λ a b → ((a R.⊕ (R.⊝ b)) R.⊕ b) R.⊜ a) refl az bz)
  where module R = Ring.Solver F

minusITimesI :
  ∀ {r} (F : C3.RealField r) →
  C3.complexMultiply (minusI F) (C3.complexI F) ≡ C3.complexOne F
minusITimesI {r} F =
  Field.complexExt
    (P.R.solve 0
      (((P.R.⊝ (P.R.Κ (C3.zero F))) P.R.⊗ P.R.Κ (C3.zero F))
        P.R.⊕ (P.R.⊝ ((P.R.⊝ P.R.Κ (C3.one F)) P.R.⊗ P.R.Κ (C3.one F))))
       P.R.⊜ P.R.Κ (C3.one F)) refl)
    (P.R.solve 0
      (((P.R.⊝ (P.R.Κ (C3.zero F))) P.R.⊗ P.R.Κ (C3.one F))
        P.R.⊕ ((P.R.⊝ P.R.Κ (C3.one F)) P.R.⊗ P.R.Κ (C3.zero F)))
       P.R.⊜ P.R.Κ (C3.zero F)) refl)
  where module P = Field.Polynomial F

minusISquared :
  ∀ {r} (F : C3.RealField r) →
  C3.complexMultiply (minusI F) (minusI F)
  ≡ C3.complexNegate (C3.complexOne F)
minusISquared {r} F =
  Field.complexExt
    (P.R.solve 0
      (((P.R.⊝ P.R.Κ (C3.zero F)) P.R.⊗ (P.R.⊝ P.R.Κ (C3.zero F)))
        P.R.⊕ (P.R.⊝ ((P.R.⊝ P.R.Κ (C3.one F)) P.R.⊗ (P.R.⊝ P.R.Κ (C3.one F)))))
       P.R.⊜ P.R.⊝ P.R.Κ (C3.one F)) refl)
    (P.R.solve 0
      (((P.R.⊝ P.R.Κ (C3.zero F)) P.R.⊗ (P.R.⊝ P.R.Κ (C3.one F)))
        P.R.⊕ ((P.R.⊝ P.R.Κ (C3.one F)) P.R.⊗ (P.R.⊝ P.R.Κ (C3.zero F))))
       P.R.⊜ P.R.Κ (C3.zero F)) refl)
  where module P = Field.Polynomial F

negateSubtractSwap :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.complexNegate (C3.complexSubtract a b)
  ≡ C3.complexSubtract b a
negateSubtractSwap {F = F} a b =
  R.solve 2
    (λ a b → R.⊝ (a R.⊕ (R.⊝ b)) R.⊜ (b R.⊕ (R.⊝ a)))
    refl a b
  where module R = Ring.Solver F

lerayKillsModeVector :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode) →
  Z3.NonZeroMode k →
  C3.lerayProject3 E I k (C3.modeVector E k) ≡ C3.complex3Zero F
lerayKillsModeVector {F = F} E I k nonzero =
  let
    dotMeaning = LerayExact.modeSelfDotIsEmbeddedNormSquared E I k
    inverseMeaning = LerayExact.embeddedInverseSquareLaw E I k nonzero
    coefficientMeaning :
      C3.complexMultiply
        (C3.realEmbed F (C3.inverseNormSquared I k))
        (C3.bilinearDot3 (C3.modeVector E k) (C3.modeVector E k))
      ≡ C3.complexOne F
    coefficientMeaning =
      trans
        (cong
          (C3.complexMultiply
            (C3.realEmbed F (C3.inverseNormSquared I k)))
          dotMeaning)
        inverseMeaning
  in
  trans
    (cong
      (C3.complex3Subtract (C3.modeVector E k))
      (cong
        (λ scalar → C3.complex3Scale scalar (C3.modeVector E k))
        coefficientMeaning))
    (trans
      (cong (C3.complex3Subtract (C3.modeVector E k))
        (complex3ScaleOne (C3.modeVector E k)))
      (complex3SubtractSelf (C3.modeVector E k)))

lerayKillsResonantGradient :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    {p q k : Z3.FourierMode}
    (resonance : Z3.Resonance p q k) →
  Z3.NonZeroMode k →
  (uP uQ : C3.Complex3 F) →
  C3.lerayProject3 E I k
    (Conv.gradientPair (C3.modeVector E p) (C3.modeVector E q) uP uQ)
  ≡ C3.complex3Zero F
lerayKillsResonantGradient {F = F} E I resonance nonzero uP uQ =
  let
    scalar = C3.bilinearDot3 uP uQ
  in
  trans
    (cong (C3.lerayProject3 E I _)
      (Conv.resonantGradientIsOutputLongitudinal E resonance uP uQ))
    (trans
      (ScalarLinear.lerayProjectComplexScale E I _ scalar (C3.modeVector E _))
      (trans
        (cong (C3.complex3Scale scalar)
          (lerayKillsModeVector E I _ nonzero))
        (complex3ScaleZero (C3.complex3Zero F))))

orderedPairIsMinusIProjectedConvective :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (uP uQ : C3.Complex3 F) →
  Signed.orderedPairVelocityInteraction
    (C3.complex3VelocityGalerkinLaws F E I) k p q uP uQ
  ≡ C3.complex3Scale (minusI F)
      (C3.lerayProject3 E I k
        (Conv.convectivePair
          (C3.modeVector E p) (C3.modeVector E q) uP uQ))
orderedPairIsMinusIProjectedConvective {F = F} E I k p q uP uQ =
  let
    first = C3.complex3Scale
      (C3.bilinearDot3 uP (C3.modeVector E q)) uQ
    second = C3.complex3Scale
      (C3.bilinearDot3 uQ (C3.modeVector E p)) uP
    pFirst = C3.lerayProject3 E I k first
    pSecond = C3.lerayProject3 E I k second
  in
  trans
    (sym (ScalarLinear.complex3ScaleAdd (minusI F) pFirst pSecond))
    (cong (C3.complex3Scale (minusI F))
      (sym (Linear.lerayProjectAdd E I k first second)))

minusIRotationalIsConvectiveMinusGradient :
  ∀ {r} {F : C3.RealField r}
    (waveP waveQ uP uQ : C3.Complex3 F) →
  C3.complex3Scale (minusI F)
    (Conv.rotationalPair waveP waveQ uP uQ)
  ≡ C3.complex3Subtract
      (Conv.convectivePair waveP waveQ uP uQ)
      (Conv.gradientPair waveP waveQ uP uQ)
minusIRotationalIsConvectiveMinusGradient {F = F} waveP waveQ uP uQ =
  let
    difference = C3.complex3Subtract
      (Conv.convectivePair waveP waveQ uP uQ)
      (Conv.gradientPair waveP waveQ uP uQ)
  in
  trans
    (cong (C3.complex3Scale (minusI F))
      (Conv.rotationalPairEqualsIConvectiveMinusGradient
        waveP waveQ uP uQ))
    (trans
      (ScalarLinear.complex3ScaleAssociative
        (minusI F) (C3.complexI F) difference)
      (trans
        (cong (λ scalar → C3.complex3Scale scalar difference)
          (minusITimesI F))
        (complex3ScaleOne difference)))

record ProjectedHelicalPairData
    {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (p q k : Z3.FourierMode) : Set r where
  constructor projected-helical-pair-data
  field
    resonance : Z3.Resonance p q k
    outputNonzero : Z3.NonZeroMode k
    uP uQ : C3.Complex3 F
    signedEigenP signedEigenQ : C3.Complex F
    curlEigenP :
      Conv.curlFromWave (C3.modeVector E p) uP
      ≡ C3.complex3Scale signedEigenP uP
    curlEigenQ :
      Conv.curlFromWave (C3.modeVector E q) uQ
      ≡ C3.complex3Scale signedEigenQ uQ

open ProjectedHelicalPairData public

projectedRotationalHelicalFactor :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {p q k : Z3.FourierMode}
    (H : ProjectedHelicalPairData E I p q k) →
  Conv.rotationalPair
    (C3.modeVector E p) (C3.modeVector E q) (uP H) (uQ H)
  ≡ C3.complex3Scale
      (C3.complexSubtract (signedEigenP H) (signedEigenQ H))
      (Cross.complex3Cross (uP H) (uQ H))
projectedRotationalHelicalFactor H =
  trans
    (cong₂
      (λ omegaP omegaQ →
        Helical.symmetrisedRotationalInteraction
          omegaP (uQ H) omegaQ (uP H))
      (curlEigenP H) (curlEigenQ H))
    (Helical.helicalInputDifferenceFactorization
      (signedEigenP H) (signedEigenQ H) (uP H) (uQ H))

projectedHelicalOrderedPairVector :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {p q k : Z3.FourierMode}
    (H : ProjectedHelicalPairData E I p q k) →
  Signed.orderedPairVelocityInteraction
    (C3.complex3VelocityGalerkinLaws F E I)
    k p q (uP H) (uQ H)
  ≡ C3.complex3Scale
      (C3.complexSubtract (signedEigenQ H) (signedEigenP H))
      (C3.lerayProject3 E I k (Cross.complex3Cross (uP H) (uQ H)))
projectedHelicalOrderedPairVector {F = F} {E} {I} {p} {q} {k} H =
  let
    C = Conv.convectivePair
      (C3.modeVector E p) (C3.modeVector E q) (uP H) (uQ H)
    G = Conv.gradientPair
      (C3.modeVector E p) (C3.modeVector E q) (uP H) (uQ H)
    R = Conv.rotationalPair
      (C3.modeVector E p) (C3.modeVector E q) (uP H) (uQ H)
    X = Cross.complex3Cross (uP H) (uQ H)
    deltaPQ = C3.complexSubtract (signedEigenP H) (signedEigenQ H)
    deltaQP = C3.complexSubtract (signedEigenQ H) (signedEigenP H)

    ordered = orderedPairIsMinusIProjectedConvective
      E I k p q (uP H) (uQ H)

    cSplit : C ≡ C3.complex3Add (C3.complex3Subtract C G) G
    cSplit = sym (subtractThenAddBack C G)

    projectedC :
      C3.lerayProject3 E I k C
      ≡ C3.lerayProject3 E I k (C3.complex3Subtract C G)
    projectedC =
      trans
        (cong (C3.lerayProject3 E I k) cSplit)
        (trans
          (Linear.lerayProjectAdd E I k (C3.complex3Subtract C G) G)
          (trans
            (cong
              (C3.complex3Add
                (C3.lerayProject3 E I k (C3.complex3Subtract C G)))
              (lerayKillsResonantGradient
                E I (resonance H) (outputNonzero H) (uP H) (uQ H)))
            (Field.complex3AddZeroRight
              (C3.lerayProject3 E I k (C3.complex3Subtract C G)))))

    differenceToRotational :
      C3.complex3Subtract C G ≡ C3.complex3Scale (minusI F) R
    differenceToRotational = sym
      (minusIRotationalIsConvectiveMinusGradient
        (C3.modeVector E p) (C3.modeVector E q) (uP H) (uQ H))

    projectedDifference :
      C3.lerayProject3 E I k (C3.complex3Subtract C G)
      ≡ C3.complex3Scale (minusI F)
          (C3.lerayProject3 E I k R)
    projectedDifference =
      trans
        (cong (C3.lerayProject3 E I k) differenceToRotational)
        (ScalarLinear.lerayProjectComplexScale E I k (minusI F) R)

    projectedRotational :
      C3.lerayProject3 E I k R
      ≡ C3.complex3Scale deltaPQ
          (C3.lerayProject3 E I k X)
    projectedRotational =
      trans
        (cong (C3.lerayProject3 E I k)
          (projectedRotationalHelicalFactor H))
        (ScalarLinear.lerayProjectComplexScale E I k deltaPQ X)

    expanded :
      Signed.orderedPairVelocityInteraction
        (C3.complex3VelocityGalerkinLaws F E I)
        k p q (uP H) (uQ H)
      ≡ C3.complex3Scale (minusI F)
          (C3.complex3Scale (minusI F)
            (C3.complex3Scale deltaPQ
              (C3.lerayProject3 E I k X)))
    expanded =
      trans ordered
        (trans
          (cong (C3.complex3Scale (minusI F)) projectedC)
          (trans
            (cong (C3.complex3Scale (minusI F)) projectedDifference)
            (cong
              (λ projectedR →
                C3.complex3Scale (minusI F)
                  (C3.complex3Scale (minusI F) projectedR))
              projectedRotational)))

    collapseMinusI :
      C3.complex3Scale (minusI F)
        (C3.complex3Scale (minusI F)
          (C3.complex3Scale deltaPQ (C3.lerayProject3 E I k X)))
      ≡ C3.complex3Scale deltaQP (C3.lerayProject3 E I k X)
    collapseMinusI =
      trans
        (ScalarLinear.complex3ScaleAssociative
          (minusI F) (minusI F)
          (C3.complex3Scale deltaPQ (C3.lerayProject3 E I k X)))
        (trans
          (cong
            (λ scalar → C3.complex3Scale scalar
              (C3.complex3Scale deltaPQ (C3.lerayProject3 E I k X)))
            (minusISquared F))
          (trans
            (ScalarLinear.complex3ScaleAssociative
              (C3.complexNegate (C3.complexOne F)) deltaPQ
              (C3.lerayProject3 E I k X))
            (cong
              (λ scalar → C3.complex3Scale scalar
                (C3.lerayProject3 E I k X))
              (trans
                (Field.complexNegateMultiplyLeft (C3.complexOne F) deltaPQ)
                (trans
                  (cong C3.complexNegate (Field.complexOneMultiply deltaPQ))
                  (negateSubtractSwap (signedEigenP H) (signedEigenQ H)))))))
  in
  trans expanded collapseMinusI

round106ProjectedHelicalSelfForcingVectorClosed : Bool
round106ProjectedHelicalSelfForcingVectorClosed = true

round106Round93ProjectedConvectiveRotationalVectorSeamClosed : Bool
round106Round93ProjectedConvectiveRotationalVectorSeamClosed = true

round106ProjectedHelicalSelfForcingVectorClosedIsTrue :
  round106ProjectedHelicalSelfForcingVectorClosed ≡ true
round106ProjectedHelicalSelfForcingVectorClosedIsTrue = refl

round106Round93ProjectedConvectiveRotationalVectorSeamClosedIsTrue :
  round106Round93ProjectedConvectiveRotationalVectorSeamClosed ≡ true
round106Round93ProjectedConvectiveRotationalVectorSeamClosedIsTrue = refl
