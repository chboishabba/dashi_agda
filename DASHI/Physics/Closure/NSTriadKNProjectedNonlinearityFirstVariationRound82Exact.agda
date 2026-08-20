module DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND82 / EXACT FIRST VARIATION OF THE LITERAL PROJECTED NONLINEARITY
--
-- The executable compact-transfer audit differentiates the finite Galerkin
-- nonlinearity by the familiar quadratic polarization
--
--   DN(u)[v] = B(u,v) + B(v,u).
--
-- This file proves that structure directly on the repository's literal finite
-- Fourier carrier.  No differential-calculus axiom is needed: the ordered
-- interaction is bilinear, Leray is additive, and the physical output fibre is
-- finite.  We therefore obtain an exact polynomial expansion
--
--   N(u+v)
--     = N(u) + DN(u)[v] + B(v,v),
--
-- with `projectedNonlinearityFirstVariation` equal to the two mixed terms and
-- `projectedNonlinearityQuadraticRemainder` equal to the exact B(v,v) remainder.
-- The remaining C4 task is no longer to invent/assume DN; it is to identify the
-- selected packet-transfer derivative built from this literal first variation
-- and prove the required physical relative-growth estimate.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit

complex3AddZeroLeft :
  ∀ {r} {F : C3.RealField r} (u : C3.Complex3 F) →
  C3.complex3Add (C3.complex3Zero F) u ≡ u
complex3AddZeroLeft u =
  trans
    (Field.complex3AddCommutative (C3.complex3Zero _) u)
    (Field.complex3AddZeroRight u)

complex3Interchange :
  ∀ {r} {F : C3.RealField r}
    (a b c d : C3.Complex3 F) →
  C3.complex3Add (C3.complex3Add a b) (C3.complex3Add c d)
  ≡ C3.complex3Add (C3.complex3Add a c) (C3.complex3Add b d)
complex3Interchange a b c d =
  trans
    (Field.complex3AddAssociative a b (C3.complex3Add c d))
    (trans
      (cong (C3.complex3Add a)
        (sym (Field.complex3AddAssociative b c d)))
      (trans
        (cong (C3.complex3Add a)
          (cong (λ middle → C3.complex3Add middle d)
            (Field.complex3AddCommutative b c)))
        (trans
          (cong (C3.complex3Add a)
            (Field.complex3AddAssociative c b d))
          (sym
            (Field.complex3AddAssociative
              a c (C3.complex3Add b d))))))

complex3PolarizationReassociate :
  ∀ {r} {F : C3.RealField r}
    (a b c d : C3.Complex3 F) →
  C3.complex3Add (C3.complex3Add a b) (C3.complex3Add c d)
  ≡ C3.complex3Add (C3.complex3Add a (C3.complex3Add b c)) d
complex3PolarizationReassociate a b c d =
  trans
    (Field.complex3AddAssociative a b (C3.complex3Add c d))
    (trans
      (cong (C3.complex3Add a)
        (sym (Field.complex3AddAssociative b c d)))
      (sym (Field.complex3AddAssociative a (C3.complex3Add b c) d)))

complexNegateAdd :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Complex F) →
  C3.complexNegate (C3.complexAdd a b)
  ≡ C3.complexAdd (C3.complexNegate a) (C3.complexNegate b)
complexNegateAdd {F = F}
    (C3.complex ar ai) (C3.complex br bi) =
  Field.complexExt
    (Algebra.realNegateAdd F ar br)
    (Algebra.realNegateAdd F ai bi)

complex3NegateAdd :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  C3.complex3Negate (C3.complex3Add u v)
  ≡ C3.complex3Add (C3.complex3Negate u) (C3.complex3Negate v)
complex3NegateAdd
    (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Field.complex3Ext
    (complexNegateAdd ux vx)
    (complexNegateAdd uy vy)
    (complexNegateAdd uz vz)

complex3SubtractPairDistributes :
  ∀ {r} {F : C3.RealField r}
    (u v a b : C3.Complex3 F) →
  C3.complex3Subtract
    (C3.complex3Add u v)
    (C3.complex3Add a b)
  ≡
  C3.complex3Add
    (C3.complex3Subtract u a)
    (C3.complex3Subtract v b)
complex3SubtractPairDistributes u v a b =
  trans
    (cong (C3.complex3Add (C3.complex3Add u v))
      (complex3NegateAdd a b))
    (complex3Interchange u v
      (C3.complex3Negate a) (C3.complex3Negate b))

complex3ScaleVectorAdd :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F)
    (u v : C3.Complex3 F) →
  C3.complex3Scale scalar (C3.complex3Add u v)
  ≡ C3.complex3Add
      (C3.complex3Scale scalar u)
      (C3.complex3Scale scalar v)
complex3ScaleVectorAdd scalar
    (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Field.complex3Ext
    (Algebra.complexMultiplyDistributesLeft scalar ux vx)
    (Algebra.complexMultiplyDistributesLeft scalar uy vy)
    (Algebra.complexMultiplyDistributesLeft scalar uz vz)

complex3ScaleScalarAdd :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Complex F)
    (u : C3.Complex3 F) →
  C3.complex3Scale (C3.complexAdd a b) u
  ≡ C3.complex3Add (C3.complex3Scale a u) (C3.complex3Scale b u)
complex3ScaleScalarAdd a b (C3.complex3 ux uy uz) =
  Field.complex3Ext
    (Algebra.complexMultiplyDistributesRight a b ux)
    (Algebra.complexMultiplyDistributesRight a b uy)
    (Algebra.complexMultiplyDistributesRight a b uz)

lerayCorrection :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode) →
  C3.Complex3 F → C3.Complex3 F
lerayCorrection {F = F} E I k value =
  C3.complex3Scale
    (C3.complexMultiply
      (C3.realEmbed F (C3.inverseNormSquared I k))
      (C3.bilinearDot3 (C3.modeVector E k) value))
    (C3.modeVector E k)

lerayCorrectionAdd :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  lerayCorrection E I k (C3.complex3Add u v)
  ≡ C3.complex3Add (lerayCorrection E I k u) (lerayCorrection E I k v)
lerayCorrectionAdd {F = F} E I k u v =
  let
    radiusInverse = C3.realEmbed F (C3.inverseNormSquared I k)
    wave = C3.modeVector E k
    dotU = C3.bilinearDot3 wave u
    dotV = C3.bilinearDot3 wave v
  in
  trans
    (cong
      (λ dot →
        C3.complex3Scale
          (C3.complexMultiply radiusInverse dot) wave)
      (Field.bilinearDotAddRight wave u v))
    (trans
      (cong
        (λ scalar → C3.complex3Scale scalar wave)
        (Algebra.complexMultiplyDistributesLeft radiusInverse dotU dotV))
      (complex3ScaleScalarAdd
        (C3.complexMultiply radiusInverse dotU)
        (C3.complexMultiply radiusInverse dotV)
        wave))

lerayProjectAdd :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  C3.lerayProject3 E I k (C3.complex3Add u v)
  ≡ C3.complex3Add
      (C3.lerayProject3 E I k u)
      (C3.lerayProject3 E I k v)
lerayProjectAdd E I k u v =
  trans
    (cong
      (C3.complex3Subtract (C3.complex3Add u v))
      (lerayCorrectionAdd E I k u v))
    (complex3SubtractPairDistributes
      u v (lerayCorrection E I k u) (lerayCorrection E I k v))

minusI :
  ∀ {r} (F : C3.RealField r) → C3.Complex F
minusI F = C3.complexNegate (C3.complexI F)

orderedInteractionAddLeft :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (u v w : C3.Complex3 F) →
  Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I)
      k p q (C3.complex3Add u v) w
  ≡
  C3.complex3Add
    (Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I) k p q u w)
    (Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I) k p q v w)
orderedInteractionAddLeft {F = F} E I k p q u v w =
  let
    wave = C3.modeVector E q
    dotU = C3.bilinearDot3 u wave
    dotV = C3.bilinearDot3 v wave
    first = C3.complex3Scale dotU w
    second = C3.complex3Scale dotV w
  in
  trans
    (cong
      (λ dot →
        C3.complex3Scale (minusI F)
          (C3.lerayProject3 E I k (C3.complex3Scale dot w)))
      (Additive.bilinearDot3LeftAdd u v wave))
    (trans
      (cong
        (λ inside →
          C3.complex3Scale (minusI F)
            (C3.lerayProject3 E I k inside))
        (complex3ScaleScalarAdd dotU dotV w))
      (trans
        (cong (C3.complex3Scale (minusI F))
          (lerayProjectAdd E I k first second))
        (complex3ScaleVectorAdd
          (minusI F)
          (C3.lerayProject3 E I k first)
          (C3.lerayProject3 E I k second))))

orderedInteractionAddRight :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode)
    (u v w : C3.Complex3 F) →
  Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I)
      k p q u (C3.complex3Add v w)
  ≡
  C3.complex3Add
    (Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I) k p q u v)
    (Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I) k p q u w)
orderedInteractionAddRight {F = F} E I k p q u v w =
  let
    dot = C3.bilinearDot3 u (C3.modeVector E q)
    first = C3.complex3Scale dot v
    second = C3.complex3Scale dot w
  in
  trans
    (cong
      (λ inside →
        C3.complex3Scale (minusI F)
          (C3.lerayProject3 E I k inside))
      (complex3ScaleVectorAdd dot v w))
    (trans
      (cong (C3.complex3Scale (minusI F))
        (lerayProjectAdd E I k first second))
      (complex3ScaleVectorAdd
        (minusI F)
        (C3.lerayProject3 E I k first)
        (C3.lerayProject3 E I k second)))

VelocityField :
  ∀ {r} (F : C3.RealField r) → Set r
VelocityField F = Z3.FourierMode → C3.Complex3 F

fieldAdd :
  ∀ {r} {F : C3.RealField r} →
  VelocityField F → VelocityField F → VelocityField F
fieldAdd left right mode = C3.complex3Add (left mode) (right mode)

mixedProjectedOrderedTerm :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  VelocityField F → VelocityField F →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
mixedProjectedOrderedTerm system left right incidence =
  Signed.orderedVelocityInteraction
    (Audit.galerkinLaws system)
    (Physical.k incidence)
    (Physical.p incidence)
    (Physical.q incidence)
    (left (Physical.p incidence))
    (right (Physical.q incidence))

mixedTerms :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  VelocityField F → VelocityField F →
  List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
mixedTerms system left right [] = []
mixedTerms system left right (incidence ∷ rest) =
  mixedProjectedOrderedTerm system left right incidence
  ∷ mixedTerms system left right rest

mixedProjectedNonlinearity :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  VelocityField F → VelocityField F →
  Z3.FourierMode → C3.Complex3 F
mixedProjectedNonlinearity system left right output =
  Audit.sumVectors
    (mixedTerms system left right (Audit.concreteTriadsAt system output))

sumMixedAddLeft :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left₁ left₂ right : VelocityField F)
    (incidences : List Physical.PhysicalTriadIncidence) →
  Audit.sumVectors (mixedTerms system (fieldAdd left₁ left₂) right incidences)
  ≡
  C3.complex3Add
    (Audit.sumVectors (mixedTerms system left₁ right incidences))
    (Audit.sumVectors (mixedTerms system left₂ right incidences))
sumMixedAddLeft system left₁ left₂ right [] =
  sym (complex3AddZeroLeft (C3.complex3Zero _))
sumMixedAddLeft {F = F} {E = E} {I = I}
    system left₁ left₂ right (incidence ∷ rest) =
  let
    k = Physical.k incidence
    p = Physical.p incidence
    q = Physical.q incidence
    a = mixedProjectedOrderedTerm system left₁ right incidence
    b = mixedProjectedOrderedTerm system left₂ right incidence
    tail₁ = Audit.sumVectors (mixedTerms system left₁ right rest)
    tail₂ = Audit.sumVectors (mixedTerms system left₂ right rest)
  in
  trans
    (cong₂ C3.complex3Add
      (orderedInteractionAddLeft E I k p q
        (left₁ p) (left₂ p) (right q))
      (sumMixedAddLeft system left₁ left₂ right rest))
    (complex3Interchange a b tail₁ tail₂)

sumMixedAddRight :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left right₁ right₂ : VelocityField F)
    (incidences : List Physical.PhysicalTriadIncidence) →
  Audit.sumVectors (mixedTerms system left (fieldAdd right₁ right₂) incidences)
  ≡
  C3.complex3Add
    (Audit.sumVectors (mixedTerms system left right₁ incidences))
    (Audit.sumVectors (mixedTerms system left right₂ incidences))
sumMixedAddRight system left right₁ right₂ [] =
  sym (complex3AddZeroLeft (C3.complex3Zero _))
sumMixedAddRight {F = F} {E = E} {I = I}
    system left right₁ right₂ (incidence ∷ rest) =
  let
    k = Physical.k incidence
    p = Physical.p incidence
    q = Physical.q incidence
    a = mixedProjectedOrderedTerm system left right₁ incidence
    b = mixedProjectedOrderedTerm system left right₂ incidence
    tail₁ = Audit.sumVectors (mixedTerms system left right₁ rest)
    tail₂ = Audit.sumVectors (mixedTerms system left right₂ rest)
  in
  trans
    (cong₂ C3.complex3Add
      (orderedInteractionAddRight E I k p q
        (left p) (right₁ q) (right₂ q))
      (sumMixedAddRight system left right₁ right₂ rest))
    (complex3Interchange a b tail₁ tail₂)

mixedProjectedNonlinearityAddLeft :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left₁ left₂ right : VelocityField F)
    output →
  mixedProjectedNonlinearity system (fieldAdd left₁ left₂) right output
  ≡ C3.complex3Add
      (mixedProjectedNonlinearity system left₁ right output)
      (mixedProjectedNonlinearity system left₂ right output)
mixedProjectedNonlinearityAddLeft system left₁ left₂ right output =
  sumMixedAddLeft system left₁ left₂ right (Audit.concreteTriadsAt system output)

mixedProjectedNonlinearityAddRight :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (left right₁ right₂ : VelocityField F)
    output →
  mixedProjectedNonlinearity system left (fieldAdd right₁ right₂) output
  ≡ C3.complex3Add
      (mixedProjectedNonlinearity system left right₁ output)
      (mixedProjectedNonlinearity system left right₂ output)
mixedProjectedNonlinearityAddRight system left right₁ right₂ output =
  sumMixedAddRight system left right₁ right₂ (Audit.concreteTriadsAt system output)

projectedNonlinearityAsMixedSelf :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    output →
  Audit.projectedNonlinearity system output
  ≡ mixedProjectedNonlinearity system
      (Audit.velocity system) (Audit.velocity system) output
projectedNonlinearityAsMixedSelf system output = refl

projectedNonlinearityFirstVariation :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  VelocityField F → Z3.FourierMode → C3.Complex3 F
projectedNonlinearityFirstVariation system perturbation output =
  C3.complex3Add
    (mixedProjectedNonlinearity system
      (Audit.velocity system) perturbation output)
    (mixedProjectedNonlinearity system
      perturbation (Audit.velocity system) output)

projectedNonlinearityQuadraticRemainder :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  VelocityField F → Z3.FourierMode → C3.Complex3 F
projectedNonlinearityQuadraticRemainder system perturbation output =
  mixedProjectedNonlinearity system perturbation perturbation output

projectedNonlinearityPolarizationExact :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (perturbation : VelocityField F)
    output →
  mixedProjectedNonlinearity system
    (fieldAdd (Audit.velocity system) perturbation)
    (fieldAdd (Audit.velocity system) perturbation)
    output
  ≡
  C3.complex3Add
    (C3.complex3Add
      (Audit.projectedNonlinearity system output)
      (projectedNonlinearityFirstVariation system perturbation output))
    (projectedNonlinearityQuadraticRemainder system perturbation output)
projectedNonlinearityPolarizationExact system perturbation output =
  let
    u = Audit.velocity system
    v = perturbation
    uu = mixedProjectedNonlinearity system u u output
    uv = mixedProjectedNonlinearity system u v output
    vu = mixedProjectedNonlinearity system v u output
    vv = mixedProjectedNonlinearity system v v output
  in
  trans
    (mixedProjectedNonlinearityAddLeft
      system u v (fieldAdd u v) output)
    (trans
      (cong₂ C3.complex3Add
        (mixedProjectedNonlinearityAddRight system u u v output)
        (mixedProjectedNonlinearityAddRight system v u v output))
      (trans
        (complex3PolarizationReassociate uu uv vu vv)
        (cong
          (λ base →
            C3.complex3Add
              (C3.complex3Add base (C3.complex3Add uv vu)) vv)
          (sym (projectedNonlinearityAsMixedSelf system output)))))

round82LiteralProjectedNonlinearityBilinear : Bool
round82LiteralProjectedNonlinearityBilinear = true

round82LiteralProjectedNonlinearityFirstVariationConstructed : Bool
round82LiteralProjectedNonlinearityFirstVariationConstructed = true

round82LiteralProjectedNonlinearityPolarizationExact : Bool
round82LiteralProjectedNonlinearityPolarizationExact = true

round82LiteralProjectedNonlinearityPolarizationExactIsTrue :
  round82LiteralProjectedNonlinearityPolarizationExact ≡ true
round82LiteralProjectedNonlinearityPolarizationExactIsTrue = refl
