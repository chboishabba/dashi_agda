module DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityTransverseRound30Exact where

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
-- DASHI CONTRIBUTION
--
-- Apply the literal Leray-output transversality theorem to the repository's
-- actual exhaustive output fibre.  Every ordered interaction
--
--   -i P_k[(u_p dot q)u_q]
--
-- is transverse at its certified output mode, and finite additivity then
-- proves that the complete projected nonlinear coefficient is transverse.
-- The embedding E and inverse-square datum I remain explicit indices of the
-- same finite system throughout; they cannot be silently resupplied.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as Leray

open Cube using (_∈_)

data AllOutput (output : Z3.FourierMode) :
    List Physical.PhysicalTriadIncidence → Set where
  all-output-empty : AllOutput output []
  all-output-step : ∀ {head tail} →
    Physical.k head ≡ output →
    AllOutput output tail →
    AllOutput output (head ∷ tail)

allOutputFromMembership :
  ∀ output (items : List Physical.PhysicalTriadIncidence) →
  (∀ incidence → incidence ∈ items → Physical.k incidence ≡ output) →
  AllOutput output items
allOutputFromMembership output [] sound = all-output-empty
allOutputFromMembership output (head ∷ tail) sound =
  all-output-step
    (sound head (Cube.here refl))
    (allOutputFromMembership output tail
      (λ incidence member → sound incidence (Cube.there member)))

physicalOutputFiberAll : ∀ cutoff output →
  AllOutput output (Output.physicalOutputFiber cutoff output)
physicalOutputFiberAll cutoff output =
  allOutputFromMembership output
    (Output.physicalOutputFiber cutoff output)
    (λ incidence member → Output.physicalOutputFiberSound member)

bilinearDot3ZeroRight :
  ∀ {r} {F : C3.RealField r}
    (left : C3.Complex3 F) →
  C3.bilinearDot3 left (C3.complex3Zero F)
  ≡ C3.complexZero F
bilinearDot3ZeroRight {F = F} left =
  trans
    (cong₂ C3.complexAdd
      (cong₂ C3.complexAdd
        (Field.complexMultiplyZeroRight (C3.x1 left))
        (Field.complexMultiplyZeroRight (C3.x2 left)))
      (Field.complexMultiplyZeroRight (C3.x3 left)))
    (trans
      (cong
        (λ selected → C3.complexAdd selected (C3.complexZero F))
        (Field.complexAddZeroLeft (C3.complexZero F)))
      (Field.complexAddZeroRight (C3.complexZero F)))

transverseAdd :
  ∀ {r} {F : C3.RealField r}
    (modeVector left right : C3.Complex3 F) →
  C3.bilinearDot3 modeVector left ≡ C3.complexZero F →
  C3.bilinearDot3 modeVector right ≡ C3.complexZero F →
  C3.bilinearDot3 modeVector (C3.complex3Add left right)
  ≡ C3.complexZero F
transverseAdd {F = F} modeVector left right leftZero rightZero =
  trans
    (Algebra.bilinearDot3RightAdd modeVector left right)
    (trans
      (cong₂ C3.complexAdd leftZero rightZero)
      (Field.complexAddZeroLeft (C3.complexZero F)))

projectedOrderedTermTransverse :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  Z3.NonZeroMode output →
  (incidence : Physical.PhysicalTriadIncidence) →
  Physical.k incidence ≡ output →
  C3.bilinearDot3
    (C3.modeVector (Audit.integerEmbedding system) output)
    (Audit.projectedOrderedTerm system incidence)
  ≡ C3.complexZero F
projectedOrderedTermTransverse {F = F} system output nonzero incidence outputExact =
  subst
    (λ selectedOutput →
      C3.bilinearDot3
        (C3.modeVector (Audit.integerEmbedding system) selectedOutput)
        (Audit.projectedOrderedTerm system incidence)
      ≡ C3.complexZero F)
    outputExact
    (trans
      (Scaling.bilinearDot3ScaleRight
        (Signed.minusImaginary (Audit.galerkinLaws system))
        (C3.modeVector
          (Audit.integerEmbedding system) (Physical.k incidence))
        (C3.lerayProject3
          (Audit.integerEmbedding system)
          (Audit.inverseSquare system)
          (Physical.k incidence)
          (C3.complex3Scale
            (C3.bilinearDot3
              (Audit.velocityAt system (Physical.p incidence))
              (C3.modeVector
                (Audit.integerEmbedding system) (Physical.q incidence)))
            (Audit.velocityAt system (Physical.q incidence)))))
      (trans
        (cong
          (C3.complexMultiply
            (Signed.minusImaginary (Audit.galerkinLaws system)))
          (Leray.lerayOutputTransverseExact
            (Audit.integerEmbedding system)
            (Audit.inverseSquare system)
            (Physical.k incidence)
            (subst Z3.NonZeroMode (sym outputExact) nonzero)
            (C3.complex3Scale
              (C3.bilinearDot3
                (Audit.velocityAt system (Physical.p incidence))
                (C3.modeVector
                  (Audit.integerEmbedding system) (Physical.q incidence)))
              (Audit.velocityAt system (Physical.q incidence)))))
        (Field.complexMultiplyZeroRight
          (Signed.minusImaginary (Audit.galerkinLaws system)))))

sumProjectedTermsTransverse :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  Z3.NonZeroMode output →
  (incidences : List Physical.PhysicalTriadIncidence) →
  AllOutput output incidences →
  C3.bilinearDot3
    (C3.modeVector (Audit.integerEmbedding system) output)
    (Audit.sumComplex3 F (Audit.mapTriadTerms system incidences))
  ≡ C3.complexZero F
sumProjectedTermsTransverse system output nonzero [] all-output-empty =
  bilinearDot3ZeroRight
    (C3.modeVector (Audit.integerEmbedding system) output)
sumProjectedTermsTransverse system output nonzero (head ∷ tail)
    (all-output-step headOutput tailOutputs) =
  transverseAdd
    (C3.modeVector (Audit.integerEmbedding system) output)
    (Audit.projectedOrderedTerm system head)
    (Audit.sumComplex3 F (Audit.mapTriadTerms system tail))
    (projectedOrderedTermTransverse
      system output nonzero head headOutput)
    (sumProjectedTermsTransverse
      system output nonzero tail tailOutputs)

projectedNonlinearityTransverseExact :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  Z3.NonZeroMode output →
  C3.bilinearDot3
    (C3.modeVector (Audit.integerEmbedding system) output)
    (Audit.projectedNonlinearity system output)
  ≡ C3.complexZero F
projectedNonlinearityTransverseExact system output nonzero =
  sumProjectedTermsTransverse
    system output nonzero
    (Output.physicalOutputFiber (Audit.cutoff system) output)
    (physicalOutputFiberAll (Audit.cutoff system) output)

projectedNonlinearityTransverseClosed : Bool
projectedNonlinearityTransverseClosed = true

projectedNonlinearityTransverseClosedIsTrue :
  projectedNonlinearityTransverseClosed ≡ true
projectedNonlinearityTransverseClosedIsTrue = refl
