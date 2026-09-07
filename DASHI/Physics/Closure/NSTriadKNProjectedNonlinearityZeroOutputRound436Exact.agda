module DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityZeroOutputRound436Exact where

------------------------------------------------------------------------
-- ROUND436 / THE LITERAL PROJECTED NS NONLINEARITY VANISHES AT OUTPUT ZERO
--
-- The remaining R307 orientation seam was the forcing-leg case p = 0.  On the
-- actual projected NS forcing this is not an analytic exceptional case.
--
-- For every inner physical incidence a+b=0, exact Z^3 resonance gives b=-a.
-- If the velocity is transverse at every mode, then
--
--   u_a . b = u_a . (-a) = -(u_a . a) = 0.
--
-- Hence the ordered Galerkin interaction vanishes BEFORE any estimate.  The
-- complete output-zero fibre is therefore a finite sum of zero vectors:
--
--   projectedNonlinearity system 0 = 0.
--
-- The all-mode transversality hypothesis is not invented here: the physical
-- trajectory carrier used by R228/R240 already owns exactly that field.  No
-- mean-zero folklore, shell estimate, helicity assumption, inverse-square law
-- at zero, or cutoff-uniform estimate is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
import Data.Integer.Base as ℤ
import Data.Integer.Properties as ℤP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNIntegerFourierModeAddExact as Add
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3TransverseDifference as Difference
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityTransverseRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityQuadraticHomogeneityRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNNestedInnerSwapCommutatorRound310Exact as R310

sumZeroRightIsNegateLeft :
  (left right : ℤ.ℤ) →
  left ℤ.+ right ≡ ℤ.+ 0 →
  right ≡ ℤ.- left
sumZeroRightIsNegateLeft left right sumZero =
  trans
    (sym (ℤP.+-identityˡ right))
    (trans
      (cong (λ value → value ℤ.+ right)
        (sym (ℤP.+-inverseˡ left)))
      (trans
        (ℤP.+-assoc (ℤ.- left) left right)
        (trans
          (cong ((ℤ.- left) ℤ.+_) sumZero)
          (ℤP.+-identityʳ (ℤ.- left)))))

zeroOutputRightInputIsNegateLeft :
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ Z3.zeroMode →
  Physical.q tau ≡ Z3.negateMode (Physical.p tau)
zeroOutputRightInputIsNegateLeft tau outputZero =
  Add.modeExt
    (sumZeroRightIsNegateLeft
      (Z3.kx (Physical.p tau))
      (Z3.kx (Physical.q tau))
      (cong Z3.kx (trans (Physical.resonance tau) outputZero)))
    (sumZeroRightIsNegateLeft
      (Z3.ky (Physical.p tau))
      (Z3.ky (Physical.q tau))
      (cong Z3.ky (trans (Physical.resonance tau) outputZero)))
    (sumZeroRightIsNegateLeft
      (Z3.kz (Physical.p tau))
      (Z3.kz (Physical.q tau))
      (cong Z3.kz (trans (Physical.resonance tau) outputZero)))

zeroOutputAdvectionScalar :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode))
    (tau : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ Z3.zeroMode →
  C3.bilinearDot3
    (Audit.velocity system (Physical.p tau))
    (C3.modeVector E (Physical.q tau))
  ≡ C3.complexZero F
zeroOutputAdvectionScalar {F = F} {E = E}
    system velocityTransverse tau outputZero =
  let
    p = Physical.p tau
    q = Physical.q tau
    uP = Audit.velocity system p
    qIsNegP = zeroOutputRightInputIsNegateLeft tau outputZero
  in
  trans
    (cong (C3.bilinearDot3 uP)
      (cong (C3.modeVector E) qIsNegP))
    (trans
      (cong (C3.bilinearDot3 uP)
        (C3.modeVectorNegation E p))
      (trans
        (Difference.bilinearDot3NegateRight uP (C3.modeVector E p))
        (trans
          (cong C3.complexNegate
            (trans
              (Algebra.bilinearDot3Commutative uP (C3.modeVector E p))
              (velocityTransverse p)))
          (Hermitian.complexNegateZero F))))

lerayZeroVector :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (mode : Z3.FourierMode) →
  C3.lerayProject3 E I mode (C3.complex3Zero F)
  ≡ C3.complex3Zero F
lerayZeroVector {F = F} E I mode =
  trans
    (cong (C3.lerayProject3 E I mode)
      (sym (R106.complex3ScaleZeroScalar (C3.complex3Zero F))))
    (trans
      (R94.lerayScale E I mode
        (C3.complexZero F) (C3.complex3Zero F))
      (R106.complex3ScaleZeroScalar
        (C3.lerayProject3 E I mode (C3.complex3Zero F))))

projectedOrderedTermAtZeroOutputIsZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode))
    (tau : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≡ Z3.zeroMode →
  Audit.projectedOrderedTerm system tau ≡ C3.complex3Zero F
projectedOrderedTermAtZeroOutputIsZero {F = F} {E = E} {I = I}
    system velocityTransverse tau outputZero =
  let
    q = Physical.q tau
    innerZero :
      C3.complex3Scale
        (C3.bilinearDot3
          (Audit.velocity system (Physical.p tau))
          (C3.modeVector E q))
        (Audit.velocity system q)
      ≡ C3.complex3Zero F
    innerZero =
      trans
        (cong
          (λ scalar → C3.complex3Scale scalar (Audit.velocity system q))
          (zeroOutputAdvectionScalar system velocityTransverse tau outputZero))
        (R106.complex3ScaleZeroScalar (Audit.velocity system q))
  in
  trans
    (cong
      (C3.complex3Scale (C3.complexNegate (C3.complexI F)))
      (trans
        (cong (C3.lerayProject3 E I (Physical.k tau)) innerZero)
        (lerayZeroVector E I (Physical.k tau))))
    (R106.complex3ScaleZeroVector
      (C3.complexNegate (C3.complexI F)))

foldZeroOutputTerms :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode))
    (items : List Physical.PhysicalTriadIncidence) →
  R30.AllOutput Z3.zeroMode items →
  R310.R224.foldVector (Audit.projectedOrderedTerm system) items
  ≡ C3.complex3Zero F
foldZeroOutputTerms system velocityTransverse [] R30.all-output-empty = refl
foldZeroOutputTerms system velocityTransverse (tau ∷ rest)
    (R30.all-output-step headOutput tailOutputs) =
  trans
    (cong₂ C3.complex3Add
      (projectedOrderedTermAtZeroOutputIsZero
        system velocityTransverse tau headOutput)
      (foldZeroOutputTerms system velocityTransverse rest tailOutputs))
    (R230.complex3AddZeroLeft (C3.complex3Zero _))

projectedNonlinearityAtZeroIsZero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  ((mode : Z3.FourierMode) →
    Helical.Transverse E mode (Audit.velocity system mode)) →
  Audit.projectedNonlinearity system Z3.zeroMode
  ≡ C3.complex3Zero F
projectedNonlinearityAtZeroIsZero system velocityTransverse =
  trans
    (R310.projectedNonlinearityAsFold system Z3.zeroMode)
    (foldZeroOutputTerms
      system velocityTransverse
      (Output.physicalOutputFiber (Audit.cutoff system) Z3.zeroMode)
      (R30.physicalOutputFiberAll (Audit.cutoff system) Z3.zeroMode))

round436ZeroOutputResonanceForcesOppositeInputs : Bool
round436ZeroOutputResonanceForcesOppositeInputs = true

round436ZeroOutputOrderedInteractionVanishes : Bool
round436ZeroOutputOrderedInteractionVanishes = true

round436ProjectedNonlinearityAtZeroVanishes : Bool
round436ProjectedNonlinearityAtZeroVanishes = true

round436UsesAllModeVelocityTransversalityOnly : Bool
round436UsesAllModeVelocityTransversalityOnly = true

round436UsesHelicityAssumption : Bool
round436UsesHelicityAssumption = false

round436UsesAnyAnalyticEstimate : Bool
round436UsesAnyAnalyticEstimate = false

round436PackageAClosed : Bool
round436PackageAClosed = false

round436ClayPromotion : Bool
round436ClayPromotion = false

round436ProjectedNonlinearityAtZeroVanishesIsTrue :
  round436ProjectedNonlinearityAtZeroVanishes ≡ true
round436ProjectedNonlinearityAtZeroVanishesIsTrue = refl

round436UsesHelicityAssumptionIsFalse :
  round436UsesHelicityAssumption ≡ false
round436UsesHelicityAssumptionIsFalse = refl

round436UsesAnyAnalyticEstimateIsFalse :
  round436UsesAnyAnalyticEstimate ≡ false
round436UsesAnyAnalyticEstimateIsFalse = refl
