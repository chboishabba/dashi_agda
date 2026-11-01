module DASHI.Physics.Closure.NSTriadKNMixedHelicityCompanionMassRound226Exact where

------------------------------------------------------------------------
-- ROUND226 / FIXED-OUTPUT COMPANION MASS = 16 * MIXED-HELICITY MASS
--
-- Round225 proves on the complete fixed-output physical fibre
--
--   sum i K_pq = 4 sum (u_p+ x u_q-).
--
-- On the exact rational C3 carrier multiplication by i preserves Euclidean
-- squared norm, while four copies multiply squared norm by 16. Hence
--
--   ||sum K_pq||^2 = 16 ||sum (u_p+ x u_q-)||^2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225

F : C3.RealField _
F = Rational.rationalRealField

four sixteen : ℚ
four = (1ℚ + 1ℚ) + (1ℚ + 1ℚ)
sixteen = four * four

complexModulusSquaredIScale :
  (z : C3.Complex F) →
  L2.complexModulusSquared (C3.complexMultiply (C3.complexI F) z)
  ≡ L2.complexModulusSquared z
complexModulusSquaredIScale (C3.complex real imaginary) =
  solve (real ∷ imaginary ∷ [])

complex3NormSquaredIScale :
  (v : C3.Complex3 F) →
  L2.complex3NormSquared (C3.complex3Scale (C3.complexI F) v)
  ≡ L2.complex3NormSquared v
complex3NormSquaredIScale (C3.complex3 x y z)
  rewrite complexModulusSquaredIScale x
        | complexModulusSquaredIScale y
        | complexModulusSquaredIScale z = refl

complexModulusSquaredFourCopies :
  (z : C3.Complex F) →
  L2.complexModulusSquared
    (C3.complexAdd (C3.complexAdd z z) (C3.complexAdd z z))
  ≡ sixteen * L2.complexModulusSquared z
complexModulusSquaredFourCopies (C3.complex real imaginary) =
  solve (real ∷ imaginary ∷ [])

complex3NormSquaredFourCopies :
  (v : C3.Complex3 F) →
  L2.complex3NormSquared (R225.fourCopies v)
  ≡ sixteen * L2.complex3NormSquared v
complex3NormSquaredFourCopies (C3.complex3 x y z)
  rewrite complexModulusSquaredFourCopies x
        | complexModulusSquaredFourCopies y
        | complexModulusSquaredFourCopies z =
  solve
    ( L2.complexModulusSquared x
    ∷ L2.complexModulusSquared y
    ∷ L2.complexModulusSquared z
    ∷ [])

complex3ScaleIZero :
  C3.complex3Scale (C3.complexI F) (C3.complex3Zero F)
  ≡ C3.complex3Zero F
complex3ScaleIZero =
  Field.complex3Ext
    (Field.complexMultiplyZeroRight (C3.complexI F))
    (Field.complexMultiplyZeroRight (C3.complexI F))
    (Field.complexMultiplyZeroRight (C3.complexI F))

quadraticKernelCell :
  (E : C3.IntegerEmbedding F)
  (S : Helical.HelicalModeScalars F)
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
quadraticKernelCell E S velocity tau =
  R145.slotKernel
    (R167.normalizedDirection E S (Physical.p tau))
    (R167.normalizedDirection E S (Physical.q tau))
    (velocity (Physical.p tau))
    (velocity (Physical.q tau))

foldIQuadraticKernelIsIScaleFoldKernel :
  (E : C3.IntegerEmbedding F)
  (S : Helical.HelicalModeScalars F)
  (velocity : Z3.FourierMode → C3.Complex3 F)
  (items : List Physical.PhysicalTriadIncidence) →
  R224.foldVector (R225.iQuadraticKernelCell S velocity) items
  ≡ C3.complex3Scale (C3.complexI F)
      (R224.foldVector (quadraticKernelCell E S velocity) items)
foldIQuadraticKernelIsIScaleFoldKernel E S velocity [] = sym complex3ScaleIZero
foldIQuadraticKernelIsIScaleFoldKernel E S velocity (tau ∷ rest) =
  trans
    (cong
      (C3.complex3Add
        (C3.complex3Scale (C3.complexI F)
          (quadraticKernelCell E S velocity tau)))
      (foldIQuadraticKernelIsIScaleFoldKernel E S velocity rest))
    (sym
      (R157.complex3ScaleAdd
        (C3.complexI F)
        (quadraticKernelCell E S velocity tau)
        (R224.foldVector (quadraticKernelCell E S velocity) rest)))

fixedOutputCompanionMassIsSixteenMixedHelicityMass :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (velocity : Z3.FourierMode → C3.Complex3 F)
  (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity)
  (cutoff : Nat) (output : Z3.FourierMode) →
  L2.complex3NormSquared
    (R224.foldVector (quadraticKernelCell E S velocity)
      (Output.physicalOutputFiber cutoff output))
  ≡ sixteen *
      L2.complex3NormSquared
        (R224.foldVector (R224.mixedPlusMinus S velocity)
          (Output.physicalOutputFiber cutoff output))
fixedOutputCompanionMassIsSixteenMixedHelicityMass
    E I S L H velocity P cutoff output =
  let
    fibre = Output.physicalOutputFiber cutoff output
    kernelSum = R224.foldVector (quadraticKernelCell E S velocity) fibre
    mixedSum = R224.foldVector (R224.mixedPlusMinus S velocity) fibre

    iFold :
      R224.foldVector (R225.iQuadraticKernelCell S velocity) fibre
      ≡ C3.complex3Scale (C3.complexI F) kernelSum
    iFold = foldIQuadraticKernelIsIScaleFoldKernel E S velocity fibre

    mixedWeld :
      R224.foldVector (R225.iQuadraticKernelCell S velocity) fibre
      ≡ R225.fourCopies mixedSum
    mixedWeld = R225.fixedOutputQuadraticKernelIsFourMixedHelicityConvolution
      P cutoff output

    vectorEquality :
      C3.complex3Scale (C3.complexI F) kernelSum
      ≡ R225.fourCopies mixedSum
    vectorEquality = trans (sym iFold) mixedWeld
  in
  trans
    (sym (complex3NormSquaredIScale kernelSum))
    (trans
      (cong L2.complex3NormSquared vectorEquality)
      (complex3NormSquaredFourCopies mixedSum))

round226CompanionMassExactlyMixedHelicityMass : Bool
round226CompanionMassExactlyMixedHelicityMass = true

round226MixedHelicityFactorSquared : ℚ
round226MixedHelicityFactorSquared = sixteen

round226MixedHelicityIntegratedBudgetClosed : Bool
round226MixedHelicityIntegratedBudgetClosed = false

round226PackageAClosed : Bool
round226PackageAClosed = false

round226ClayPromotion : Bool
round226ClayPromotion = false

round226CompanionMassExactlyMixedHelicityMassIsTrue :
  round226CompanionMassExactlyMixedHelicityMass ≡ true
round226CompanionMassExactlyMixedHelicityMassIsTrue = refl

round226MixedHelicityIntegratedBudgetClosedIsFalse :
  round226MixedHelicityIntegratedBudgetClosed ≡ false
round226MixedHelicityIntegratedBudgetClosedIsFalse = refl

round226PackageAClosedIsFalse : round226PackageAClosed ≡ false
round226PackageAClosedIsFalse = refl

round226ClayPromotionIsFalse : round226ClayPromotion ≡ false
round226ClayPromotionIsFalse = refl
