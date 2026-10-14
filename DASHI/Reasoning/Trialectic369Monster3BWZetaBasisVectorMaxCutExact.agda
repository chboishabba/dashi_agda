module DASHI.Reasoning.Trialectic369Monster3BWZetaBasisVectorMaxCutExact where

------------------------------------------------------------------------
-- MONSTER 3B W_zeta: CORRECTED BASIS/VECTOR SAME-OBJECT MAX-CUT
--
-- The finite 729 x 90 model is a BASIS-LABEL model.  The literal Moonshine-VOA
-- zeta eigenspace is a state/vector carrier.  Therefore the remaining Monster
-- recognition must not be stated as a bijection between every literal vector
-- and the 65,610 finite basis labels.
--
-- Existing owners already pay three substantial ingredients:
--
--   * the selected literal 3B element is welded to the certified central-zeta
--     kernel class, whose restricted character is ninety copies of the
--     degree-729 Heisenberg character;
--   * the repository owns an explicit 729-dimensional Schrodinger linear
--     carrier with the full finite-Heisenberg action law;
--   * the canonical linear route already identifies the right multiplicity
--     OBJECT as S_zeta = Hom_E(H_zeta,W_zeta), with the intended evaluation
--     H_zeta x S_zeta <-> W_zeta typed as the actual same-object target.
--
-- What remains is now separated into three non-interchangeable payments:
--
--   (1) recognize the explicit Schrodinger representation as the actual
--       H_zeta constituent and intertwine the extraspecial-kernel action;
--   (2) instantiate the actual Hom-space/evaluation inverse on the SAME
--       literal W_zeta vector carrier;
--   (3) choose/recognize a genuine basis of S_zeta indexed by Fin 90 and prove
--       that the resulting tensor basis is the representation-native W_zeta
--       basis on which the six translations/modulation observers act.
--
-- Ninety-fold character isotypy constrains (2)/(3), but it does not choose the
-- Hom-space basis.  Likewise the finite X6 x Fin90 model does not identify all
-- W_zeta vectors with basis labels.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact as Kernel
import DASHI.Moonshine.Monster3BBarracloughWilson729SourceReceiptExact as BW
import DASHI.Moonshine.Monster3BWZetaBasisVectorRecognitionCorrectionExact as Correction
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BFiniteSchrodingerHilbertLiftExact as Schrodinger
import DASHI.Reasoning.Trialectic369SchrodingerHZetaRecognitionMaxCutExact as HZeta
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom

------------------------------------------------------------------------
-- 1. Corrected source package.  This is deliberately NOT an inhabitant here.
------------------------------------------------------------------------

record CorrectedWZetaRecognitionSource (Monster K : Set) : Setω where
  field
    kernelAttachment : Kernel.Actual3BKernelSameElementAttachment Monster K

    schrodingerIsActualHZeta : HZeta.SchrodingerIsActualHZeta

    multiplicityHomSpace : Hom.ActualLinearMultiplicityHomSpace

    literalWZetaIsHomChosenCarrier :
      Hom.ChosenZetaCarrier multiplicityHomSpace
      ≡ Kernel.selectedLiteralZetaSector kernelAttachment

    multiplicityBasis :
      Correction.ActualMultiplicityBasisRecognition multiplicityHomSpace

    basisRecognition :
      Correction.ActualZetaBasisRecognition
        (Kernel.selectedLiteralZetaSector kernelAttachment)

    basisVectorCompatibility :
      Correction.WZetaBasisVectorRecognition
        (Kernel.selectedLiteralZetaSector kernelAttachment)
        multiplicityHomSpace

open CorrectedWZetaRecognitionSource public

------------------------------------------------------------------------
-- 2. Paid donors are exposed without promoting them to the missing source.
------------------------------------------------------------------------

barracloughWilsonBoundary : BW.Boundary
barracloughWilsonBoundary = BW.canonicalBoundary

schrodingerBoundary : Schrodinger.SchrodingerHilbertLiftBoundary
schrodingerBoundary = Schrodinger.canonicalSchrodingerHilbertLiftBoundary

linearHomFrontier : Hom.LinearMultiplicityHomFrontier
linearHomFrontier = Hom.currentLinearMultiplicityHomFrontier

------------------------------------------------------------------------
-- 3. Attribution / WrongType firewalls for the recut.
------------------------------------------------------------------------

data NinetyIsotypyCreatesMultiplicityBasis : Set where
data Degree729CreatesActualHZetaSameObject : Set where
data FiniteModelBasisCreatesLinearEvaluation : Set where
data HomDimensionCreatesNormalizerAction : Set where

ninetyIsotypyDoesNotCreateMultiplicityBasis :
  NinetyIsotypyCreatesMultiplicityBasis → ⊥
ninetyIsotypyDoesNotCreateMultiplicityBasis ()

degree729DoesNotCreateActualHZetaSameObject :
  Degree729CreatesActualHZetaSameObject → ⊥
degree729DoesNotCreateActualHZetaSameObject ()

finiteModelDoesNotCreateLinearEvaluation :
  FiniteModelBasisCreatesLinearEvaluation → ⊥
finiteModelDoesNotCreateLinearEvaluation ()

homDimensionDoesNotCreateNormalizerAction :
  HomDimensionCreatesNormalizerAction → ⊥
homDimensionDoesNotCreateNormalizerAction ()

------------------------------------------------------------------------
-- 4. Machine-readable current max-cut.
------------------------------------------------------------------------

nextResidual : String
nextResidual =
  "Recognize the explicit Schrodinger module as the actual H_zeta constituent; instantiate S_zeta = Hom_E(H_zeta,W_zeta) and its evaluation/recovery on the same literal VOA W_zeta vector carrier; then choose a representation-native basis of S_zeta indexed by Fin 90 and prove basis-tensor compatibility with the finite X6 x Fin90 translation/modulation model. Ninety-fold character isotypy and 65610=729*90 constrain these payments but do not choose the basis or supply the same-object intertwiners. The previous whole-W_zeta-vector <-> finite-basis-label bijection is retired as an overstrong target."

record CorrectedWZetaMaxCutBoundary : Set where
  constructor corrected-w-zeta-maxcut-boundary
  field
    selectedLiteralKernelSameElementAvailable : Bool
    kernelNinetyHeisenbergIsotypyAvailable : Bool
    barracloughWilsonDegree729SourceAlignmentAvailable : Bool
    explicitSchrodingerHZetaCandidatePaid : Bool
    explicitSchrodingerHeisenbergActionPaid : Bool
    homSpaceMultiplicityTargetReused : Bool
    finiteX6Fin90BasisModelPaid : Bool
    wholeWZetaVectorCarrierBijectionToFiniteBasisRequired : Bool
    actualHZetaSameObjectRecognitionPaid : Bool
    actualHomEvaluationSameObjectPaid : Bool
    actualMultiplicityFin90BasisPaid : Bool
    representationNativeWZetaBasisActionPaid : Bool
    correctedRecognitionSourceInhabitedHere : Bool
    nextResidual : String

open CorrectedWZetaMaxCutBoundary public

canonicalBoundary : CorrectedWZetaMaxCutBoundary
canonicalBoundary =
  corrected-w-zeta-maxcut-boundary
    true
    true
    (BW.repoSchrodingerDimension729SourceAligned BW.canonicalBoundary)
    (Schrodinger.hilbertLiftPackaged Schrodinger.canonicalSchrodingerHilbertLiftBoundary)
    (Schrodinger.fullHeisenbergLinearActionPackaged Schrodinger.canonicalSchrodingerHilbertLiftBoundary)
    true
    true
    false
    false
    false
    false
    false
    false
    nextResidual
