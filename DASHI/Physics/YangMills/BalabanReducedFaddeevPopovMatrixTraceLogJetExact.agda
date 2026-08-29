module DASHI.Physics.YangMills.BalabanReducedFaddeevPopovMatrixTraceLogJetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- DASHI CONTRIBUTION
--
-- Replace the cyclic identities in the fourth-order trace-log jet by actual
-- finite rational matrix theorems.  A caller now supplies only four matrices
-- X1,...,X4 on one finite index list.  Matrix associativity and tr(AB)=tr(BA)
-- construct every ordered moment and discharge the cyclic equalities consumed
-- by the compact degree-three and degree-four formulas.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanReducedFaddeevPopovTraceLogJetExact as Jet

record FiniteGhostPerturbationMatrices4 (Index : Set) : Set where
  field
    indices : List Index
    X1 X2 X3 X4 : Matrix.Matrix Index
open FiniteGhostPerturbationMatrices4 public

product :
  ∀ {Index} → FiniteGhostPerturbationMatrices4 Index →
  Matrix.Matrix Index → Matrix.Matrix Index → Matrix.Matrix Index
product dataSet = Matrix.matrixProduct (indices dataSet)

trace :
  ∀ {Index} → FiniteGhostPerturbationMatrices4 Index →
  Matrix.Matrix Index → ℚ
trace dataSet = Matrix.matrixTrace (indices dataSet)

traceCong :
  ∀ {Index} (dataSet : FiniteGhostPerturbationMatrices4 Index)
    (left right : Matrix.Matrix Index) →
  (∀ row column → left row column ≡ right row column) →
  trace dataSet left ≡ trace dataSet right
traceCong dataSet left right pointwise =
  Sums.sumRationalCong (indices dataSet)
    (λ index → left index index)
    (λ index → right index index)
    (λ index → pointwise index index)

matrixMoments :
  ∀ {Index} → FiniteGhostPerturbationMatrices4 Index →
  Jet.CyclicGhostTraceMoments4
matrixMoments dataSet = record
  { Jet.CyclicGhostTraceMoments4.tr1 = trace dataSet x1
  ; Jet.CyclicGhostTraceMoments4.tr2 = trace dataSet x2
  ; Jet.CyclicGhostTraceMoments4.tr3 = trace dataSet x3
  ; Jet.CyclicGhostTraceMoments4.tr4 = trace dataSet x4
  ; Jet.CyclicGhostTraceMoments4.tr11 = trace dataSet (mul x1 x1)
  ; Jet.CyclicGhostTraceMoments4.tr12 = trace dataSet (mul x1 x2)
  ; Jet.CyclicGhostTraceMoments4.tr21 = trace dataSet (mul x2 x1)
  ; Jet.CyclicGhostTraceMoments4.tr111 = trace dataSet (mul (mul x1 x1) x1)
  ; Jet.CyclicGhostTraceMoments4.tr13 = trace dataSet (mul x1 x3)
  ; Jet.CyclicGhostTraceMoments4.tr22 = trace dataSet (mul x2 x2)
  ; Jet.CyclicGhostTraceMoments4.tr31 = trace dataSet (mul x3 x1)
  ; Jet.CyclicGhostTraceMoments4.tr112 = trace dataSet (mul (mul x1 x1) x2)
  ; Jet.CyclicGhostTraceMoments4.tr121 = trace dataSet (mul (mul x1 x2) x1)
  ; Jet.CyclicGhostTraceMoments4.tr211 = trace dataSet (mul x2 (mul x1 x1))
  ; Jet.CyclicGhostTraceMoments4.tr1111 =
      trace dataSet (mul (mul x1 x1) (mul x1 x1))
  ; Jet.CyclicGhostTraceMoments4.cyclic12 =
      Matrix.finiteMatrixTraceCyclic ids x2 x1
  ; Jet.CyclicGhostTraceMoments4.cyclic13 =
      Matrix.finiteMatrixTraceCyclic ids x3 x1
  ; Jet.CyclicGhostTraceMoments4.cyclic112-121 = cyclic112121
  ; Jet.CyclicGhostTraceMoments4.cyclic112-211 =
      Matrix.finiteMatrixTraceCyclic ids x2 (mul x1 x1)
  }
  where
  ids = indices dataSet
  x1 = X1 dataSet
  x2 = X2 dataSet
  x3 = X3 dataSet
  x4 = X4 dataSet
  mul = Matrix.matrixProduct ids

  cyclic112121 :
    trace dataSet (mul (mul x1 x2) x1)
    ≡ trace dataSet (mul (mul x1 x1) x2)
  cyclic112121 =
    trans
      (Matrix.finiteMatrixTraceCyclic ids (mul x1 x2) x1)
      (traceCong dataSet
        (mul x1 (mul x1 x2))
        (mul (mul x1 x1) x2)
        (λ row column →
          sym (Matrix.matrixProductAssociative
            ids x1 x1 x2 row column)))

matrixTraceLogJet4 :
  ∀ {Index} → FiniteGhostPerturbationMatrices4 Index →
  Jet.ReducedGhostTraceLogJet4
matrixTraceLogJet4 dataSet = record
  { Jet.ReducedGhostTraceLogJet4.moments = matrixMoments dataSet }

finiteGhostMatrixMomentConstructionLevel : ProofLevel
finiteGhostMatrixMomentConstructionLevel = machineChecked

finiteGhostTraceCyclicitiesDerivedLevel : ProofLevel
finiteGhostTraceCyclicitiesDerivedLevel = machineChecked

finiteGhostFourthOrderTraceLogJetLevel : ProofLevel
finiteGhostFourthOrderTraceLogJetLevel = machineChecked
