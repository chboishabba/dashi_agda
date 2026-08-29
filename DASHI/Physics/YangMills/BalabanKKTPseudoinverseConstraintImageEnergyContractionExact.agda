module DASHI.Physics.YangMills.BalabanKKTPseudoinverseConstraintImageEnergyContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers", RAIRO Analyse Numerique 8 (1974),
-- 129--151. No DOI was assigned to the cited article.
--
-- DASHI CONTRIBUTION
--
-- Remove an unnecessary global norm bound on the singular KKT pseudoinverse.
-- For K = L L* and its Moore--Penrose inverse K+, the already-constructed
-- repair operator
--
--       R v = L* K+ L v
--
-- is the orthogonal projection onto im(L*), while P=I-R is the admissible
-- projection onto ker(L).  Hence
--
--       ||v||^2 = ||P v||^2 + ||R v||^2
--
-- and therefore, for every literal constraint image s=L v,
--
--       <s,K+ s> = ||R v||^2 <= ||v||^2.
--
-- This estimate is rank/stabilizer agnostic: no smallest nonzero eigenvalue,
-- rowMass(K+), or background-independent null-space dimension is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact as Positive

------------------------------------------------------------------------
-- Orthogonality of admissible projection and constraint repair.
------------------------------------------------------------------------

projectRepairOrthogonal :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    state →
  Rect.finiteDot KKT.physicalStateCarrier
    (Pseudo.admissibleProject pseudoData state)
    (Pseudo.constraintRepair pseudoData state)
  ≡ 0ℚ
projectRepairOrthogonal pseudoData state =
  let
    projected = Pseudo.admissibleProject pseudoData state
    multiplier = Pseudo.pseudoApply pseudoData
      (Pseudo.constraintApply pseudoData state)

    adjoint :
      Rect.finiteDot (Pseudo.multiplierCarrier pseudoData)
        (Pseudo.constraintApply pseudoData projected) multiplier
      ≡ Rect.finiteDot KKT.physicalStateCarrier projected
          (Pseudo.constraintAdjointApply pseudoData multiplier)
    adjoint = Rect.rectangularAdjointExact
      (Pseudo.multiplierCarrier pseudoData)
      KKT.physicalStateCarrier
      (Pseudo.constraintMatrix pseudoData)
      projected multiplier

    constraintZero =
      Pseudo.constraintZero (Pseudo.projectConstraintZero pseudoData state)

    leftZero :
      Rect.finiteDot (Pseudo.multiplierCarrier pseudoData)
        (Pseudo.constraintApply pseudoData projected) multiplier
      ≡ 0ℚ
    leftZero = trans
      (Rect.finiteDotLeftPointwiseCong
        (Pseudo.multiplierCarrier pseudoData) constraintZero)
      (Rect.finiteDotZeroLeft
        (Pseudo.multiplierCarrier pseudoData) multiplier)
  in
  trans (sym adjoint) leftZero

repairProjectOrthogonal :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    state →
  Rect.finiteDot KKT.physicalStateCarrier
    (Pseudo.constraintRepair pseudoData state)
    (Pseudo.admissibleProject pseudoData state)
  ≡ 0ℚ
repairProjectOrthogonal pseudoData state =
  trans
    (Rect.finiteDotSymmetric KKT.physicalStateCarrier
      (Pseudo.constraintRepair pseudoData state)
      (Pseudo.admissibleProject pseudoData state))
    (projectRepairOrthogonal pseudoData state)

stateSplitsProjectPlusRepair :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    state coordinate →
  state coordinate
  ≡ Rect.vectorAdd
      (Pseudo.admissibleProject pseudoData state)
      (Pseudo.constraintRepair pseudoData state) coordinate
stateSplitsProjectPlusRepair pseudoData state coordinate =
  ℚRing.solve-∀
    (state coordinate)
    (Pseudo.constraintRepair pseudoData state coordinate)

projectRepairPythagoras :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    state →
  Rect.finiteNormSq KKT.physicalStateCarrier state
  ≡ Rect.finiteNormSq KKT.physicalStateCarrier
      (Pseudo.admissibleProject pseudoData state)
    + Rect.finiteNormSq KKT.physicalStateCarrier
      (Pseudo.constraintRepair pseudoData state)
projectRepairPythagoras pseudoData state =
  let
    projected = Pseudo.admissibleProject pseudoData state
    repair = Pseudo.constraintRepair pseudoData state
    sum = Rect.vectorAdd projected repair

    stateToSum :
      Rect.finiteNormSq KKT.physicalStateCarrier state
      ≡ Rect.finiteNormSq KKT.physicalStateCarrier sum
    stateToSum = trans
      (Rect.finiteDotLeftPointwiseCong
        KKT.physicalStateCarrier
        (stateSplitsProjectPlusRepair pseudoData state))
      (Rect.finiteDotRightPointwiseCong
        KKT.physicalStateCarrier
        (stateSplitsProjectPlusRepair pseudoData state))

    expandLeft :
      Rect.finiteNormSq KKT.physicalStateCarrier sum
      ≡ Rect.finiteDot KKT.physicalStateCarrier projected sum
        + Rect.finiteDot KKT.physicalStateCarrier repair sum
    expandLeft = Rect.finiteDotAddLeft
      KKT.physicalStateCarrier projected repair sum

    expandProjected :
      Rect.finiteDot KKT.physicalStateCarrier projected sum
      ≡ Rect.finiteNormSq KKT.physicalStateCarrier projected
        + Rect.finiteDot KKT.physicalStateCarrier projected repair
    expandProjected = Rect.finiteDotAddRight
      KKT.physicalStateCarrier projected projected repair

    expandRepair :
      Rect.finiteDot KKT.physicalStateCarrier repair sum
      ≡ Rect.finiteDot KKT.physicalStateCarrier repair projected
        + Rect.finiteNormSq KKT.physicalStateCarrier repair
    expandRepair = Rect.finiteDotAddRight
      KKT.physicalStateCarrier repair projected repair
  in
  trans stateToSum
    (trans expandLeft
      (trans
        (cong₂ _+_ expandProjected expandRepair)
        (trans
          (cong
            (λ crossPair →
              Rect.finiteNormSq KKT.physicalStateCarrier projected
              + crossPair
              + Rect.finiteNormSq KKT.physicalStateCarrier repair)
            (cong₂ _+_
              (projectRepairOrthogonal pseudoData state)
              (repairProjectOrthogonal pseudoData state)))
          (ℚRing.solve-∀
            (Rect.finiteNormSq KKT.physicalStateCarrier projected)
            (Rect.finiteNormSq KKT.physicalStateCarrier repair)))))

constraintRepairNormSqBelowState :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    state →
  Rect.finiteNormSq KKT.physicalStateCarrier
      (Pseudo.constraintRepair pseudoData state)
  ≤ Rect.finiteNormSq KKT.physicalStateCarrier state
constraintRepairNormSqBelowState pseudoData state =
  let
    projectedNorm = Rect.finiteNormSq KKT.physicalStateCarrier
      (Pseudo.admissibleProject pseudoData state)
    repairNorm = Rect.finiteNormSq KKT.physicalStateCarrier
      (Pseudo.constraintRepair pseudoData state)
    projectedNN = Rect.finiteNormSqNonnegative
      KKT.physicalStateCarrier (Pseudo.admissibleProject pseudoData state)
    addBound : repairNorm ≤ projectedNorm + repairNorm
    addBound = subst
      (λ lower → lower ≤ projectedNorm + repairNorm)
      (ℚRing.solve-∀ repairNorm)
      (ℚP.+-mono-≤ projectedNN ℚP.≤-refl)
  in
  subst
    (λ upper → repairNorm ≤ upper)
    (sym (projectRepairPythagoras pseudoData state))
    addBound

constraintImagePseudoinverseEnergyBelowStateNormSq :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    state →
  Positive.pseudoinverseEnergy pseudoData
      (Pseudo.constraintApply pseudoData state)
  ≤ Rect.finiteNormSq KKT.physicalStateCarrier state
constraintImagePseudoinverseEnergyBelowStateNormSq pseudoData state =
  subst
    (λ lower → lower ≤ Rect.finiteNormSq KKT.physicalStateCarrier state)
    (sym
      (Positive.pseudoinverseEnergyAsAdjointNormSq
        pseudoData (Pseudo.constraintApply pseudoData state)))
    (constraintRepairNormSqBelowState pseudoData state)

kktRepairOrthogonalProjectionLevel : ProofLevel
kktRepairOrthogonalProjectionLevel = machineChecked

kktConstraintImagePseudoinverseEnergyContractionLevel : ProofLevel
kktConstraintImagePseudoinverseEnergyContractionLevel = machineChecked
