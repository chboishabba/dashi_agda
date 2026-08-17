module DASHI.Physics.YangMills.BalabanKKTGreenPolarizationLowerBoundExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proc. Cambridge Philosophical
-- Society 51 (1955), 406--413. DOI: 10.1017/S0305004100030401.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Once Round60 has derived K+ >= 0 from the existing Moore--Penrose/Gram
-- carrier, polarization turns every sign-sensitive cross Green term into
-- diagonal energies.  For B(s,d)=<s,K+d> and E(v)=<v,K+v>,
--
--   0 <= E(s+d) = E(s) + 2 B(s,d) + E(d)
--
-- hence
--
--   -(E(s)+E(d)) <= 2 B(s,d).
--
-- No sign assumption on the cross term is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact as Positive

bilinearGreen :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier) →
  (Multiplier → ℚ) → (Multiplier → ℚ) → ℚ
bilinearGreen pseudoData left right =
  Rect.finiteDot
    (Pseudo.multiplierCarrier pseudoData)
    left
    (Pseudo.pseudoApply pseudoData right)

bilinearGreenSymmetric :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    left right →
  bilinearGreen pseudoData left right
  ≡ bilinearGreen pseudoData right left
bilinearGreenSymmetric pseudoData left right =
  trans
    (Rect.symmetricMatrixMovesAcrossDot
      (Pseudo.multiplierCarrier pseudoData)
      (Pseudo.gramPseudoinverse pseudoData)
      (Pseudo.gramPseudoinverseSymmetric pseudoData)
      left right)
    (Rect.finiteDotSymmetric
      (Pseudo.multiplierCarrier pseudoData)
      (Pseudo.pseudoApply pseudoData left)
      right)

pseudoinverseEnergyAddExpansion :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    left right →
  Positive.pseudoinverseEnergy pseudoData (Rect.vectorAdd left right)
  ≡ (Positive.pseudoinverseEnergy pseudoData left
      + bilinearGreen pseudoData right left)
    + (bilinearGreen pseudoData left right
      + Positive.pseudoinverseEnergy pseudoData right)
pseudoinverseEnergyAddExpansion pseudoData left right =
  let
    carrier = Pseudo.multiplierCarrier pseudoData
    matrix = Pseudo.gramPseudoinverse pseudoData
    appliedLeft = Pseudo.pseudoApply pseudoData left
    appliedRight = Pseudo.pseudoApply pseudoData right

    applyAdd : ∀ row →
      Pseudo.pseudoApply pseudoData (Rect.vectorAdd left right) row
      ≡ Rect.vectorAdd appliedLeft appliedRight row
    applyAdd row =
      Rect.applyRectangularAddExact carrier matrix left right row
  in
  trans
    (Rect.finiteDotRightPointwiseCong carrier applyAdd)
    (trans
      (Rect.finiteDotAddRight
        carrier (Rect.vectorAdd left right) appliedLeft appliedRight)
      (cong₂ _+_
        (Rect.finiteDotAddLeft carrier left right appliedLeft)
        (Rect.finiteDotAddLeft carrier left right appliedRight)))

pseudoinverseEnergyAddSymmetricExpansion :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    left right →
  Positive.pseudoinverseEnergy pseudoData (Rect.vectorAdd left right)
  ≡ Positive.pseudoinverseEnergy pseudoData left
    + (bilinearGreen pseudoData left right
      + bilinearGreen pseudoData left right)
    + Positive.pseudoinverseEnergy pseudoData right
pseudoinverseEnergyAddSymmetricExpansion pseudoData left right =
  let
    leftEnergy = Positive.pseudoinverseEnergy pseudoData left
    rightEnergy = Positive.pseudoinverseEnergy pseudoData right
    cross = bilinearGreen pseudoData left right
    reverseCross = bilinearGreen pseudoData right left

    raw = pseudoinverseEnergyAddExpansion pseudoData left right
    replaceReverse :
      (leftEnergy + reverseCross) + (cross + rightEnergy)
      ≡ (leftEnergy + cross) + (cross + rightEnergy)
    replaceReverse =
      cong (λ selected → (leftEnergy + selected) + (cross + rightEnergy))
        (bilinearGreenSymmetric pseudoData right left)
  in
  trans raw
    (trans replaceReverse
      (ℚRing.solve-∀ leftEnergy rightEnergy cross))

polarizationGreenLowerBound :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    source defect →
  - (Positive.pseudoinverseEnergy pseudoData source
      + Positive.pseudoinverseEnergy pseudoData defect)
  ≤ bilinearGreen pseudoData source defect
      + bilinearGreen pseudoData source defect
polarizationGreenLowerBound pseudoData source defect =
  let
    sourceEnergy = Positive.pseudoinverseEnergy pseudoData source
    defectEnergy = Positive.pseudoinverseEnergy pseudoData defect
    cross = bilinearGreen pseudoData source defect

    sumNonnegative :
      0ℚ ≤ Positive.pseudoinverseEnergy pseudoData
        (Rect.vectorAdd source defect)
    sumNonnegative =
      Positive.pseudoinverseEnergyNonnegative pseudoData
        (Rect.vectorAdd source defect)

    expandedNonnegative :
      0ℚ ≤ sourceEnergy + (cross + cross) + defectEnergy
    expandedNonnegative =
      subst
        (λ selected → 0ℚ ≤ selected)
        (pseudoinverseEnergyAddSymmetricExpansion pseudoData source defect)
        sumNonnegative

    differenceNonnegative :
      0ℚ ≤ (cross + cross) - (- (sourceEnergy + defectEnergy))
    differenceNonnegative =
      subst
        (λ selected → 0ℚ ≤ selected)
        (ℚRing.solve-∀ sourceEnergy defectEnergy cross)
        expandedNonnegative
  in
  Norm.nonnegativeDifferenceImpliesBelow differenceNonnegative

kktGreenPolarizationLowerBoundLevel : ProofLevel
kktGreenPolarizationLowerBoundLevel = machineChecked
