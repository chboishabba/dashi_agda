module DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- DASHI CONTRIBUTION
--
-- Construct and verify the literal Kronecker coordinate basis on the complete
-- 3072-coordinate side-four SU(2) carrier.  The proof does not assume an
-- abstract orthonormal basis: it proves selector identities recursively for
-- the cyclic carrier and compositionally for finite Cartesian products.
--
-- For the physical basis vector e_y this gives
--
--   ||e_y||^2 = 1,
--   (M e_y)(x) = M(x,y),
--   v(x)^2 <= ||v||^2.
--
-- Therefore any squared operator estimate
--
--   ||M v||^2 <= B ||v||^2
--
-- yields the literal matrix-entry estimate M(x,y)^2 <= B.  At B=4096 the
-- ordered rational calculation proves |M(x,y)| <= 64, closing the formerly
-- conditional norm-to-entry socket in the Combes--Thomas promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; _/_; ∣_∣; NonNegative; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Cell
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2CauchyInverseSquaredExact as Cauchy
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33CombesThomasSquaredHalfGapExact as Squared

------------------------------------------------------------------------
-- Finite Kronecker selectors.
------------------------------------------------------------------------

kronecker :
  ∀ {A : Set} → DecidableEquality A → A → A → ℚ
kronecker decide left right with decide left right
... | yes _ = 1ℚ
... | no _ = 0ℚ

record FiniteSelector (A : Set) : Set₁ where
  field
    elements : List A
    decide : DecidableEquality A
    selectorExact : ∀ (value : A → ℚ) target →
      Sums.sumRational elements
        (λ candidate →
          value candidate * kronecker decide candidate target)
      ≡ value target

open FiniteSelector public

cyclicKroneckerSucExact :
  ∀ {n} (left right : CyclicIndex n) →
  kronecker cyclicIndexDecidableEquality
    (sucᵢ left) (sucᵢ right)
  ≡ kronecker cyclicIndexDecidableEquality left right
cyclicKroneckerSucExact left right
  with cyclicIndexDecidableEquality left right
... | yes refl = refl
... | no _ = refl

cyclicSelectorExact :
  ∀ n (value : CyclicIndex n → ℚ) target →
  Sums.sumRational (allCyclicIndices n)
    (λ candidate →
      value candidate
        * kronecker cyclicIndexDecidableEquality candidate target)
  ≡ value target
cyclicSelectorExact zero value ()
cyclicSelectorExact (suc n) value zeroᵢ =
  let
    tailTerm : CyclicIndex (suc n) → ℚ
    tailTerm candidate =
      value candidate
        * kronecker cyclicIndexDecidableEquality candidate zeroᵢ

    tailZero :
      Sums.sumRational
        (map sucᵢ (allCyclicIndices n)) tailTerm
      ≡ 0ℚ
    tailZero =
      trans
        (Fubini.sumRationalMap
          sucᵢ (allCyclicIndices n) tailTerm)
        (trans
          (Sums.sumRationalCong
            (allCyclicIndices n)
            (λ candidate → tailTerm (sucᵢ candidate))
            (λ _ → 0ℚ)
            (λ candidate → ℚRing.solve []))
          (Fubini.sumRationalZero (allCyclicIndices n)))
  in
  trans
    (cong
      (value zeroᵢ
        * kronecker cyclicIndexDecidableEquality zeroᵢ zeroᵢ +_)
      tailZero)
    (ℚRing.solve-∀ (value zeroᵢ))
cyclicSelectorExact (suc n) value (sucᵢ target) =
  let
    tailTerm : CyclicIndex (suc n) → ℚ
    tailTerm candidate =
      value candidate
        * kronecker cyclicIndexDecidableEquality
            candidate (sucᵢ target)

    tailExact :
      Sums.sumRational
        (map sucᵢ (allCyclicIndices n)) tailTerm
      ≡ value (sucᵢ target)
    tailExact =
      trans
        (Fubini.sumRationalMap
          sucᵢ (allCyclicIndices n) tailTerm)
        (trans
          (Sums.sumRationalCong
            (allCyclicIndices n)
            (λ candidate → tailTerm (sucᵢ candidate))
            (λ candidate →
              value (sucᵢ candidate)
                * kronecker cyclicIndexDecidableEquality
                    candidate target)
            (λ candidate →
              cong
                (value (sucᵢ candidate) *_)
                (cyclicKroneckerSucExact candidate target)))
          (cyclicSelectorExact n
            (λ candidate → value (sucᵢ candidate)) target))
  in
  trans
    (cong
      (value zeroᵢ
        * kronecker cyclicIndexDecidableEquality
            zeroᵢ (sucᵢ target) +_)
      tailExact)
    (ℚRing.solve-∀ (value (sucᵢ target)))

cyclicFiniteSelector : ∀ n → FiniteSelector (CyclicIndex n)
cyclicFiniteSelector n = record
  { elements = allCyclicIndices n
  ; decide = cyclicIndexDecidableEquality
  ; selectorExact = cyclicSelectorExact n
  }

productKroneckerFactorExact :
  ∀ {A B : Set}
    (decideA : DecidableEquality A)
    (decideB : DecidableEquality B)
    (leftA rightA : A)
    (leftB rightB : B) →
  kronecker (productDecidableEquality decideA decideB)
    (pair leftA leftB) (pair rightA rightB)
  ≡ kronecker decideA leftA rightA
      * kronecker decideB leftB rightB
productKroneckerFactorExact
    decideA decideB leftA rightA leftB rightB
  with decideA leftA rightA | decideB leftB rightB
... | yes refl | yes refl = ℚRing.solve []
... | yes refl | no _ = ℚRing.solve []
... | no _ | yes refl = ℚRing.solve []
... | no _ | no _ = ℚRing.solve []

productFiniteSelector :
  ∀ {A B : Set} →
  FiniteSelector A → FiniteSelector B →
  FiniteSelector (Product A B)
productFiniteSelector {A} {B} selectorA selectorB = record
  { elements = cartesian (elements selectorA) (elements selectorB)
  ; decide = productDecidableEquality
      (decide selectorA) (decide selectorB)
  ; selectorExact = productSelector
  }
  where
  productSelector :
    ∀ (value : Product A B → ℚ) target →
    Sums.sumRational
      (cartesian (elements selectorA) (elements selectorB))
      (λ candidate →
        value candidate
          * kronecker
              (productDecidableEquality
                (decide selectorA) (decide selectorB))
              candidate target)
    ≡ value target
  productSelector value (pair targetA targetB) =
    let
      innerExact : ∀ candidateA →
        Sums.sumRational (elements selectorB)
          (λ candidateB →
            value (pair candidateA candidateB)
              * kronecker
                  (productDecidableEquality
                    (decide selectorA) (decide selectorB))
                  (pair candidateA candidateB)
                  (pair targetA targetB))
        ≡ value (pair candidateA targetB)
            * kronecker (decide selectorA) candidateA targetA
      innerExact candidateA =
        let
          coefficient =
            kronecker (decide selectorA) candidateA targetA

          innerValue : B → ℚ
          innerValue candidateB =
            value (pair candidateA candidateB)
              * kronecker (decide selectorB) candidateB targetB
        in
        trans
          (Sums.sumRationalCong
            (elements selectorB)
            (λ candidateB →
              value (pair candidateA candidateB)
                * kronecker
                    (productDecidableEquality
                      (decide selectorA) (decide selectorB))
                    (pair candidateA candidateB)
                    (pair targetA targetB))
            (λ candidateB → coefficient * innerValue candidateB)
            (λ candidateB →
              trans
                (cong
                  (value (pair candidateA candidateB) *_)
                  (productKroneckerFactorExact
                    (decide selectorA) (decide selectorB)
                    candidateA targetA candidateB targetB))
                (ℚRing.solve [])))
          (trans
            (Sums.sumRationalScale
              coefficient (elements selectorB) innerValue)
            (trans
              (cong
                (coefficient *_)
                (selectorExact selectorB
                  (λ candidateB → value (pair candidateA candidateB))
                  targetB))
              (ℚRing.solve [])))
    in
    trans
      (Fubini.sumCartesian
        (elements selectorA) (elements selectorB)
        (λ candidate →
          value candidate
            * kronecker
                (productDecidableEquality
                  (decide selectorA) (decide selectorB))
                candidate (pair targetA targetB)))
      (trans
        (Sums.sumRationalCong
          (elements selectorA)
          (λ candidateA →
            Sums.sumRational (elements selectorB)
              (λ candidateB →
                value (pair candidateA candidateB)
                  * kronecker
                      (productDecidableEquality
                        (decide selectorA) (decide selectorB))
                      (pair candidateA candidateB)
                      (pair targetA targetB)))
          (λ candidateA →
            value (pair candidateA targetB)
              * kronecker (decide selectorA) candidateA targetA)
          innerExact)
        (selectorExact selectorA
          (λ candidateA → value (pair candidateA targetB))
          targetA))

lieCoordinateSelectorExact :
  ∀ (value : Physical.LieCoordinate3 → ℚ) target →
  Sums.sumRational Physical.lieCoordinates3
    (λ candidate →
      value candidate
        * kronecker Calibration.lieCoordinateDecidableEquality
            candidate target)
  ≡ value target
lieCoordinateSelectorExact value Physical.coordinateX = ℚRing.solve []
lieCoordinateSelectorExact value Physical.coordinateY = ℚRing.solve []
lieCoordinateSelectorExact value Physical.coordinateZ = ℚRing.solve []

lieCoordinateFiniteSelector : FiniteSelector Physical.LieCoordinate3
lieCoordinateFiniteSelector = record
  { elements = Physical.lieCoordinates3
  ; decide = Calibration.lieCoordinateDecidableEquality
  ; selectorExact = lieCoordinateSelectorExact
  }

axis4FiniteSelector : FiniteSelector Axis4
axis4FiniteSelector = cyclicFiniteSelector four

site4FiniteSelector : FiniteSelector (Block.PhysicalBlockL Path4.side4)
site4FiniteSelector =
  productFiniteSelector
    (productFiniteSelector axis4FiniteSelector axis4FiniteSelector)
    (productFiniteSelector axis4FiniteSelector axis4FiniteSelector)

bondCellFiniteSelector : FiniteSelector Cell.BondCell4
bondCellFiniteSelector =
  productFiniteSelector axis4FiniteSelector site4FiniteSelector

physicalCoordinateFiniteSelector :
  FiniteSelector Physical.PhysicalSU2Coordinate4
physicalCoordinateFiniteSelector =
  productFiniteSelector
    lieCoordinateFiniteSelector bondCellFiniteSelector

identityEntryIsKronecker : ∀ left right →
  Calibration.identityEntry left right
  ≡ kronecker Calibration.physicalCoordinateDecidableEquality left right
identityEntryIsKronecker left right
  with Calibration.physicalCoordinateDecidableEquality left right
... | yes _ = refl
... | no _ = refl

physicalIdentitySelectorExact :
  ∀ (value : Physical.PhysicalSU2Coordinate4 → ℚ) target →
  Sums.sumRational Physical.physicalSU2Coordinates4
    (λ candidate → value candidate * Calibration.identityEntry candidate target)
  ≡ value target
physicalIdentitySelectorExact value target =
  trans
    (Sums.sumRationalCong
      Physical.physicalSU2Coordinates4
      (λ candidate → value candidate * Calibration.identityEntry candidate target)
      (λ candidate →
        value candidate
          * kronecker Calibration.physicalCoordinateDecidableEquality
              candidate target)
      (λ candidate →
        cong (value candidate *_) (identityEntryIsKronecker candidate target)))
    (selectorExact physicalCoordinateFiniteSelector value target)

------------------------------------------------------------------------
-- Literal basis and coordinate extraction.
------------------------------------------------------------------------

physicalBasis :
  Physical.PhysicalSU2Coordinate4 →
  Physical.PhysicalSU2Coordinate4 → ℚ
physicalBasis target coordinate = Calibration.identityEntry coordinate target

identityEntrySquareExact : ∀ left right →
  FiniteL2.square (Calibration.identityEntry left right)
  ≡ Calibration.identityEntry left right
identityEntrySquareExact left right
  with Calibration.physicalCoordinateDecidableEquality left right
... | yes _ = ℚRing.solve []
... | no _ = ℚRing.solve []

physicalBasisNormSqExact : ∀ target →
  Physical.physicalSU2CoordinateNormSq (physicalBasis target) ≡ 1ℚ
physicalBasisNormSqExact target =
  trans
    (Sums.sumRationalCong
      Physical.physicalSU2Coordinates4
      (λ coordinate → FiniteL2.square (physicalBasis target coordinate))
      (λ coordinate → Calibration.identityEntry coordinate target)
      (λ coordinate → identityEntrySquareExact coordinate target))
    (trans
      (Sums.sumRationalCong
        Physical.physicalSU2Coordinates4
        (λ coordinate → Calibration.identityEntry coordinate target)
        (λ coordinate → 1ℚ * Calibration.identityEntry coordinate target)
        (λ coordinate → ℚRing.solve []))
      (physicalIdentitySelectorExact (λ _ → 1ℚ) target))

physicalBasisDotExact :
  ∀ target vector →
  Physical.physicalCoordinateDot (physicalBasis target) vector
  ≡ vector target
physicalBasisDotExact target vector =
  trans
    (Sums.sumRationalCong
      Physical.physicalSU2Coordinates4
      (λ coordinate →
        Calibration.identityEntry coordinate target * vector coordinate)
      (λ coordinate →
        vector coordinate * Calibration.identityEntry coordinate target)
      (λ coordinate → ℚP.*-comm
        (Calibration.identityEntry coordinate target) (vector coordinate)))
    (physicalIdentitySelectorExact vector target)

physicalMatrixApplyBasisExact :
  ∀ matrix row target →
  Physical.physicalMatrixApply matrix (physicalBasis target) row
  ≡ matrix row target
physicalMatrixApplyBasisExact matrix row target =
  physicalIdentitySelectorExact (matrix row) target

physicalCoordinateSquareBelowNormSq :
  ∀ vector coordinate →
  FiniteL2.square (vector coordinate)
  ≤ Physical.physicalSU2CoordinateNormSq vector
physicalCoordinateSquareBelowNormSq vector coordinate =
  let
    cauchy =
      Cauchy.physicalCoordinateCauchySchwarzSquared
        (physicalBasis coordinate) vector

    lowerExact :
      FiniteL2.square
        (Physical.physicalCoordinateDot (physicalBasis coordinate) vector)
      ≡ FiniteL2.square (vector coordinate)
    lowerExact = cong FiniteL2.square
      (physicalBasisDotExact coordinate vector)

    upperExact :
      Physical.physicalSU2CoordinateNormSq (physicalBasis coordinate)
        * Physical.physicalSU2CoordinateNormSq vector
      ≡ Physical.physicalSU2CoordinateNormSq vector
    upperExact =
      trans
        (cong
          (_* Physical.physicalSU2CoordinateNormSq vector)
          (physicalBasisNormSqExact coordinate))
        (ℚRing.solve-∀ (Physical.physicalSU2CoordinateNormSq vector))
  in
  subst
    (λ lower → lower ≤ Physical.physicalSU2CoordinateNormSq vector)
    lowerExact
    (subst
      (λ upper →
        FiniteL2.square
          (Physical.physicalCoordinateDot
            (physicalBasis coordinate) vector)
        ≤ upper)
      upperExact
      cauchy)

------------------------------------------------------------------------
-- Squared operator norm to literal matrix entry.
------------------------------------------------------------------------

physicalMatrixEntrySquaredFromOperatorBound :
  ∀ matrix bound row column →
  (∀ vector →
    Physical.physicalSU2CoordinateNormSq
      (Physical.physicalMatrixApply matrix vector)
    ≤ bound * Physical.physicalSU2CoordinateNormSq vector) →
  FiniteL2.square (matrix row column) ≤ bound
physicalMatrixEntrySquaredFromOperatorBound
    matrix bound row column operatorBound =
  let
    coordinateBound :
      FiniteL2.square
        (Physical.physicalMatrixApply matrix (physicalBasis column) row)
      ≤ Physical.physicalSU2CoordinateNormSq
          (Physical.physicalMatrixApply matrix (physicalBasis column))
    coordinateBound =
      physicalCoordinateSquareBelowNormSq
        (Physical.physicalMatrixApply matrix (physicalBasis column)) row

    outputBound :
      Physical.physicalSU2CoordinateNormSq
        (Physical.physicalMatrixApply matrix (physicalBasis column))
      ≤ bound
    outputBound =
      subst
        (λ upper →
          Physical.physicalSU2CoordinateNormSq
            (Physical.physicalMatrixApply matrix (physicalBasis column))
          ≤ upper)
        (trans
          (cong (bound *_) (physicalBasisNormSqExact column))
          (ℚRing.solve-∀ bound))
        (operatorBound (physicalBasis column))

    entryApplication :
      FiniteL2.square
        (Physical.physicalMatrixApply matrix (physicalBasis column) row)
      ≡ FiniteL2.square (matrix row column)
    entryApplication =
      cong FiniteL2.square
        (physicalMatrixApplyBasisExact matrix row column)
  in
  subst
    (λ lower → lower ≤ bound)
    entryApplication
    (ℚP.≤-trans coordinateBound outputBound)

sixtyFour sixtyFourSquared : ℚ
sixtyFour = + 64 / 1
sixtyFourSquared = + 4096 / 1

sixtyFourSquareExact :
  sixtyFourSquared ≡ sixtyFour * sixtyFour
sixtyFourSquareExact = ℚRing.solve []

squareBound4096ImpliesAbsoluteBound64 : ∀ value →
  FiniteL2.square value ≤ sixtyFourSquared →
  ∣ value ∣ ≤ sixtyFour
squareBound4096ImpliesAbsoluteBound64 value squareBound
  with ℚP.≤-total ∣ value ∣ sixtyFour
... | inj₁ alreadyBelow = alreadyBelow
... | inj₂ sixtyFourBelow =
  let
    sixtyFourNonnegative : 0ℚ ≤ sixtyFour
    sixtyFourNonnegative = ℚP.nonNegative⁻¹ sixtyFour

    instance
      sixtyFourNN : NonNegative sixtyFour
      sixtyFourNN = ℚ.nonNegative sixtyFourNonnegative

    absoluteSquareBound :
      FiniteL2.square ∣ value ∣ ≤ sixtyFour * sixtyFour
    absoluteSquareBound =
      subst
        (λ lower → lower ≤ sixtyFour * sixtyFour)
        (sym (Schur.absoluteSquareExact value))
        (subst
          (λ upper → FiniteL2.square value ≤ upper)
          sixtyFourSquareExact
          squareBound)

    lowerProduct :
      sixtyFour * sixtyFour ≤ sixtyFour * ∣ value ∣
    lowerProduct =
      ℚP.*-monoˡ-≤-nonNeg sixtyFour sixtyFourBelow

    absoluteSquareBelowMixed :
      ∣ value ∣ * ∣ value ∣ ≤ ∣ value ∣ * sixtyFour
    absoluteSquareBelowMixed =
      subst
        (λ upper →
          ∣ value ∣ * ∣ value ∣ ≤ upper)
        (ℚP.*-comm sixtyFour ∣ value ∣)
        (ℚP.≤-trans absoluteSquareBound lowerProduct)

    sixtyFourPositive : 0ℚ < sixtyFour
    sixtyFourPositive = ℚP.positive⁻¹ sixtyFour

    absolutePositive : 0ℚ < ∣ value ∣
    absolutePositive =
      ℚP.<-≤-trans sixtyFourPositive sixtyFourBelow

    instance
      absolutePositiveInstance : Positive ∣ value ∣
      absolutePositiveInstance = ℚ.positive absolutePositive
  in
  ℚP.*-cancelˡ-≤-pos ∣ value ∣ absoluteSquareBelowMixed

p33PhysicalEntryAbsoluteBoundFromSquaredOperator :
  ∀ matrix row column →
  (∀ vector →
    Physical.physicalSU2CoordinateNormSq
      (Physical.physicalMatrixApply matrix vector)
    ≤ Squared.p33SquaredInverseScale
        * Physical.physicalSU2CoordinateNormSq vector) →
  ∣ matrix row column ∣ ≤ sixtyFour
p33PhysicalEntryAbsoluteBoundFromSquaredOperator
    matrix row column operatorBound =
  squareBound4096ImpliesAbsoluteBound64
    (matrix row column)
    (physicalMatrixEntrySquaredFromOperatorBound
      matrix Squared.p33SquaredInverseScale
      row column operatorBound)

physicalCoordinateSelectorLevel : ProofLevel
physicalCoordinateSelectorLevel = machineChecked

physicalCoordinateBasisNormLevel : ProofLevel
physicalCoordinateBasisNormLevel = machineChecked

physicalMatrixColumnExtractionLevel : ProofLevel
physicalMatrixColumnExtractionLevel = machineChecked

physicalNormToEntrySquaredLevel : ProofLevel
physicalNormToEntrySquaredLevel = machineChecked

physicalNormToEntrySixtyFourLevel : ProofLevel
physicalNormToEntrySixtyFourLevel = machineChecked
