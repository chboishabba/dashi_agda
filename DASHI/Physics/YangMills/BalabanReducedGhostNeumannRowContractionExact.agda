module DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Reduce the analytic Neumann/logarithm convergence seam for the explicit
-- reduced ghost matrix R to one source-native contraction estimate.
--
-- On the repository's literal finite rational matrix carrier we prove
--
--   rowMass(A B) <= rowMassBound(A) rowMassBound(B)
--
-- and hence, if every row of R has absolute mass <= q,
--
--   rowMass(R^(n+1)) <= q^(n+1).
--
-- We additionally prove that multiplying a power by any nonnegative scalar
-- coefficient c <= 1 (in particular the 1/n coefficients of the matrix-log
-- series) cannot enlarge this geometric majorant.
--
-- Thus the remaining physical input to the standard finite-dimensional
-- Neumann/matrix-log argument is precisely a strict selected-ball bound q < 1
-- for the SAME R(g)=M_A M0^{-1}-I already constructed in Round61.  No
-- spectral-radius receipt or abstract matrix norm is substituted for that
-- physical estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix

rowMass : ∀ {Index : Set} → List Index → Matrix.Matrix Index → Index → ℚ
rowMass = Schur.absoluteRowMass

UniformRowBound : ∀ {Index : Set} → List Index → Matrix.Matrix Index → ℚ → Set
UniformRowBound indices matrix bound = ∀ row → rowMass indices matrix row ≤ bound

------------------------------------------------------------------------
-- Absolute row mass is submultiplicative on the exact finite matrix product.
------------------------------------------------------------------------

productEntryAbsoluteUpper :
  ∀ {Index : Set} (indices : List Index)
    (left right : Matrix.Matrix Index) row column →
  ∣ Matrix.matrixProduct indices left right row column ∣
  ≤ Sums.sumRational indices
      (λ middle → ∣ left row middle ∣ * ∣ right middle column ∣)
productEntryAbsoluteUpper indices left right row column =
  let
    triangle = Schur.sumAbsoluteTriangle indices
      (λ middle → left row middle * right middle column)
    productsExact = Sums.sumRationalCong indices _ _
      (λ middle → ℚP.∣p*q∣≡∣p∣*∣q∣
        (left row middle) (right middle column))
  in
  subst
    (λ upper →
      ∣ Matrix.matrixProduct indices left right row column ∣ ≤ upper)
    productsExact triangle

productRowMassFubiniUpper :
  ∀ {Index : Set} (indices : List Index)
    (left right : Matrix.Matrix Index) row →
  rowMass indices (Matrix.matrixProduct indices left right) row
  ≤ Sums.sumRational indices
      (λ middle → ∣ left row middle ∣ * rowMass indices right middle)
productRowMassFubiniUpper indices left right row =
  let
    pointwise = Schur.sumPointwiseBelow indices
      (λ column → ∣ Matrix.matrixProduct indices left right row column ∣)
      (λ column → Sums.sumRational indices
        (λ middle → ∣ left row middle ∣ * ∣ right middle column ∣))
      (productEntryAbsoluteUpper indices left right row)

    swapped = Fubini.sumSwap indices indices
      (λ column middle → ∣ left row middle ∣ * ∣ right middle column ∣)

    scaled = Sums.sumRationalCong indices _ _
      (λ middle →
        sym (Fibre.sumRationalScale
          ∣ left row middle ∣ indices
          (λ column → ∣ right middle column ∣)))
  in
  subst
    (λ upper → rowMass indices (Matrix.matrixProduct indices left right) row ≤ upper)
    (trans swapped scaled)
    pointwise

productRowMassBound :
  ∀ {Index : Set} (indices : List Index)
    (left right : Matrix.Matrix Index) leftBound rightBound →
  0ℚ ≤ rightBound →
  UniformRowBound indices left leftBound →
  UniformRowBound indices right rightBound →
  UniformRowBound indices (Matrix.matrixProduct indices left right)
    (leftBound * rightBound)
productRowMassBound indices left right leftBound rightBound
    rightBoundNonnegative leftRows rightRows row =
  let
    pointwise :
      Sums.sumRational indices
        (λ middle → ∣ left row middle ∣ * rowMass indices right middle)
      ≤ Sums.sumRational indices
        (λ middle → ∣ left row middle ∣ * rightBound)
    pointwise = Schur.sumPointwiseBelow indices _ _
      (λ middle →
        let
          instance
            entryNN : NonNegative ∣ left row middle ∣
            entryNN = ℚP.∣-∣-nonNeg (left row middle)
        in
        ℚP.*-monoˡ-≤-nonNeg ∣ left row middle ∣ (rightRows middle))

    scaleExact :
      Sums.sumRational indices
        (λ middle → ∣ left row middle ∣ * rightBound)
      ≡ rowMass indices left row * rightBound
    scaleExact = Fibre.sumRationalScaleRight rightBound indices
      (λ middle → ∣ left row middle ∣)

    scaledLeft : rowMass indices left row * rightBound ≤ leftBound * rightBound
    scaledLeft =
      let
        instance
          rightNN : NonNegative rightBound
          rightNN = ℚ.nonNegative rightBoundNonnegative
      in
      ℚP.*-monoʳ-≤-nonNeg rightBound (leftRows row)
  in
  ℚP.≤-trans
    (productRowMassFubiniUpper indices left right row)
    (ℚP.≤-trans pointwise
      (subst
        (λ lower → lower ≤ leftBound * rightBound)
        (sym scaleExact)
        scaledLeft))

------------------------------------------------------------------------
-- Positive powers inherit the geometric q^(n+1) row bound.
------------------------------------------------------------------------

rationalPower : ℚ → Nat → ℚ
rationalPower ratio zero = 1ℚ
rationalPower ratio (suc exponent) = ratio * rationalPower ratio exponent

positiveMatrixPower :
  ∀ {Index : Set} → List Index → Matrix.Matrix Index → Nat → Matrix.Matrix Index
positiveMatrixPower indices matrix zero = matrix
positiveMatrixPower indices matrix (suc exponent) =
  Matrix.matrixProduct indices matrix (positiveMatrixPower indices matrix exponent)

powerNonnegative : ∀ q exponent → 0ℚ ≤ q → 0ℚ ≤ rationalPower q exponent
powerNonnegative q zero qNonnegative = ℚP.nonNegative⁻¹ 1ℚ
powerNonnegative q (suc exponent) qNonnegative =
  let
    instance
      qNN : NonNegative q
      qNN = ℚ.nonNegative qNonnegative
      powerNN : NonNegative (rationalPower q exponent)
      powerNN = ℚ.nonNegative (powerNonnegative q exponent qNonnegative)
  in
  ℚP.nonNegative⁻¹ (q * rationalPower q exponent)

positivePowerRowBound :
  ∀ {Index : Set} (indices : List Index)
    (matrix : Matrix.Matrix Index) q exponent →
  0ℚ ≤ q →
  UniformRowBound indices matrix q →
  UniformRowBound indices (positiveMatrixPower indices matrix exponent)
    (rationalPower q (suc exponent))
positivePowerRowBound indices matrix q zero qNonnegative matrixRows = matrixRows
positivePowerRowBound indices matrix q (suc exponent) qNonnegative matrixRows =
  productRowMassBound
    indices matrix (positiveMatrixPower indices matrix exponent)
    q (rationalPower q (suc exponent))
    (powerNonnegative q (suc exponent) qNonnegative)
    matrixRows
    (positivePowerRowBound indices matrix q exponent qNonnegative matrixRows)

------------------------------------------------------------------------
-- Log-series coefficients 0 <= c <= 1 preserve the power majorant.
------------------------------------------------------------------------

scaleMatrix : ∀ {Index : Set} → ℚ → Matrix.Matrix Index → Matrix.Matrix Index
scaleMatrix scalar matrix row column = scalar * matrix row column

scaledRowMassExact :
  ∀ {Index : Set} (indices : List Index)
    scalar (matrix : Matrix.Matrix Index) row →
  0ℚ ≤ scalar →
  rowMass indices (scaleMatrix scalar matrix) row
  ≡ scalar * rowMass indices matrix row
scaledRowMassExact indices scalar matrix row scalarNonnegative =
  let
    scalarAbs : ∣ scalar ∣ ≡ scalar
    scalarAbs = ℚP.0≤p⇒∣p∣≡p scalarNonnegative

    entryExact = Sums.sumRationalCong indices _ _
      (λ column →
        trans
          (ℚP.∣p*q∣≡∣p∣*∣q∣ scalar (matrix row column))
          (cong (_* ∣ matrix row column ∣) scalarAbs))
  in
  trans entryExact
    (Sums.sumRationalScale scalar indices
      (λ column → ∣ matrix row column ∣))

unitCoefficientPreservesRowBound :
  ∀ {Index : Set} (indices : List Index)
    scalar (matrix : Matrix.Matrix Index) bound →
  0ℚ ≤ scalar → scalar ≤ 1ℚ →
  0ℚ ≤ bound →
  UniformRowBound indices matrix bound →
  UniformRowBound indices (scaleMatrix scalar matrix) bound
unitCoefficientPreservesRowBound
    indices scalar matrix bound scalarNonnegative scalarBelowOne
    boundNonnegative matrixRows row =
  let
    first : scalar * rowMass indices matrix row ≤ scalar * bound
    first =
      let
        instance scalarNN : NonNegative scalar
        scalarNN = ℚ.nonNegative scalarNonnegative
      in ℚP.*-monoˡ-≤-nonNeg scalar (matrixRows row)

    second : scalar * bound ≤ 1ℚ * bound
    second =
      let
        instance boundNN : NonNegative bound
        boundNN = ℚ.nonNegative boundNonnegative
      in ℚP.*-monoʳ-≤-nonNeg bound scalarBelowOne
  in
  subst
    (λ lower → lower ≤ bound)
    (sym (scaledRowMassExact indices scalar matrix row scalarNonnegative))
    (ℚP.≤-trans first
      (subst (λ upper → scalar * bound ≤ upper)
        (ℚP.*-identityˡ bound) second))

logCoefficientPowerRowBound :
  ∀ {Index : Set} (indices : List Index)
    (matrix : Matrix.Matrix Index) q exponent coefficient →
  0ℚ ≤ q →
  UniformRowBound indices matrix q →
  0ℚ ≤ coefficient → coefficient ≤ 1ℚ →
  UniformRowBound indices
    (scaleMatrix coefficient (positiveMatrixPower indices matrix exponent))
    (rationalPower q (suc exponent))
logCoefficientPowerRowBound
    indices matrix q exponent coefficient qNonnegative matrixRows
    coefficientNonnegative coefficientBelowOne =
  unitCoefficientPreservesRowBound
    indices coefficient (positiveMatrixPower indices matrix exponent)
    (rationalPower q (suc exponent))
    coefficientNonnegative coefficientBelowOne
    (powerNonnegative q (suc exponent) qNonnegative)
    (positivePowerRowBound indices matrix q exponent qNonnegative matrixRows)

reducedGhostMatrixProductRowSubmultiplicativityLevel : ProofLevel
reducedGhostMatrixProductRowSubmultiplicativityLevel = machineChecked

reducedGhostPositivePowerGeometricMajorantLevel : ProofLevel
reducedGhostPositivePowerGeometricMajorantLevel = machineChecked

reducedGhostLogCoefficientGeometricMajorantLevel : ProofLevel
reducedGhostLogCoefficientGeometricMajorantLevel = machineChecked

-- The remaining physical convergence input is now a bound q < 1 on the
-- actual reduced perturbation matrix R(g).  The repository already carries
-- Bishop absolute-series/comparison machinery; once this same-object q-bound
-- is established, the analytic log series can be discharged by comparison to
-- the geometric majorant proved here.
physicalReducedGhostStrictRowContractionLevel : ProofLevel
physicalReducedGhostStrictRowContractionLevel = conditional
