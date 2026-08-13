module DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Isolate and prove the finite telescope used by G1 in exactly Bałaban's
-- matrix operator norm.  For unitary factors U_j,
--
--   U_1...U_n - I
--     = U_1...(U_n-I) + ... + (U_1-I),
--
-- and unitary left multiplication preserves operator norm.  Consequently
--
--   |U_1...U_n-I|_op <= sum_j |U_j-I|_op.
--
-- The analytic operator-norm facts are standard imported matrix analysis; the
-- finite-list induction and all scalar budget consequences are machine checked.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

record UnitaryOperatorDefectKernel (Unitary : Set) : Set₁ where
  field
    identity : Unitary
    multiply : Unitary → Unitary → Unitary
    defect : Unitary → ℚ

    defectNonnegative : ∀ value → 0ℚ ≤ defect value
    identityDefectZero : defect identity ≡ 0ℚ

    -- Standard operator-norm consequence of
    -- ||UV-I|| = ||U(V-I)+(U-I)|| <= ||V-I||+||U-I||.
    productDefectTriangle : ∀ left right →
      defect (multiply left right) ≤ defect left + defect right

open UnitaryOperatorDefectKernel public

productList :
  ∀ {Unitary : Set} →
  UnitaryOperatorDefectKernel Unitary → List Unitary → Unitary
productList kernel [] = identity kernel
productList kernel (value ∷ values) =
  multiply kernel value (productList kernel values)

defectSum :
  ∀ {Unitary : Set} →
  UnitaryOperatorDefectKernel Unitary → List Unitary → ℚ
defectSum kernel values =
  Sums.sumRational values (defect kernel)

productDefectBelowSum :
  ∀ {Unitary : Set}
    (kernel : UnitaryOperatorDefectKernel Unitary)
    (values : List Unitary) →
  defect kernel (productList kernel values) ≤ defectSum kernel values
productDefectBelowSum kernel [] =
  subst
    (λ lower → lower ≤ 0ℚ)
    (sym (identityDefectZero kernel))
    ℚP.≤-refl
productDefectBelowSum kernel (value ∷ values) =
  ℚP.≤-trans
    (productDefectTriangle kernel value (productList kernel values))
    (ℚP.+-mono-≤
      ℚP.≤-refl
      (productDefectBelowSum kernel values))

record PointwiseDefectMajorant
    {Unitary : Set}
    (kernel : UnitaryOperatorDefectKernel Unitary)
    (values : List Unitary)
    (majorant : Unitary → ℚ) : Set where
  field
    pointwise : ∀ value → defect kernel value ≤ majorant value

open PointwiseDefectMajorant public

sumDefectBelowMajorant :
  ∀ {Unitary : Set}
    (kernel : UnitaryOperatorDefectKernel Unitary)
    (values : List Unitary)
    (majorant : Unitary → ℚ) →
  PointwiseDefectMajorant kernel values majorant →
  defectSum kernel values ≤ Sums.sumRational values majorant
sumDefectBelowMajorant kernel [] majorant bounds = ℚP.≤-refl
sumDefectBelowMajorant kernel (value ∷ values) majorant bounds =
  ℚP.+-mono-≤
    (pointwise bounds value)
    (sumDefectBelowMajorant kernel values majorant bounds)

productDefectBelowMajorantSum :
  ∀ {Unitary : Set}
    (kernel : UnitaryOperatorDefectKernel Unitary)
    (values : List Unitary)
    (majorant : Unitary → ℚ) →
  PointwiseDefectMajorant kernel values majorant →
  defect kernel (productList kernel values)
  ≤ Sums.sumRational values majorant
productDefectBelowMajorantSum kernel values majorant bounds =
  ℚP.≤-trans
    (productDefectBelowSum kernel values)
    (sumDefectBelowMajorant kernel values majorant bounds)

cmp98FiniteUnitaryDefectTelescopeLevel : ProofLevel
cmp98FiniteUnitaryDefectTelescopeLevel = machineChecked

-- The operator-norm triangle/submultiplicativity/unitary-isometry theorem is
-- standard imported matrix analysis.  The repository-specific remaining task
-- is only to identify the literal rational SU(2) links with this kernel.
cmp98UnitaryOperatorNormKernelLevel : ProofLevel
cmp98UnitaryOperatorNormKernelLevel = standardImported
