module DASHI.Physics.YangMills.BalabanCompactSimpleHaarQuadraticCasimirExact where

------------------------------------------------------------------------
-- ROUND83: HAAR / EXPONENTIAL-MAP JACOBIAN QUADRATIC TERM = C_A / 24
--
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction",
-- second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Anthony W. Knapp,
-- "Lie Groups Beyond an Introduction", second edition, Birkhauser, 2002.
-- DOI: 10.1007/978-1-4757-2453-0.
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- STANDARD FINITE-DIMENSIONAL LIE/MATRIX ANALYSIS
--
-- In exponential coordinates on a compact Lie group,
--
--   J_exp(X) = det((1-exp(-ad_X))/ad_X).
--
-- Since tr(ad_X)=0 in the compact semisimple case, the determinant may be
-- written using the even factor sinh(ad_X/2)/(ad_X/2).  The scalar series
--
--   log(sinh z / z) = z^2/6 + O(z^4)
--
-- therefore gives
--
--   log J_exp(gX) = (g^2/24) tr(ad_X^2) + O(g^4),
--
-- and hence the measure contribution to the effective action is
--
--   -log J_exp(gX)
--      = -(g^2/24) tr(ad_X^2) + O(g^4).
--
-- In the long-root-squared-two / SU(2):C_A=2 convention,
--
--   -tr(ad_X^2) = C_A ||X||^2.
--
-- DASHI CONTRIBUTION
--
-- The exact rational coefficient algebra below proves that the quadratic
-- effective-action coefficient is
--
--        (C_A / 24) ||X||^2.
--
-- Thus the Haar sector of the all-compact-simple one-loop calculation does not
-- require separate exceptional-group diagrams.  The only physical seam is the
-- SAME-OBJECT identification of Bałaban's literal source coordinate/Jacobian
-- with this exponential-coordinate normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _-_; _*_; _/_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactSimpleClassificationAdjointCasimirExact as Class

twentyFour : ℚ
twentyFour = + 24 / 1

oneTwentyFourth : ℚ
oneTwentyFourth = + 1 / 24

record AdjointTraceCasimirData : Set₁ where
  field
    adjointCasimir : ℚ
    normSquared : ℚ
    traceAdSquared : ℚ

    adjointCasimirNonnegative : 0ℚ ≤ adjointCasimir
    normSquaredNonnegative : 0ℚ ≤ normSquared

    -- Compact real form convention: ad_X is skew-adjoint, so its quadratic
    -- trace is nonpositive and the positive Casimir identity reads
    --     -Tr(ad_X^2) = C_A ||X||^2.
    traceCasimirIdentity :
      0ℚ - traceAdSquared ≡ adjointCasimir * normSquared

open AdjointTraceCasimirData public

haarEffectiveActionQuadraticCoefficient : AdjointTraceCasimirData → ℚ
haarEffectiveActionQuadraticCoefficient dataSet =
  oneTwentyFourth * (0ℚ - traceAdSquared dataSet)

haarQuadraticCoefficientIsCasimirOverTwentyFour :
  (dataSet : AdjointTraceCasimirData) →
  haarEffectiveActionQuadraticCoefficient dataSet
  ≡ (adjointCasimir dataSet * oneTwentyFourth) * normSquared dataSet
haarQuadraticCoefficientIsCasimirOverTwentyFour dataSet =
  trans
    (cong (oneTwentyFourth *_) (traceCasimirIdentity dataSet))
    (ℚRing.solve-∀
      (adjointCasimir dataSet) (normSquared dataSet) oneTwentyFourth)

haarQuadraticCoefficientNonnegative :
  (dataSet : AdjointTraceCasimirData) →
  0ℚ ≤ haarEffectiveActionQuadraticCoefficient dataSet
haarQuadraticCoefficientNonnegative dataSet =
  subst
    (λ coefficient → 0ℚ ≤ coefficient)
    (sym (haarQuadraticCoefficientIsCasimirOverTwentyFour dataSet))
    (let
      oneTwentyFourthNonnegative : 0ℚ ≤ oneTwentyFourth
      oneTwentyFourthNonnegative = ℚP.nonNegative⁻¹ oneTwentyFourth
      casimirTimesNormNonnegative :
        0ℚ ≤ adjointCasimir dataSet * normSquared dataSet
      casimirTimesNormNonnegative =
        ℚP.*-mono-≤
          ℚP.≤-refl (adjointCasimirNonnegative dataSet)
          ℚP.≤-refl (normSquaredNonnegative dataSet)
     in
      ℚP.*-mono-≤
        ℚP.≤-refl casimirTimesNormNonnegative
        ℚP.≤-refl oneTwentyFourthNonnegative)

record ClassifiedHaarQuadraticData : Set₁ where
  field
    lieType : Class.Class.SimpleLieType
    normSquared : ℚ
    traceAdSquared : ℚ
    normSquaredNonnegative : 0ℚ ≤ normSquared
    traceCasimirIdentity :
      0ℚ - traceAdSquared
      ≡ Class.classificationAdjointCasimir lieType * normSquared

open ClassifiedHaarQuadraticData public

classifiedAdjointTraceData : ClassifiedHaarQuadraticData → AdjointTraceCasimirData
classifiedAdjointTraceData dataSet = record
  { AdjointTraceCasimirData.adjointCasimir =
      Class.classificationAdjointCasimir (lieType dataSet)
  ; AdjointTraceCasimirData.normSquared = normSquared dataSet
  ; AdjointTraceCasimirData.traceAdSquared = traceAdSquared dataSet
  ; AdjointTraceCasimirData.adjointCasimirNonnegative =
      ℚP.<⇒≤ (Class.classificationAdjointCasimirPositive (lieType dataSet))
  ; AdjointTraceCasimirData.normSquaredNonnegative = normSquaredNonnegative dataSet
  ; AdjointTraceCasimirData.traceCasimirIdentity = traceCasimirIdentity dataSet
  }

classifiedHaarQuadraticCoefficient : ClassifiedHaarQuadraticData → ℚ
classifiedHaarQuadraticCoefficient dataSet =
  haarEffectiveActionQuadraticCoefficient (classifiedAdjointTraceData dataSet)

classifiedHaarQuadraticCoefficientExact :
  (dataSet : ClassifiedHaarQuadraticData) →
  classifiedHaarQuadraticCoefficient dataSet
  ≡ (Class.classificationAdjointCasimir (lieType dataSet) * oneTwentyFourth)
      * normSquared dataSet
classifiedHaarQuadraticCoefficientExact dataSet =
  haarQuadraticCoefficientIsCasimirOverTwentyFour
    (classifiedAdjointTraceData dataSet)

exponentialMapHaarJacobianFormulaLevel : ProofLevel
exponentialMapHaarJacobianFormulaLevel = standardImported

logDexpQuadraticTaylorCoefficientLevel : ProofLevel
logDexpQuadraticTaylorCoefficientLevel = standardImported

compactSemisimpleAdjointTraceCasimirIdentityLevel : ProofLevel
compactSemisimpleAdjointTraceCasimirIdentityLevel = standardImported

classifiedHaarQuadraticCoefficientLevel : ProofLevel
classifiedHaarQuadraticCoefficientLevel = machineChecked

-- Literal physical seam: prove that the Haar/Jacobian factor in the SAME
-- Bałaban finite-cutoff change of variables uses this exponential coordinate and
-- normalization.  Once that is identified, its quadratic coefficient is fixed.
physicalBalabanHaarCoordinateNormalizationLevel : ProofLevel
physicalBalabanHaarCoordinateNormalizationLevel = conditional
