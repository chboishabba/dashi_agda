module DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Bałaban's background-field variational theorem.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 605--636.
-- DOI: 10.1007/BF01229381.
--
-- Theorem 1 proves, under the displayed small-field assumptions, existence and
-- uniqueness of the constrained action minimizer, the quantitative fine-bond
-- estimate
--
--   |U_1(b)-1| <= 2 B_3 d L^{2j} e_k,
--
-- and analyticity of the background field in the coarse variables. The record
-- below preserves this theorem profile without identifying it prematurely with
-- DASHI's selected finite action or norm convention.
------------------------------------------------------------------------

record BackgroundFieldVariationalTheorem
    (CoarseField FineField Bond Bound : Set) : Set₁ where
  field
    add multiply power : Bound → Bound → Bound
    LessEqual StrictlyLess : Bound → Bound → Set

    zero one two : Bound
    dimension blockSide scaleDepth B3 epsilon0 epsilon1 runningSmallness : Bound

    CoarseSmallField : CoarseField → Set
    FineConstraint : CoarseField → FineField → Set
    FineRegularGauge : FineField → Set

    action : FineField → Bound
    bondValue : FineField → Bond → Bound
    identityBondValue : Bound
    bondDeviation : Bound → Bound → Bound

    background : (coarse : CoarseField) →
      CoarseSmallField coarse → FineField

    backgroundSatisfiesConstraint : ∀ coarse small →
      FineConstraint coarse (background coarse small)

    backgroundInRegularGauge : ∀ coarse small →
      FineRegularGauge (background coarse small)

    backgroundMinimizesAction : ∀ coarse small competitor →
      FineConstraint coarse competitor →
      FineRegularGauge competitor →
      LessEqual
        (action (background coarse small))
        (action competitor)

    backgroundUnique : ∀ coarse small competitor →
      FineConstraint coarse competitor →
      FineRegularGauge competitor →
      action competitor ≡ action (background coarse small) →
      competitor ≡ background coarse small

    fineBondSmallness : ∀ coarse small bond →
      LessEqual
        (bondDeviation
          (bondValue (background coarse small) bond)
          identityBondValue)
        (multiply two
          (multiply B3
            (multiply dimension
              (multiply (power blockSide (multiply two scaleDepth))
                runningSmallness))))

    AnalyticInCoarseField :
      ((coarse : CoarseField) → CoarseSmallField coarse → FineField) → Set

    backgroundAnalytic : AnalyticInCoarseField background

    sourceSmallnessHypothesis :
      StrictlyLess runningSmallness epsilon1

open BackgroundFieldVariationalTheorem public

balabanBackgroundFieldExistenceUniquenessLevel : ProofLevel
balabanBackgroundFieldExistenceUniquenessLevel = standardImported

balabanBackgroundFieldFineBondEstimateLevel : ProofLevel
balabanBackgroundFieldFineBondEstimateLevel = standardImported

balabanBackgroundFieldAnalyticityLevel : ProofLevel
balabanBackgroundFieldAnalyticityLevel = standardImported

physicalBackgroundActionConstraintIdentificationInputsLevel : ProofLevel
physicalBackgroundActionConstraintIdentificationInputsLevel = conditional

physicalBackgroundNormConventionInputsLevel : ProofLevel
physicalBackgroundNormConventionInputsLevel = conditional
