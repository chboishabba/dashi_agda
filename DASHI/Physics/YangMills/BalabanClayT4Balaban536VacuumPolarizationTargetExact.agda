module DASHI.Physics.YangMills.BalabanClayT4Balaban536VacuumPolarizationTargetExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary-source normalization.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
--
-- Exact comparison points:
--   Eq. (5.36): Laurent-variable transverse representation of f_{mu nu}(z).
--   Eq. (5.37): momentum representation
--     H_{mu nu}(p) = beta(delta_{mu nu} Delta(p)
--                         - partial_mu(p) partial_nu(p) + H'_{mu nu}(p)).
--   Eq. (5.38): the remainder is third order in lattice derivatives and has an
--               analytic extension to a uniform complex strip.
--   Eq. (5.41): beta is recovered from the mixed z_1,z_2 derivative of f_12 at
--               z_1=z_2=1.
--
-- This module is a falsification target, not a paper-imported proof.  A DASHI
-- one-loop kernel must construct this record from its literal Wilson, ghost and
-- Haar diagrams before the universal coefficient can be consumed.
------------------------------------------------------------------------

record Balaban536LaurentTarget
    (Direction Laurent Momentum Scalar Tensor Remainder : Set) : Set₂ where
  field
    deltaDirection : Direction → Direction → Scalar
    subtract multiply add negate : Scalar → Scalar → Scalar

    zMinusOne zInverseMinusOne : Laurent → Direction → Scalar
    latticeDerivative conjugateDerivative laplacian : Momentum → Direction → Scalar

    coefficientBeta : Scalar
    f : Direction → Direction → Laurent → Scalar
    H : Direction → Direction → Momentum → Scalar
    HPrime : Direction → Direction → Momentum → Scalar

    -- Exact Eq. (5.36).  The written relevant term is separated from a
    -- higher-derivative Laurent remainder.
    laurentRemainder : Direction → Direction → Laurent → Scalar
    equation536 : ∀ mu nu z →
      f mu nu z
      ≡ add
          (multiply coefficientBeta
            (subtract
              (multiply (deltaDirection mu nu)
                (multiply (zInverseMinusOne z mu) (zMinusOne z nu)))
              (multiply (zInverseMinusOne z nu) (zMinusOne z mu))))
          (laurentRemainder mu nu z)

    -- Exact Eq. (5.37) after z_mu = exp(i p_mu).
    equation537 : ∀ mu nu momentum →
      H mu nu momentum
      ≡ multiply coefficientBeta
          (add
            (subtract
              (multiply (deltaDirection mu nu)
                (laplacian momentum mu))
              (multiply
                (latticeDerivative momentum mu)
                (conjugateDerivative momentum nu)))
            (HPrime mu nu momentum))

    -- Eq. (5.38): H' is at least third order in lattice derivatives and its
    -- coefficient functions are analytic in one uniform complex strip.
    hPrimeThirdDerivativeOrder : ∀ mu nu momentum → Set
    hPrimeHypercubicSymmetric : ∀ mu nu momentum → Set
    hPrimeAnalyticUniformStrip : Set

    -- Eq. (5.41): mixed derivative extraction of beta.
    mixedLaurentDerivative :
      Direction → Direction →
      (Direction → Direction → Laurent → Scalar) → Laurent → Scalar
    identityLaurent : Laurent

    equation541 : ∀ mu nu →
      mixedLaurentDerivative mu nu f identityLaurent ≡ coefficientBeta

open Balaban536LaurentTarget public

record DASHIOneLoopMatchesBalaban536
    (Direction Laurent Momentum Scalar Tensor Remainder : Set) : Set₂ where
  field
    target : Balaban536LaurentTarget
      Direction Laurent Momentum Scalar Tensor Remainder

    dashiOneLoopKernel : Direction → Direction → Momentum → Scalar
    dashiPlaquetteCoefficient : Scalar

    dashiKernelEqualsH : ∀ mu nu momentum →
      dashiOneLoopKernel mu nu momentum ≡ H target mu nu momentum

    dashiCoefficientEqualsMixedDerivative :
      dashiPlaquetteCoefficient
      ≡ mixedLaurentDerivative target
          configuredMu configuredNu (f target) (identityLaurent target)

    configuredMu configuredNu : Direction

open DASHIOneLoopMatchesBalaban536 public

dashiCoefficientMatchesBalabanBeta :
  ∀ {Direction Laurent Momentum Scalar Tensor Remainder}
    (dataSet : DASHIOneLoopMatchesBalaban536
      Direction Laurent Momentum Scalar Tensor Remainder) →
  dashiPlaquetteCoefficient dataSet ≡ coefficientBeta (target dataSet)
dashiCoefficientMatchesBalabanBeta dataSet =
  Relation.Binary.PropositionalEquality.trans
    (dashiCoefficientEqualsMixedDerivative dataSet)
    (equation541 (target dataSet)
      (configuredMu dataSet) (configuredNu dataSet))
  where
  open import Relation.Binary.PropositionalEquality

balaban536LaurentReductionLevel : ProofLevel
balaban536LaurentReductionLevel = machineChecked

balaban537MomentumReductionLevel : ProofLevel
balaban537MomentumReductionLevel = machineChecked

balaban541CoefficientExtractionLevel : ProofLevel
balaban541CoefficientExtractionLevel = machineChecked

literalDiagramToBalabanTargetInputsLevel : ProofLevel
literalDiagramToBalabanTargetInputsLevel = conditional
