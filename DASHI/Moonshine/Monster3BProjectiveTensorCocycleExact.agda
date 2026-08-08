module DASHI.Moonshine.Monster3BProjectiveTensorCocycleExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Gregory Karpilovsky,
-- "Projective Representations of Finite Groups",
-- Marcel Dekker, 1985.
-- ISBN: 978-0-8247-7313-7; no DOI assigned.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact algebra needed for the 3B inertia action.  A projective
-- action on the Heisenberg factor and the inverse-projective action on the
-- multiplicity factor descend to a genuine action on balanced pure tensors.
-- The proof does not assume a particular normalizer or manufacture a cocycle;
-- it states the precise cancellation law that actual generator data must
-- inhabit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

record CompensatingProjectiveTensor : Set₁ where
  field
    GroupElement : Set
    HeisenbergCarrier : Set
    MultiplicityCarrier : Set
    TensorCarrier : Set
    Phase : Set

    composeGroup : GroupElement → GroupElement → GroupElement
    phaseDefect : GroupElement → GroupElement → Phase

    actHeisenberg : GroupElement → HeisenbergCarrier → HeisenbergCarrier
    actMultiplicity : GroupElement → MultiplicityCarrier → MultiplicityCarrier

    scaleHeisenberg : Phase → HeisenbergCarrier → HeisenbergCarrier
    inverseScaleMultiplicity :
      Phase → MultiplicityCarrier → MultiplicityCarrier

    pureTensor :
      HeisenbergCarrier → MultiplicityCarrier → TensorCarrier

    heisenbergProjectiveComposition :
      (g h : GroupElement) →
      (x : HeisenbergCarrier) →
      actHeisenberg g (actHeisenberg h x)
      ≡ scaleHeisenberg
          (phaseDefect g h)
          (actHeisenberg (composeGroup g h) x)

    multiplicityCompensatingComposition :
      (g h : GroupElement) →
      (s : MultiplicityCarrier) →
      actMultiplicity g (actMultiplicity h s)
      ≡ inverseScaleMultiplicity
          (phaseDefect g h)
          (actMultiplicity (composeGroup g h) s)

    balancedTensorCancellation :
      (phase : Phase) →
      (x : HeisenbergCarrier) →
      (s : MultiplicityCarrier) →
      pureTensor
        (scaleHeisenberg phase x)
        (inverseScaleMultiplicity phase s)
      ≡ pureTensor x s

open CompensatingProjectiveTensor public

pureTensorAction :
  (data : CompensatingProjectiveTensor) →
  GroupElement data →
  HeisenbergCarrier data →
  MultiplicityCarrier data →
  TensorCarrier data
pureTensorAction data g x s =
  pureTensor data
    (actHeisenberg data g x)
    (actMultiplicity data g s)

-- This is the load-bearing cocycle theorem.  It is exactly the reason the
-- tensor product may carry a genuine inertia-group action although its two
-- factors separately carry opposite projective multipliers.
tensorCocycleCancels :
  (data : CompensatingProjectiveTensor) →
  (g h : GroupElement data) →
  (x : HeisenbergCarrier data) →
  (s : MultiplicityCarrier data) →
  pureTensor data
    (actHeisenberg data g (actHeisenberg data h x))
    (actMultiplicity data g (actMultiplicity data h s))
  ≡ pureTensorAction data (composeGroup data g h) x s
tensorCocycleCancels data g h x s
  rewrite heisenbergProjectiveComposition data g h x
        | multiplicityCompensatingComposition data g h s =
  balancedTensorCancellation data
    (phaseDefect data g h)
    (actHeisenberg data (composeGroup data g h) x)
    (actMultiplicity data (composeGroup data g h) s)

record GenuineTensorActionCertificate
  (data : CompensatingProjectiveTensor) : Set₁ where
  constructor genuine-tensor-action-certificate
  field
    compositionOnPureTensors :
      (g h : GroupElement data) →
      (x : HeisenbergCarrier data) →
      (s : MultiplicityCarrier data) →
      pureTensor data
        (actHeisenberg data g (actHeisenberg data h x))
        (actMultiplicity data g (actMultiplicity data h s))
      ≡ pureTensorAction data (composeGroup data g h) x s

open GenuineTensorActionCertificate public

actualTensorNormalizerAction :
  (data : CompensatingProjectiveTensor) →
  GenuineTensorActionCertificate data
actualTensorNormalizerAction data =
  genuine-tensor-action-certificate (tensorCocycleCancels data)
