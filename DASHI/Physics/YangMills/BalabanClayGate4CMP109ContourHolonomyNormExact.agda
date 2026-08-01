module DASHI.Physics.YangMills.BalabanClayGate4CMP109ContourHolonomyNormExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ContourLengthExact as Length
import DASHI.Physics.YangMills.BalabanClayGate4FiniteHolonomyDerivativeExact as Holonomy
import DASHI.Physics.YangMills.BalabanClayGate4FiniteHolonomyDerivativeNormExact as HolonomyNorm

------------------------------------------------------------------------
-- Physical path-stage estimate for every enumerated CMP109 contour.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press (1983;
-- reissued 2023). DOI: 10.1017/9781009290395.
--
-- Combining the exact contour-word length with Ad-invariance of the compact
-- Lie-algebra norm gives, for every enumerated contour order,
--
--   ||D Hol[A]||
--     <= (sum_mu |delta_mu|) sup_e ||A_e||.
--
-- The path factor in the four-stage CMP109 entry estimate is therefore an
-- explicit coordinate-displacement count rather than an independent analytic
-- constant.
------------------------------------------------------------------------

record CMP109ContourHolonomyNormInputs
    (Group Lie Scalar : Set) : Set₁ where
  field
    displacement : Contours.Displacement4
    order : Agda.Builtin.List.List Contours.AxisSegment
    orderEnumerated :
      Contours._∈_ order
        (Contours.cmp109ShortestContourOrders displacement)

    normData : HolonomyNorm.HolonomyDerivativeNormData
      Word.SignedAxis4 Group Lie Scalar

    fieldMeaning :
      HolonomyNorm.field normData
      ≡ HolonomyNorm.field normData

open CMP109ContourHolonomyNormInputs public

selectedContourWord :
  ∀ {Group Lie Scalar} →
  CMP109ContourHolonomyNormInputs Group Lie Scalar →
  Agda.Builtin.List.List Word.SignedAxis4
selectedContourWord inputs = Periodic.contourWord (order inputs)

selectedContourDerivative :
  ∀ {Group Lie Scalar} →
  CMP109ContourHolonomyNormInputs Group Lie Scalar → Lie
selectedContourDerivative inputs =
  Holonomy.leftTrivializedHolonomyDerivative
    (HolonomyNorm.differential (normData inputs))
    (HolonomyNorm.field (normData inputs))
    (HolonomyNorm.variation (normData inputs))
    (selectedContourWord inputs)

selectedContourDerivativeNormBelowDisplacementLength :
  ∀ {Group Lie Scalar}
    (inputs : CMP109ContourHolonomyNormInputs Group Lie Scalar) →
  HolonomyNorm.LessEqual
    (HolonomyNorm.scalar (normData inputs))
    (HolonomyNorm.norm (normData inputs)
      (selectedContourDerivative inputs))
    (HolonomyNorm.natScale
      (HolonomyNorm.scalar (normData inputs))
      (Length.segmentCountSum
        (Contours.activeSegments (displacement inputs)))
      (HolonomyNorm.variationBound (normData inputs)))
selectedContourDerivativeNormBelowDisplacementLength inputs =
  subst
    (λ count →
      HolonomyNorm.LessEqual
        (HolonomyNorm.scalar (normData inputs))
        (HolonomyNorm.norm (normData inputs)
          (selectedContourDerivative inputs))
        (HolonomyNorm.natScale
          (HolonomyNorm.scalar (normData inputs))
          count
          (HolonomyNorm.variationBound (normData inputs))))
    (Length.enumeratedContourWordLengthExact
      (displacement inputs) (order inputs) (orderEnumerated inputs))
    (HolonomyNorm.finiteHolonomyDerivativeNormBelowPathLength
      (normData inputs) (selectedContourWord inputs))

cmp109ContourHolonomyDisplacementNormLevel : ProofLevel
cmp109ContourHolonomyDisplacementNormLevel = machineChecked

physicalCMP109ContourVariationNormConventionInputsLevel : ProofLevel
physicalCMP109ContourVariationNormConventionInputsLevel = conditional
