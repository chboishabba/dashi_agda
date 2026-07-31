module DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale

------------------------------------------------------------------------
-- Quantitative principal-chart admission for finite SU(2) paths.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- The principal logarithm is unavailable at the antipodal cut.  For every
-- relative holonomy used by the block map, chart admission can instead be
-- proved from two elementary facts: multiplicative defect is subadditive and
-- every path factor is uniformly small.  The finite induction below yields
--
--   defect(product factors) <= length(factors) * linkDefectBound.
--
-- Thus the analytic input is reduced to a single scalar cut comparison for the
-- maximal printed path length, rather than a separate principal-log hypothesis
-- for every coarse bond and fine site.
------------------------------------------------------------------------

record GroupDefectAlgebra (Group Bound : Set) : Set₁ where
  field
    scale : Scale.OrderedAdditiveScale Bound

    identity : Group
    multiply : Group → Group → Group
    defect : Group → Bound

    defectIdentity : defect identity ≡ Scale.zeroScalar scale
    defectProduct : ∀ left right →
      Scale.LessEqual scale
        (defect (multiply left right))
        (Scale.add scale (defect left) (defect right))

open GroupDefectAlgebra public

productList :
  ∀ {Group Bound} → GroupDefectAlgebra Group Bound →
  List Group → Group
productList algebra [] = identity algebra
productList algebra (value ∷ values) =
  multiply algebra value (productList algebra values)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = Agda.Builtin.Nat.zero
listLength (_ ∷ values) = Agda.Builtin.Nat.suc (listLength values)

data AllDefectBelow
    {Group Bound : Set}
    (algebra : GroupDefectAlgebra Group Bound)
    (bound : Bound) : List Group → Set where
  allDefectNil : AllDefectBelow algebra bound []
  allDefectCons : ∀ {value values} →
    Scale.LessEqual (scale algebra) (defect algebra value) bound →
    AllDefectBelow algebra bound values →
    AllDefectBelow algebra bound (value ∷ values)

productDefectBelowLengthScale :
  ∀ {Group Bound}
    (algebra : GroupDefectAlgebra Group Bound)
    bound {values : List Group} →
  AllDefectBelow algebra bound values →
  Scale.LessEqual (scale algebra)
    (defect algebra (productList algebra values))
    (Scale.natScale (scale algebra) (listLength values) bound)
productDefectBelowLengthScale algebra bound allDefectNil =
  Scale.substLower
    (defectIdentity algebra)
    (Scale.reflexive (scale algebra) (Scale.zeroScalar (scale algebra)))
  where
  Scale.substLower : ∀ {Scalar : Set}
    {ordered : Scale.OrderedAdditiveScale Scalar}
    {left right upper : Scalar} →
    left ≡ right →
    Scale.LessEqual ordered right upper →
    Scale.LessEqual ordered left upper
  Scale.substLower equality proof rewrite equality = proof
productDefectBelowLengthScale algebra bound
    (allDefectCons headBound tailBounds) =
  Scale.transitive (scale algebra)
    (defectProduct algebra _ _)
    (Scale.addMonotone (scale algebra)
      headBound
      (productDefectBelowLengthScale algebra bound tailBounds))

record PrincipalLogCutData (Group Bound : Set) : Set₁ where
  field
    defectAlgebra : GroupDefectAlgebra Group Bound
    chartRadius : Bound

    PrincipalLogAdmissible : Group → Set

    defectBelowRadiusImpliesAdmissible : ∀ group →
      Scale.LessEqual (scale defectAlgebra)
        (defect defectAlgebra group) chartRadius →
      PrincipalLogAdmissible group

open PrincipalLogCutData public

record UniformPathChartInputs
    (Group Bound : Set) : Set₁ where
  field
    chart : PrincipalLogCutData Group Bound
    factors : List Group
    linkDefectBound : Bound

    everyFactorSmall :
      AllDefectBelow (defectAlgebra chart) linkDefectBound factors

    lengthBudgetBelowChartRadius :
      Scale.LessEqual (scale (defectAlgebra chart))
        (Scale.natScale (scale (defectAlgebra chart))
          (listLength factors) linkDefectBound)
        (chartRadius chart)

open UniformPathChartInputs public

pathProductPrincipalLogAdmissible :
  ∀ {Group Bound}
    (inputs : UniformPathChartInputs Group Bound) →
  PrincipalLogAdmissible (chart inputs)
    (productList (defectAlgebra (chart inputs)) (factors inputs))
pathProductPrincipalLogAdmissible inputs =
  defectBelowRadiusImpliesAdmissible (chart inputs)
    (productList (defectAlgebra (chart inputs)) (factors inputs))
    (Scale.transitive (scale (defectAlgebra (chart inputs)))
      (productDefectBelowLengthScale
        (defectAlgebra (chart inputs))
        (linkDefectBound inputs)
        (everyFactorSmall inputs))
      (lengthBudgetBelowChartRadius inputs))

principalLogFinitePathDefectLevel : ProofLevel
principalLogFinitePathDefectLevel = machineChecked

principalLogPathAdmissionLevel : ProofLevel
principalLogPathAdmissionLevel = machineChecked

physicalSU2MultiplicativeDefectInputsLevel : ProofLevel
physicalSU2MultiplicativeDefectInputsLevel = conditional

physicalCMP109MaxPathLengthCutInputsLevel : ProofLevel
physicalCMP109MaxPathLengthCutInputsLevel = conditional
