module DASHI.Physics.YangMills.BalabanP33CMP109LiteralPathDerivativeKernelExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- Turn the repository's exact recursive holonomy derivative into a literal
-- edge kernel.  For a path e1...en and a basis perturbation at b, the kernel is
--
--   K_path(b)
--     = D^L(U_e1...U_en)[delta_b].
--
-- The recursion is exactly
--
--   delta_b(e1) + Ad(U_e1) K_tail(b),
--
-- so a bond which does not occur in the path has zero kernel entry.  The result
-- is lifted through an explicit finite family of CMP109 contours.  Consequently
-- derivative support is the existential path-occurrence relation; no separate
-- support oracle is needed.
--
-- The later logarithm and outer-exponential factors act on this literal path
-- kernel.  Their norm estimates remain separate, but path support and the
-- finite derivative formula are discharged here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; subst; trans)
open import Relation.Nullary using (Dec; yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4FiniteHolonomyDerivativeExact as Holonomy

DecidableEquality : Set → Set₁
DecidableEquality Carrier = ∀ left right → Dec (left ≡ right)

basisVariation :
  ∀ {Edge Lie}
    (decide : DecidableEquality Edge)
    (zero vector : Lie) → Edge → Edge → Lie
basisVariation decide zero vector selected edge
    with decide selected edge
... | yes _ = vector
... | no _ = zero

------------------------------------------------------------------------
-- Proof-relevant non-membership and occurrence.
------------------------------------------------------------------------

data NotMember {Edge : Set} (selected : Edge) : List Edge → Set where
  notMemberNil : NotMember selected []
  notMemberCons : ∀ {edge edges} →
    selected ≢ edge →
    NotMember selected edges →
    NotMember selected (edge ∷ edges)

data Member {Edge : Set} (selected : Edge) : List Edge → Set where
  here : ∀ {edges} → Member selected (selected ∷ edges)
  there : ∀ {edge edges} →
    Member selected edges → Member selected (edge ∷ edges)

basisVariationZeroOffSelected :
  ∀ {Edge Lie}
    (decide : DecidableEquality Edge)
    (zero vector : Lie)
    selected edge →
  selected ≢ edge →
  basisVariation decide zero vector selected edge ≡ zero
basisVariationZeroOffSelected decide zero vector selected edge unequal
    with decide selected edge
... | yes equal = unequal equal
... | no _ = refl

basisVariationZeroOnAbsentPath :
  ∀ {Edge Lie}
    (decide : DecidableEquality Edge)
    (zero vector : Lie)
    selected edges →
  NotMember selected edges →
  Holonomy.All
    (λ edge → basisVariation decide zero vector selected edge ≡ zero)
    edges
basisVariationZeroOnAbsentPath decide zero vector selected []
    notMemberNil = Holonomy.allNil
basisVariationZeroOnAbsentPath decide zero vector selected (edge ∷ edges)
    (notMemberCons unequal absentTail) =
  Holonomy.allCons
    (basisVariationZeroOffSelected
      decide zero vector selected edge unequal)
    (basisVariationZeroOnAbsentPath
      decide zero vector selected edges absentTail)

------------------------------------------------------------------------
-- Literal path kernel.
------------------------------------------------------------------------

pathDerivativeKernel :
  ∀ {Edge Group Lie}
    (algebra : Holonomy.HolonomyDifferentialAlgebra Group Lie)
    (decide : DecidableEquality Edge)
    (connection : Edge → Group)
    (basisVector : Lie)
    (path : List Edge)
    (selected : Edge) → Lie
pathDerivativeKernel algebra decide connection basisVector path selected =
  Holonomy.leftTrivializedHolonomyDerivative
    algebra connection
    (basisVariation decide (Holonomy.zeroLie algebra) basisVector selected)
    path

pathDerivativeKernelRecursion :
  ∀ {Edge Group Lie}
    (algebra : Holonomy.HolonomyDifferentialAlgebra Group Lie)
    (decide : DecidableEquality Edge)
    (connection : Edge → Group)
    (basisVector : Lie)
    edge edges selected →
  pathDerivativeKernel algebra decide connection basisVector
    (edge ∷ edges) selected
  ≡ Holonomy.addLie algebra
      (basisVariation decide (Holonomy.zeroLie algebra)
        basisVector selected edge)
      (Holonomy.adjoint algebra (connection edge)
        (pathDerivativeKernel algebra decide connection basisVector
          edges selected))
pathDerivativeKernelRecursion algebra decide connection basisVector
    edge edges selected = refl

pathDerivativeKernelZeroOutside :
  ∀ {Edge Group Lie}
    (algebra : Holonomy.HolonomyDifferentialAlgebra Group Lie)
    (decide : DecidableEquality Edge)
    (connection : Edge → Group)
    (basisVector : Lie)
    path selected →
  NotMember selected path →
  pathDerivativeKernel algebra decide connection basisVector path selected
  ≡ Holonomy.zeroLie algebra
pathDerivativeKernelZeroOutside algebra decide connection basisVector
    path selected absent =
  Holonomy.variationZeroOnPath
    algebra connection
    (basisVariation decide (Holonomy.zeroLie algebra) basisVector selected)
    path
    (basisVariationZeroOnAbsentPath
      decide (Holonomy.zeroLie algebra) basisVector selected path absent)

------------------------------------------------------------------------
-- Finite contour family.  This is the literal sum before the outer exponential
-- and principal logarithm derivative are applied.
------------------------------------------------------------------------

record CMP109FinitePathFamily
    (Coarse Sample Edge Group Lie : Set)
    (algebra : Holonomy.HolonomyDifferentialAlgebra Group Lie) : Set₁ where
  field
    samples : Coarse → List Sample
    contour : Coarse → Sample → List Edge
    connection : Edge → Group
    decideEdge : DecidableEquality Edge
    basisVector : Lie

open CMP109FinitePathFamily public

sumLie :
  ∀ {Group Lie}
    (algebra : Holonomy.HolonomyDifferentialAlgebra Group Lie) →
  List Lie → Lie
sumLie algebra [] = Holonomy.zeroLie algebra
sumLie algebra (value ∷ values) =
  Holonomy.addLie algebra value (sumLie algebra values)

map : ∀ {A B : Set} → (A → B) → List A → List B
map function [] = []
map function (value ∷ values) =
  function value ∷ map function values

cmp109PathDerivativeEntry :
  ∀ {Coarse Sample Edge Group Lie algebra} →
  CMP109FinitePathFamily Coarse Sample Edge Group Lie algebra →
  Coarse → Edge → Lie
cmp109PathDerivativeEntry {algebra = algebra} family coarse selected =
  sumLie algebra
    (map
      (λ sample →
        pathDerivativeKernel algebra
          (decideEdge family)
          (connection family)
          (basisVector family)
          (contour family coarse sample)
          selected)
      (samples family coarse))

PathFamilyOccurrence :
  ∀ {Coarse Sample Edge Group Lie algebra} →
  CMP109FinitePathFamily Coarse Sample Edge Group Lie algebra →
  Coarse → Edge → Set
PathFamilyOccurrence {Sample = Sample} family coarse selected =
  Σ Sample (λ sample →
    Σ (Member sample (samples family coarse)) (λ _ →
      Member selected (contour family coarse sample)))

record AbsentFromEveryContour
    {Coarse Sample Edge Group Lie : Set}
    {algebra : Holonomy.HolonomyDifferentialAlgebra Group Lie}
    (family : CMP109FinitePathFamily
      Coarse Sample Edge Group Lie algebra)
    (coarse : Coarse) (selected : Edge) : Set₁ where
  field
    absent : ∀ sample →
      Member sample (samples family coarse) →
      NotMember selected (contour family coarse sample)

open AbsentFromEveryContour public

allZeroSum :
  ∀ {Group Lie}
    (algebra : Holonomy.HolonomyDifferentialAlgebra Group Lie)
    values →
  Holonomy.All (λ value → value ≡ Holonomy.zeroLie algebra) values →
  sumLie algebra values ≡ Holonomy.zeroLie algebra
allZeroSum algebra [] Holonomy.allNil = refl
allZeroSum algebra (value ∷ values)
    (Holonomy.allCons valueZero restZero) =
  trans
    (cong
      (Holonomy.addLie algebra value)
      (allZeroSum algebra values restZero))
    (trans
      (cong
        (λ head → Holonomy.addLie algebra head (Holonomy.zeroLie algebra))
        valueZero)
      (Holonomy.addZeroLeft algebra (Holonomy.zeroLie algebra)))

mapKernelsZeroWhenAbsent :
  ∀ {Coarse Sample Edge Group Lie}
    {algebra : Holonomy.HolonomyDifferentialAlgebra Group Lie}
    (family : CMP109FinitePathFamily
      Coarse Sample Edge Group Lie algebra)
    coarse selected sampleList →
  (∀ sample → Member sample sampleList →
    NotMember selected (contour family coarse sample)) →
  Holonomy.All
    (λ value → value ≡ Holonomy.zeroLie algebra)
    (map
      (λ sample →
        pathDerivativeKernel algebra
          (decideEdge family)
          (connection family)
          (basisVector family)
          (contour family coarse sample)
          selected)
      sampleList)
mapKernelsZeroWhenAbsent family coarse selected [] absent =
  Holonomy.allNil
mapKernelsZeroWhenAbsent family coarse selected (sample ∷ samples) absent =
  Holonomy.allCons
    (pathDerivativeKernelZeroOutside _ _ _ _ _ _
      (absent sample here))
    (mapKernelsZeroWhenAbsent family coarse selected samples
      (λ later membership → absent later (there membership)))

cmp109PathDerivativeVanishesOutsideLiteralOccurrence :
  ∀ {Coarse Sample Edge Group Lie}
    {algebra : Holonomy.HolonomyDifferentialAlgebra Group Lie}
    (family : CMP109FinitePathFamily
      Coarse Sample Edge Group Lie algebra)
    coarse selected →
  AbsentFromEveryContour family coarse selected →
  cmp109PathDerivativeEntry family coarse selected
  ≡ Holonomy.zeroLie algebra
cmp109PathDerivativeVanishesOutsideLiteralOccurrence
    {algebra = algebra} family coarse selected absence =
  allZeroSum algebra _
    (mapKernelsZeroWhenAbsent family coarse selected
      (samples family coarse) (absent absence))

cmp109LiteralPathKernelLevel : ProofLevel
cmp109LiteralPathKernelLevel = machineChecked

cmp109LiteralPathSupportLevel : ProofLevel
cmp109LiteralPathSupportLevel = machineChecked

cmp109OuterLogTransportIdentificationLevel : ProofLevel
cmp109OuterLogTransportIdentificationLevel = conditional
