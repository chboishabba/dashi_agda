module DASHI.Physics.YangMills.CompactLieBiInvariantRicciNonnegativeExact where

------------------------------------------------------------------------
-- ROUND74: BI-INVARIANT COMPACT LIE METRIC -> NONNEGATIVE RICCI, UNIFORMLY
--
-- PRIMARY SOURCE
--
-- John Milnor,
-- "Curvatures of Left Invariant Metrics on Lie Groups",
-- Advances in Mathematics 21 (1976), 293--329.
-- DOI: 10.1016/S0001-8708(76)80002-3.
--
-- For a bi-invariant metric, ad_X is skew-adjoint and the sectional curvature
-- of an orthonormal two-plane is
--
--     K(X,Y) = (1/4) ||[X,Y]||^2 >= 0.
--
-- Hence Ric(X,X), being the finite sum of sectional curvatures through X in an
-- orthonormal frame, is nonnegative.  The product metric on G^E has Ricci equal
-- to the sum of the factor Ricci tensors, so the same lower bound 0 is
-- independent of the number of lattice edges.
--
-- DASHI CONTRIBUTION
--
-- The group-native heat/Doob curvature condition used by the mass-gap route is
--
--     (1/2) Ric_{G^E} + Hess V_t >= kappa_t g.
--
-- The Ricci term therefore never consumes negative-curvature budget.  It may
-- be dropped when proving a SUFFICIENT lower bound: it is enough to prove
--
--     Hess V_t >= kappa_t g.
--
-- This removes a whole geometric estimate from physical theorem #6.  The live
-- curvature debt is entirely an effective-action Hessian problem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record OrderedCurvatureScalar : Set₁ where
  field
    Scalar : Set
    zero quarter : Scalar
    add mul : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set

    refl≤ : ∀ x → x ≤ x
    zero≤quarter : zero ≤ quarter
    addMono : ∀ {a b c d} → a ≤ b → c ≤ d → add a c ≤ add b d
    mulNonnegative : ∀ {a b} → zero ≤ a → zero ≤ b → zero ≤ mul a b
    addZeroLeft : ∀ x → add zero x ≡ x

open OrderedCurvatureScalar public

record BiInvariantSectionalCurvatureData (S : OrderedCurvatureScalar) : Set₁ where
  field
    Lie : Set
    bracketNormSq : Lie → Lie → Scalar S
    bracketNormSqNonnegative : ∀ X Y → zero S ≤ bracketNormSq X Y

    sectional : Lie → Lie → Scalar S
    sectionalFormula : ∀ X Y →
      sectional X Y ≡ mul S (quarter S) (bracketNormSq X Y)

open BiInvariantSectionalCurvatureData public

sectionalNonnegative :
  ∀ {S} (D : BiInvariantSectionalCurvatureData S) X Y →
  zero S ≤ sectional D X Y
sectionalNonnegative {S} D X Y
  rewrite sectionalFormula D X Y =
  mulNonnegative S (zero≤quarter S) (bracketNormSqNonnegative D X Y)

foldAdd : ∀ S → List (Scalar S) → Scalar S
foldAdd S [] = zero S
foldAdd S (x ∷ xs) = add S x (foldAdd S xs)

finiteSumNonnegative :
  ∀ {S} →
  (values : List (Scalar S)) →
  (∀ x → x ∈ values → zero S ≤ x) →
  zero S ≤ foldAdd S values
finiteSumNonnegative {S} [] pointwise = refl≤ S (zero S)
finiteSumNonnegative {S} (x ∷ xs) pointwise =
  let
    first = pointwise x (here refl)
    rest = finiteSumNonnegative xs
      (λ y y∈xs → pointwise y (there y∈xs))
    summed = addMono S first rest
  in
  lowerZero summed
  where
  lowerZero :
    {a : Scalar S} →
    add S (zero S) (zero S) ≤ a →
    zero S ≤ a
  lowerZero proof rewrite addZeroLeft S (zero S) = proof

sumSectional :
  ∀ {S} (D : BiInvariantSectionalCurvatureData S) →
  Lie D → List (Lie D) → Scalar S
sumSectional {S} D X [] = zero S
sumSectional {S} D X (Y ∷ Ys) =
  add S (sectional D X Y) (sumSectional D X Ys)

sumSectionalNonnegative :
  ∀ {S} (D : BiInvariantSectionalCurvatureData S) X frame →
  zero S ≤ sumSectional D X frame
sumSectionalNonnegative {S} D X frame =
  finiteSumNonnegative
    (mapSectional D X frame)
    (mapSectionalPointwise D X frame)
  where
  mapSectional :
    BiInvariantSectionalCurvatureData S →
    Lie D → List (Lie D) → List (Scalar S)
  mapSectional D X [] = []
  mapSectional D X (Y ∷ Ys) = sectional D X Y ∷ mapSectional D X Ys

  mapSectionalPointwise :
    (D : BiInvariantSectionalCurvatureData S) →
    (X : Lie D) →
    (frame : List (Lie D)) →
    ∀ q → q ∈ mapSectional D X frame → zero S ≤ q
  mapSectionalPointwise D X [] q ()
  mapSectionalPointwise D X (Y ∷ Ys) .(sectional D X Y) (here refl) =
    sectionalNonnegative D X Y
  mapSectionalPointwise D X (Y ∷ Ys) q (there q∈rest) =
    mapSectionalPointwise D X Ys q q∈rest

-- Standard geometric ownership: Milnor's bi-invariant sectional-curvature
-- formula and the product-Ricci identity are imported geometry, while all
-- finite nonnegative-sum algebra above is owned here.
biInvariantSectionalCurvatureFormulaLevel : ProofLevel
biInvariantSectionalCurvatureFormulaLevel = standardImported

finiteProductRicciNonnegativeLevel : ProofLevel
finiteProductRicciNonnegativeLevel = machineChecked

-- Physical implication for Round74: #6 does not need an independent lower
-- estimate for Ric_{G^E}.  The live YM curvature leaf is the heat-renormalised
-- effective-potential Hessian history.
physicalHeatDoobRicciDebtLevel : ProofLevel
physicalHeatDoobRicciDebtLevel = standardImported
