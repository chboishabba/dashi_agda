module DASHI.Physics.YangMills.BalabanFiniteAdjointQuadraticForms where

------------------------------------------------------------------------
-- Finite inner-product sums on the literal lattice carriers.
--
-- The Bałaban Hessians are finite-dimensional quadratic forms at fixed
-- cutoff.  This module constructs the point-, bond-, and plaquette-field
-- squared norms by summing an invariant adjoint inner product over the exact
-- finite enumerations.  Gauge invariance is proved by list induction.
--
-- The scalar and adjoint inner product remain parameters; no positivity,
-- determinant, or analytic estimate is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4 )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using
  ( DirectedBond4
  ; source
  )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeEnumeration using
  ( allCube4
  ; allPositiveBonds
  )
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  ( GroupStructure )
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  ( GaugeFunction4 )
open import DASHI.Physics.YangMills.BalabanLatticeAdjointCovariantDerivative using
  ( Vector
  ; action
  )
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( AdjointLinearModule
  ; additive
  ; DirectedAdjointBondField4
  ; transformAdjointBondField
  )
open import DASHI.Physics.YangMills.BalabanPeriodicPlaquetteHolonomy using
  ( AxisPair4
  ; axes01
  ; axes02
  ; axes03
  ; axes12
  ; axes13
  ; axes23
  )

record AdjointInnerProductModule
  (group : GroupStructure) : Set₁ where
  field
    linear : AdjointLinearModule group

    Scalar : Set
    zeroScalar : Scalar
    addScalar : Scalar → Scalar → Scalar

    inner :
      Vector (additive linear) →
      Vector (additive linear) →
      Scalar

    innerActionInvariant :
      ∀ g X Y →
      inner
        (action (additive linear) g X)
        (action (additive linear) g Y)
      ≡ inner X Y

open AdjointInnerProductModule public

sumMap :
  ∀ {A Scalar : Set} →
  Scalar →
  (Scalar → Scalar → Scalar) →
  (A → Scalar) →
  List A →
  Scalar
sumMap zero add f [] = zero
sumMap zero add f (x ∷ xs) =
  add (f x) (sumMap zero add f xs)

sumMapPointwise :
  ∀ {A Scalar : Set}
  (zero : Scalar)
  (add : Scalar → Scalar → Scalar)
  (f g : A → Scalar)
  (xs : List A) →
  (∀ x → f x ≡ g x) →
  sumMap zero add f xs ≡ sumMap zero add g xs
sumMapPointwise zero add f g [] pointwise = refl
sumMapPointwise zero add f g (x ∷ xs) pointwise =
  trans
    (cong
      (λ head → add head (sumMap zero add f xs))
      (pointwise x))
    (cong
      (add (g x))
      (sumMapPointwise zero add f g xs pointwise))

PointAdjointField4 :
  (N : Nat) →
  (group : GroupStructure) →
  AdjointInnerProductModule group →
  Set
PointAdjointField4 N group innerModule =
  Cube4 N → Vector (additive (linear innerModule))

PlaquetteAdjointField4 :
  (N : Nat) →
  (group : GroupStructure) →
  AdjointInnerProductModule group →
  Set
PlaquetteAdjointField4 N group innerModule =
  AxisPair4 → Cube4 N →
  Vector (additive (linear innerModule))

allAxisPairs : List AxisPair4
allAxisPairs =
  axes01 ∷ axes02 ∷ axes03 ∷
  axes12 ∷ axes13 ∷ axes23 ∷ []

pointFieldSquaredNorm :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (innerModule : AdjointInnerProductModule group) →
  PointAdjointField4 N group innerModule →
  Scalar innerModule
pointFieldSquaredNorm {N = N} group innerModule phi =
  sumMap
    (zeroScalar innerModule)
    (addScalar innerModule)
    (λ x → inner innerModule (phi x) (phi x))
    (allCube4 N)

bondFieldSquaredNorm :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (innerModule : AdjointInnerProductModule group) →
  DirectedAdjointBondField4 N group (linear innerModule) →
  Scalar innerModule
bondFieldSquaredNorm {N = N} group innerModule A =
  sumMap
    (zeroScalar innerModule)
    (addScalar innerModule)
    (λ b → inner innerModule (A b) (A b))
    (allPositiveBonds N)

plaquetteFieldSquaredNorm :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (innerModule : AdjointInnerProductModule group) →
  PlaquetteAdjointField4 N group innerModule →
  Scalar innerModule
plaquetteFieldSquaredNorm {N = N} group innerModule F =
  sumMap
    (zeroScalar innerModule)
    (addScalar innerModule)
    (λ pair →
      sumMap
        (zeroScalar innerModule)
        (addScalar innerModule)
        (λ x → inner innerModule (F pair x) (F pair x))
        (allCube4 N))
    allAxisPairs

transformPointAdjointField :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (innerModule : AdjointInnerProductModule group) →
  GaugeFunction4 N group →
  PointAdjointField4 N group innerModule →
  PointAdjointField4 N group innerModule
transformPointAdjointField group innerModule gauge phi x =
  action (additive (linear innerModule)) (gauge x) (phi x)

transformPlaquetteAdjointField :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (innerModule : AdjointInnerProductModule group) →
  GaugeFunction4 N group →
  PlaquetteAdjointField4 N group innerModule →
  PlaquetteAdjointField4 N group innerModule
transformPlaquetteAdjointField group innerModule gauge F pair x =
  action (additive (linear innerModule)) (gauge x) (F pair x)

pointFieldSquaredNormGaugeInvariant :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (innerModule : AdjointInnerProductModule group) →
  (gauge : GaugeFunction4 N group) →
  (phi : PointAdjointField4 N group innerModule) →
  pointFieldSquaredNorm group innerModule
    (transformPointAdjointField group innerModule gauge phi)
  ≡ pointFieldSquaredNorm group innerModule phi
pointFieldSquaredNormGaugeInvariant
  {N = N} group innerModule gauge phi =
  sumMapPointwise
    (zeroScalar innerModule)
    (addScalar innerModule)
    _ _ (allCube4 N)
    (λ x →
      innerActionInvariant innerModule
        (gauge x) (phi x) (phi x))

bondFieldSquaredNormGaugeInvariant :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (innerModule : AdjointInnerProductModule group) →
  (gauge : GaugeFunction4 N group) →
  (A : DirectedAdjointBondField4 N group (linear innerModule)) →
  bondFieldSquaredNorm group innerModule
    (transformAdjointBondField
      group (linear innerModule) gauge A)
  ≡ bondFieldSquaredNorm group innerModule A
bondFieldSquaredNormGaugeInvariant
  {N = N} group innerModule gauge A =
  sumMapPointwise
    (zeroScalar innerModule)
    (addScalar innerModule)
    _ _ (allPositiveBonds N)
    (λ b →
      innerActionInvariant innerModule
        (gauge (source b)) (A b) (A b))

plaquetteFieldSquaredNormGaugeInvariant :
  ∀ {N : Nat}
  (group : GroupStructure) →
  (innerModule : AdjointInnerProductModule group) →
  (gauge : GaugeFunction4 N group) →
  (F : PlaquetteAdjointField4 N group innerModule) →
  plaquetteFieldSquaredNorm group innerModule
    (transformPlaquetteAdjointField group innerModule gauge F)
  ≡ plaquetteFieldSquaredNorm group innerModule F
plaquetteFieldSquaredNormGaugeInvariant
  {N = N} group innerModule gauge F =
  sumMapPointwise
    (zeroScalar innerModule)
    (addScalar innerModule)
    _ _ allAxisPairs
    (λ pair →
      sumMapPointwise
        (zeroScalar innerModule)
        (addScalar innerModule)
        _ _ (allCube4 N)
        (λ x →
          innerActionInvariant innerModule
            (gauge x) (F pair x) (F pair x)))
