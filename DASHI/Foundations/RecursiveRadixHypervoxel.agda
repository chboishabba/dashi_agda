module DASHI.Foundations.RecursiveRadixHypervoxel where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

open import DASHI.Foundations.Base369MobiusTransport using
  ( OrientationPolarity
  ; positive
  ; negative
  ; flipOrientationPolarity
  )

------------------------------------------------------------------------
-- Rank describes the local shape.  Depth describes recursive refinement.
------------------------------------------------------------------------

data Axis3 : Set where
  axis-low  : Axis3
  axis-mid  : Axis3
  axis-high : Axis3

data AxisBlock : Nat → Set where
  block-root : AxisBlock zero
  block-cons : ∀ {rank} → Axis3 → AxisBlock rank → AxisBlock (suc rank)

data TernaryAddress (rank : Nat) : Nat → Set where
  address-root : TernaryAddress rank zero
  address-refine :
    ∀ {depth} →
    TernaryAddress rank depth →
    AxisBlock rank →
    TernaryAddress rank (suc depth)

addressDepth :
  ∀ {rank depth} → TernaryAddress rank depth → Nat
addressDepth {depth = depth} _ = depth

coarsen :
  ∀ {rank depth} →
  TernaryAddress rank (suc depth) →
  TernaryAddress rank depth
coarsen (address-refine parent child) = parent

fineBlock :
  ∀ {rank depth} →
  TernaryAddress rank (suc depth) →
  AxisBlock rank
fineBlock (address-refine parent child) = child

coarsenAfterRefine :
  ∀ {rank depth}
    (parent : TernaryAddress rank depth)
    (child : AxisBlock rank) →
  coarsen (address-refine parent child) ≡ parent
coarsenAfterRefine parent child = refl

fineBlockAfterRefine :
  ∀ {rank depth}
    (parent : TernaryAddress rank depth)
    (child : AxisBlock rank) →
  fineBlock (address-refine parent child) ≡ child
fineBlockAfterRefine parent child = refl

------------------------------------------------------------------------
-- Address joins concatenate a coarse prefix with a relative fine suffix.
------------------------------------------------------------------------

infixl 6 _⊕_
_⊕_ : Nat → Nat → Nat
n ⊕ zero = n
n ⊕ suc m = suc (n ⊕ m)

data AddressSuffix (rank : Nat) : Nat → Set where
  suffix-root : AddressSuffix rank zero
  suffix-refine :
    ∀ {depth} →
    AddressSuffix rank depth →
    AxisBlock rank →
    AddressSuffix rank (suc depth)

joinAddress :
  ∀ {rank coarseDepth fineDepth} →
  TernaryAddress rank coarseDepth →
  AddressSuffix rank fineDepth →
  TernaryAddress rank (coarseDepth ⊕ fineDepth)
joinAddress parent suffix-root = parent
joinAddress parent (suffix-refine suffix child) =
  address-refine (joinAddress parent suffix) child

joinAddressRoot :
  ∀ {rank depth} (parent : TernaryAddress rank depth) →
  joinAddress parent suffix-root ≡ parent
joinAddressRoot parent = refl

record SubSuperVoxel
  (rank coarseDepth fineDepth : Nat) : Set where
  constructor sub-super-voxel
  field
    coarseAddress : TernaryAddress rank coarseDepth
    relativeAddress : AddressSuffix rank fineDepth
    fineAddress : TernaryAddress rank (coarseDepth ⊕ fineDepth)
    fineAddressIsJoin :
      fineAddress ≡ joinAddress coarseAddress relativeAddress

------------------------------------------------------------------------
-- Cube and cubie are scale-relative roles.
------------------------------------------------------------------------

data ScaleRelativeRole : Set where
  cubieRelativeToParent : ScaleRelativeRole
  cubeRelativeToChildren : ScaleRelativeRole
  rootCubeRole : ScaleRelativeRole

data ScaleRelation : Nat → Nat → Set where
  immediateRefinement : ∀ {depth} → ScaleRelation depth (suc depth)

record CubieCubeRole (rank depth : Nat) : Set where
  field
    address : TernaryAddress rank depth
    upwardRole : ScaleRelativeRole
    downwardRole : ScaleRelativeRole

------------------------------------------------------------------------
-- Sibling assembly and cross-object gluing are separate from address join.
------------------------------------------------------------------------

SiblingField : Nat → Set → Set
SiblingField rank Value = AxisBlock rank → Value

record SiblingAggregation (rank : Nat) (Value : Set) : Set₁ where
  field
    aggregate : SiblingField rank Value → Value
    aggregationLabel : String

record CrossObjectJoin (Left Interface Right : Set) : Set₁ where
  field
    Joined : Set
    leftInterface : Interface → Left
    rightInterface : Interface → Right
    injectLeft : Left → Joined
    injectRight : Right → Joined
    interfaceCompatible :
      ∀ z → injectLeft (leftInterface z) ≡ injectRight (rightInterface z)

------------------------------------------------------------------------
-- Spatial refinement is exponential; configuration recursion is the place
-- where iterated exponentiation/tetration begins.
------------------------------------------------------------------------

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc exponent) = base * pow base exponent

siteCount : Nat → Nat → Nat
siteCount rank depth = pow 3 (rank * depth)

configurationCount : Nat → Nat → Nat
configurationCount rank depth = pow 3 (siteCount rank depth)

tower3 : Nat → Nat
tower3 zero = 1
tower3 (suc height) = pow 3 (tower3 height)

tower3Height0 : tower3 0 ≡ 1
tower3Height0 = refl

tower3Height1 : tower3 1 ≡ 3
tower3Height1 = refl

tower3Height2 : tower3 2 ≡ 27
tower3Height2 = refl

rank1Depth1Sites : siteCount 1 1 ≡ 3
rank1Depth1Sites = refl

rank2Depth1Sites : siteCount 2 1 ≡ 9
rank2Depth1Sites = refl

rank3Depth1Sites : siteCount 3 1 ≡ 27
rank3Depth1Sites = refl

rank3Depth2Sites : siteCount 3 2 ≡ 729
rank3Depth2Sites = refl

------------------------------------------------------------------------
-- The SU(2)-style lift polarity is a fibre, not another ternary axis.
------------------------------------------------------------------------

Polarity : Set
Polarity = OrientationPolarity

multiplyPolarity : Polarity → Polarity → Polarity
multiplyPolarity positive positive = positive
multiplyPolarity positive negative = negative
multiplyPolarity negative positive = negative
multiplyPolarity negative negative = positive

polarityIdentityLeft : ∀ p → multiplyPolarity positive p ≡ p
polarityIdentityLeft positive = refl
polarityIdentityLeft negative = refl

polarityIdentityRight : ∀ p → multiplyPolarity p positive ≡ p
polarityIdentityRight positive = refl
polarityIdentityRight negative = refl

polaritySelfInverse : ∀ p → multiplyPolarity p p ≡ positive
polaritySelfInverse positive = refl
polaritySelfInverse negative = refl

polarityAssociative :
  ∀ a b c →
  multiplyPolarity a (multiplyPolarity b c)
  ≡ multiplyPolarity (multiplyPolarity a b) c
polarityAssociative positive positive positive = refl
polarityAssociative positive positive negative = refl
polarityAssociative positive negative positive = refl
polarityAssociative positive negative negative = refl
polarityAssociative negative positive positive = refl
polarityAssociative negative positive negative = refl
polarityAssociative negative negative positive = refl
polarityAssociative negative negative negative = refl

record LiftedAddress (rank depth : Nat) : Set where
  constructor lifted-address
  field
    baseAddress : TernaryAddress rank depth
    liftPolarity : Polarity

open LiftedAddress public

projectLiftedAddress :
  ∀ {rank depth} →
  LiftedAddress rank depth →
  TernaryAddress rank depth
projectLiftedAddress = baseAddress

centralFlip :
  ∀ {rank depth} →
  LiftedAddress rank depth →
  LiftedAddress rank depth
centralFlip lifted =
  lifted-address
    (baseAddress lifted)
    (flipOrientationPolarity (liftPolarity lifted))

projectCentralFlipInvariant :
  ∀ {rank depth} (lifted : LiftedAddress rank depth) →
  projectLiftedAddress (centralFlip lifted)
  ≡ projectLiftedAddress lifted
projectCentralFlipInvariant lifted = refl

LiftField : Nat → Nat → Set
LiftField rank depth = TernaryAddress rank depth → Polarity

record ScaleLiftTransport (rank : Nat) : Set₁ where
  field
    transport :
      ∀ {depth} →
      LiftedAddress rank depth →
      AxisBlock rank →
      LiftedAddress rank (suc depth)
    baseTransportLaw :
      ∀ {depth} (x : LiftedAddress rank depth) child →
      projectLiftedAddress (transport x child)
      ≡ address-refine (projectLiftedAddress x) child

------------------------------------------------------------------------
-- Rubik-style moves permute base addresses and may transport fibre data.
------------------------------------------------------------------------

record RubikMove (rank depth : Nat) : Set₁ where
  field
    baseMove : TernaryAddress rank depth → TernaryAddress rank depth
    liftedMove : LiftedAddress rank depth → LiftedAddress rank depth
    projectionCommutes :
      ∀ x →
      projectLiftedAddress (liftedMove x)
      ≡ baseMove (projectLiftedAddress x)

------------------------------------------------------------------------
-- Centre-blind data descends to the base; centre-sensitive data remains on
-- the lifted carrier.
------------------------------------------------------------------------

data CentreVisibility : Set where
  centreBlind : CentreVisibility
  centreSensitive : CentreVisibility

record LiftedField (rank depth : Nat) (Value : Set) : Set₁ where
  field
    value : LiftedAddress rank depth → Value
    visibility : CentreVisibility

record CentreBlindField (rank depth : Nat) (Value : Set) : Set₁ where
  field
    value : LiftedAddress rank depth → Value
    centralFlipInvisible : ∀ x → value (centralFlip x) ≡ value x

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record HypervoxelAuthorityBoundary : Set where
  field
    polarityIsGeometricAxisClaimed : Bool
    recursiveSpatialRefinementIsTetrationClaimed : Bool
    cubieAndCubeAreAbsoluteRolesClaimed : Bool
    aggregationLawIsDomainIndependentClaimed : Bool
    baseAndFibreAreExplicit : Bool

canonicalHypervoxelAuthorityBoundary : HypervoxelAuthorityBoundary
canonicalHypervoxelAuthorityBoundary = record
  { polarityIsGeometricAxisClaimed = false
  ; recursiveSpatialRefinementIsTetrationClaimed = false
  ; cubieAndCubeAreAbsoluteRolesClaimed = false
  ; aggregationLawIsDomainIndependentClaimed = false
  ; baseAndFibreAreExplicit = true
  }

hypervoxelSummary : String
hypervoxelSummary =
  "Rank gives the local 3^rank shape; depth gives recursive subvoxel refinement; a binary lift is a fibre over every address, and configuration recursion is distinct from spatial refinement."
