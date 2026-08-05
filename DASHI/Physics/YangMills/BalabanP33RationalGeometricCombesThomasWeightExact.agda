module DASHI.Physics.YangMills.BalabanP33RationalGeometricCombesThomasWeightExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- DASHI CONTRIBUTION
--
-- Construct the geometric diagonal weight used by the finite conjugation
-- theorem without invoking a real exponential.  For a support-graph distance d
-- and reciprocal rational bases s,t with s*t=1, define
--
--   D_root(x)      = t ^ d(root,x),
--   D_root^{-1}(x) = s ^ d(root,x).
--
-- The module proves the pointwise inverse law exactly.  If a nonzero operator
-- entry joins equal or adjacent support-graph shells, its conjugation ratio is
-- exactly one of
--
--   1, t, s.
--
-- Thus the complete one-edge tilt distortion is controlled by the two scalar
-- quantities |s-1| and |t-1|.  Any finite-range stencil can use its own support
-- graph as the metric, so every nonzero stencil edge is a unit graph step.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _-_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Rational powers and reciprocal products.
------------------------------------------------------------------------

pow : ℚ → Nat → ℚ
pow base zero = 1ℚ
pow base (suc exponent) = pow base exponent * base

powReciprocalProduct :
  ∀ base inverseBase →
  base * inverseBase ≡ 1ℚ →
  ∀ exponent →
  pow base exponent * pow inverseBase exponent ≡ 1ℚ
powReciprocalProduct base inverseBase inverseLaw zero =
  ℚRing.solve []
powReciprocalProduct base inverseBase inverseLaw (suc exponent) =
  let
    prefixLaw :
      pow base exponent * pow inverseBase exponent ≡ 1ℚ
    prefixLaw =
      powReciprocalProduct base inverseBase inverseLaw exponent

    rearrange :
      pow base (suc exponent) * pow inverseBase (suc exponent)
      ≡ (pow base exponent * pow inverseBase exponent)
          * (base * inverseBase)
    rearrange = ℚRing.solve []

    collapsePrefix :
      (pow base exponent * pow inverseBase exponent)
        * (base * inverseBase)
      ≡ 1ℚ * (base * inverseBase)
    collapsePrefix =
      cong (_* (base * inverseBase)) prefixLaw

    removeOne : 1ℚ * (base * inverseBase) ≡ base * inverseBase
    removeOne = ℚRing.solve []
  in
  trans rearrange
    (trans collapsePrefix (trans removeOne inverseLaw))

powNonnegative :
  ∀ base → 0ℚ ≤ base → ∀ exponent → 0ℚ ≤ pow base exponent
powNonnegative base baseNonnegative zero = ℚP.nonNegative⁻¹ 1ℚ
powNonnegative base baseNonnegative (suc exponent) =
  let
    instance
      prefixNN : NonNegative (pow base exponent)
      prefixNN = ℚ.nonNegative (powNonnegative base baseNonnegative exponent)
      baseNN : NonNegative base
      baseNN = ℚ.nonNegative baseNonnegative
  in
  ℚP.nonNegative⁻¹ (pow base exponent * base)

powAbsolute :
  ∀ base →
  ∣ base ∣ ≡ base →
  ∀ exponent →
  ∣ pow base exponent ∣ ≡ pow base exponent
powAbsolute base baseAbsolute zero = refl
powAbsolute base baseAbsolute (suc exponent) =
  trans
    (ℚP.∣p*q∣≡∣p∣*∣q∣ (pow base exponent) base)
    (trans
      (cong (_* ∣ base ∣) (powAbsolute base baseAbsolute exponent))
      (cong (pow base exponent *_) baseAbsolute))

------------------------------------------------------------------------
-- Rooted weights.
------------------------------------------------------------------------

rootedWeight :
  ∀ {Site : Set} →
  (Site → Site → Nat) → ℚ → Site → Site → ℚ
rootedWeight distance inverseBase root site =
  pow inverseBase (distance root site)

rootedInverseWeight :
  ∀ {Site : Set} →
  (Site → Site → Nat) → ℚ → Site → Site → ℚ
rootedInverseWeight distance base root site =
  pow base (distance root site)

rootedWeightInverseLaw :
  ∀ {Site : Set}
    (distance : Site → Site → Nat)
    (base inverseBase : ℚ) →
  base * inverseBase ≡ 1ℚ →
  ∀ root site →
  rootedInverseWeight distance base root site
    * rootedWeight distance inverseBase root site
  ≡ 1ℚ
rootedWeightInverseLaw distance base inverseBase inverseLaw root site =
  powReciprocalProduct
    base inverseBase inverseLaw (distance root site)

rootedInverseAtRoot :
  ∀ {Site : Set}
    (distance : Site → Site → Nat)
    (base : ℚ)
    (root : Site) →
  distance root root ≡ zero →
  rootedInverseWeight distance base root root ≡ 1ℚ
rootedInverseAtRoot distance base root rootDistanceZero
  rewrite rootDistanceZero = refl

rootedWeightNonnegative :
  ∀ {Site : Set}
    (distance : Site → Site → Nat)
    (inverseBase : ℚ) →
  0ℚ ≤ inverseBase →
  ∀ root site →
  0ℚ ≤ rootedWeight distance inverseBase root site
rootedWeightNonnegative distance inverseBase inverseNonnegative root site =
  powNonnegative inverseBase inverseNonnegative (distance root site)

rootedWeightAbsolute :
  ∀ {Site : Set}
    (distance : Site → Site → Nat)
    (inverseBase : ℚ) →
  ∣ inverseBase ∣ ≡ inverseBase →
  ∀ root site →
  ∣ rootedWeight distance inverseBase root site ∣
    ≡ rootedWeight distance inverseBase root site
rootedWeightAbsolute distance inverseBase inverseAbsolute root site =
  powAbsolute inverseBase inverseAbsolute (distance root site)

------------------------------------------------------------------------
-- Exact unit-shell ratios.
------------------------------------------------------------------------

data UnitShellRelation : Nat → Nat → Set where
  sameShell : ∀ shell → UnitShellRelation shell shell
  leftOneFarther : ∀ shell → UnitShellRelation (suc shell) shell
  rightOneFarther : ∀ shell → UnitShellRelation shell (suc shell)

unitShellRatio : ℚ → ℚ → Nat → Nat → ℚ
unitShellRatio base inverseBase leftDistance rightDistance =
  pow inverseBase leftDistance * pow base rightDistance

unitShellRatioExact :
  ∀ base inverseBase →
  base * inverseBase ≡ 1ℚ →
  ∀ {leftDistance rightDistance} →
  UnitShellRelation leftDistance rightDistance →
  (unitShellRatio base inverseBase leftDistance rightDistance ≡ 1ℚ)
  ⊎
  ((unitShellRatio base inverseBase leftDistance rightDistance ≡ inverseBase)
    ⊎
   (unitShellRatio base inverseBase leftDistance rightDistance ≡ base))
unitShellRatioExact base inverseBase inverseLaw (sameShell shell) =
  inj₁
    (trans
      (ℚRing.solve-∀
        (pow inverseBase shell) (pow base shell))
      (powReciprocalProduct base inverseBase inverseLaw shell))
unitShellRatioExact base inverseBase inverseLaw (leftOneFarther shell) =
  inj₂ (inj₁ ratio)
  where
    prefixLaw :
      pow base shell * pow inverseBase shell ≡ 1ℚ
    prefixLaw =
      powReciprocalProduct base inverseBase inverseLaw shell

    rearrange :
      unitShellRatio base inverseBase (suc shell) shell
      ≡ (pow base shell * pow inverseBase shell) * inverseBase
    rearrange = ℚRing.solve []

    collapse :
      (pow base shell * pow inverseBase shell) * inverseBase
      ≡ 1ℚ * inverseBase
    collapse = cong (_* inverseBase) prefixLaw

    ratio :
      unitShellRatio base inverseBase (suc shell) shell ≡ inverseBase
    ratio = trans rearrange (trans collapse (ℚRing.solve []))
unitShellRatioExact base inverseBase inverseLaw (rightOneFarther shell) =
  inj₂ (inj₂ ratio)
  where
    prefixLaw :
      pow base shell * pow inverseBase shell ≡ 1ℚ
    prefixLaw =
      powReciprocalProduct base inverseBase inverseLaw shell

    rearrange :
      unitShellRatio base inverseBase shell (suc shell)
      ≡ (pow base shell * pow inverseBase shell) * base
    rearrange = ℚRing.solve []

    collapse :
      (pow base shell * pow inverseBase shell) * base
      ≡ 1ℚ * base
    collapse = cong (_* base) prefixLaw

    ratio :
      unitShellRatio base inverseBase shell (suc shell) ≡ base
    ratio = trans rearrange (trans collapse (ℚRing.solve []))

unitShellDistortionBound :
  ∀ base inverseBase distortion →
  base * inverseBase ≡ 1ℚ →
  0ℚ ≤ distortion →
  ∣ base - 1ℚ ∣ ≤ distortion →
  ∣ inverseBase - 1ℚ ∣ ≤ distortion →
  ∀ {leftDistance rightDistance} →
  UnitShellRelation leftDistance rightDistance →
  ∣ unitShellRatio base inverseBase leftDistance rightDistance - 1ℚ ∣
    ≤ distortion
unitShellDistortionBound
    base inverseBase distortion inverseLaw distortionNonnegative
    baseBound inverseBound relation
  with unitShellRatioExact base inverseBase inverseLaw relation
... | inj₁ ratio =
  subst
    (λ selected → ∣ selected - 1ℚ ∣ ≤ distortion)
    (sym ratio)
    (subst
      (λ zeroValue → zeroValue ≤ distortion)
      (ℚRing.solve [])
      distortionNonnegative)
... | inj₂ (inj₁ ratio) =
  subst
    (λ selected → ∣ selected - 1ℚ ∣ ≤ distortion)
    (sym ratio)
    inverseBound
... | inj₂ (inj₂ ratio) =
  subst
    (λ selected → ∣ selected - 1ℚ ∣ ≤ distortion)
    (sym ratio)
    baseBound

rationalGeometricWeightLevel : ProofLevel
rationalGeometricWeightLevel = machineChecked

supportGraphUnitRatioLevel : ProofLevel
supportGraphUnitRatioLevel = machineChecked

supportGraphTiltDistortionLevel : ProofLevel
supportGraphTiltDistortionLevel = machineChecked
