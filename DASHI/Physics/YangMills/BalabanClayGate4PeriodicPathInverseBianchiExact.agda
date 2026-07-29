module DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact using (SignedAxis4)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact as Covariance

------------------------------------------------------------------------
-- Primary provenance.
--
-- G. G. Batrouni,
-- "Plaquette Formulation and the Bianchi Identity for Lattice Gauge Theories",
-- Nuclear Physics B 208 (1982), 467--483.
-- DOI: 10.1016/0550-3213(82)90231-0.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press, open-access
-- reissue (2022). DOI: 10.1017/9781009290395.
--
-- In a non-Abelian lattice theory, six face holonomies must first be transported
-- to one base point and ordered.  The algebra below proves cancellation from a
-- literal path/opposite-reverse decomposition; it does not use the false
-- untransported statement that an arbitrary product of six plaquettes is one.
------------------------------------------------------------------------

infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ right = right
(left ∷ lefts) ++ right = left ∷ (lefts ++ right)

oppositeDirection : SignedAxis4 → SignedAxis4
oppositeDirection (pair axis true) = pair axis false
oppositeDirection (pair axis false) = pair axis true

reverseOpposite : List SignedAxis4 → List SignedAxis4
reverseOpposite [] = []
reverseOpposite (direction ∷ directions) =
  reverseOpposite directions ++ (oppositeDirection direction ∷ [])

walkAppend : ∀ {n} (site : Periodic.PeriodicBlock n) left right →
  Bond.walk site (left ++ right)
  ≡ Bond.walk (Bond.walk site left) right
walkAppend site [] right = refl
walkAppend site (direction ∷ directions) right =
  walkAppend (Bond.walkStep site direction) directions right

walkOppositeStep :
  ∀ {n} (stepLaws : Covariance.PeriodicStepInverseLaws n)
    site direction →
  Bond.walkStep (Bond.walkStep site direction)
    (oppositeDirection direction)
  ≡ site
walkOppositeStep stepLaws site (pair axis true) =
  Covariance.negativeAfterPositive stepLaws site axis
walkOppositeStep stepLaws site (pair axis false) =
  Covariance.positiveAfterNegative stepLaws site axis

walkReverseOpposite :
  ∀ {n} (stepLaws : Covariance.PeriodicStepInverseLaws n)
    site directions →
  Bond.walk (Bond.walk site directions) (reverseOpposite directions)
  ≡ site
walkReverseOpposite stepLaws site [] = refl
walkReverseOpposite stepLaws site (direction ∷ directions) =
  trans
    (walkAppend
      (Bond.walk (Bond.walkStep site direction) directions)
      (reverseOpposite directions)
      (oppositeDirection direction ∷ []))
    (trans
      (cong
        (λ intermediate →
          Bond.walk intermediate (oppositeDirection direction ∷ []))
        (walkReverseOpposite stepLaws
          (Bond.walkStep site direction) directions))
      (walkOppositeStep stepLaws site direction))

inverseIdentity :
  ∀ {Value} (group : Bond.ExactLinkGroup Value) →
  Bond.inverse group (Bond.identity group) ≡ Bond.identity group
inverseIdentity group =
  trans
    (sym (Bond.identityRight group (Bond.inverse group (Bond.identity group))))
    (Bond.inverseLeft group (Bond.identity group))

singletonHolonomy :
  ∀ {n Value} {group : Bond.ExactLinkGroup Value}
    (realization : Bond.PeriodicBondGaugeRealization n Value group)
    site direction →
  Bond.pathHolonomy realization site (direction ∷ [])
  ≡ Bond.orientedLink realization site direction
singletonHolonomy {group = group} realization site direction =
  Bond.identityRight group (Bond.orientedLink realization site direction)

orientedLinkOpposite :
  ∀ {n Value} {group : Bond.ExactLinkGroup Value}
    (stepLaws : Covariance.PeriodicStepInverseLaws n)
    (realization : Bond.PeriodicBondGaugeRealization n Value group)
    site direction →
  Bond.orientedLink realization (Bond.walkStep site direction)
    (oppositeDirection direction)
  ≡ Bond.inverse group (Bond.orientedLink realization site direction)
orientedLinkOpposite {group = group} stepLaws realization site
  (pair axis true) =
  cong (Bond.inverse group)
    (cong
      (λ base → Bond.bondField realization (pair base axis))
      (Covariance.negativeAfterPositive stepLaws site axis))
orientedLinkOpposite {group = group} stepLaws realization site
  (pair axis false) =
  sym (Bond.inverseInverse group
    (Bond.bondField realization (pair (Bond.negativeStep site axis) axis)))

holonomyAppend :
  ∀ {n Value} {group : Bond.ExactLinkGroup Value}
    (realization : Bond.PeriodicBondGaugeRealization n Value group)
    site left right →
  Bond.pathHolonomy realization site (left ++ right)
  ≡ Bond.multiply group
      (Bond.pathHolonomy realization site left)
      (Bond.pathHolonomy realization (Bond.walk site left) right)
holonomyAppend {group = group} realization site [] right =
  sym (Bond.identityLeft group
    (Bond.pathHolonomy realization site right))
holonomyAppend {group = group} realization site
  (direction ∷ directions) right =
  trans
    (cong
      (Bond.multiply group (Bond.orientedLink realization site direction))
      (holonomyAppend realization
        (Bond.walkStep site direction) directions right))
    (sym (Bond.multiplyAssociative group
      (Bond.orientedLink realization site direction)
      (Bond.pathHolonomy realization
        (Bond.walkStep site direction) directions)
      (Bond.pathHolonomy realization
        (Bond.walk (Bond.walkStep site direction) directions) right)))

pathHolonomyReverseOpposite :
  ∀ {n Value} {group : Bond.ExactLinkGroup Value}
    (stepLaws : Covariance.PeriodicStepInverseLaws n)
    (realization : Bond.PeriodicBondGaugeRealization n Value group)
    site directions →
  Bond.pathHolonomy realization (Bond.walk site directions)
    (reverseOpposite directions)
  ≡ Bond.inverse group (Bond.pathHolonomy realization site directions)
pathHolonomyReverseOpposite {group = group} stepLaws realization site [] =
  sym (inverseIdentity group)
pathHolonomyReverseOpposite {group = group} stepLaws realization site
  (direction ∷ directions) =
  trans
    (holonomyAppend realization
      (Bond.walk (Bond.walkStep site direction) directions)
      (reverseOpposite directions)
      (oppositeDirection direction ∷ []))
    (trans
      (cong₂ (Bond.multiply group)
        (pathHolonomyReverseOpposite stepLaws realization
          (Bond.walkStep site direction) directions)
        (trans
          (cong
            (λ start → Bond.pathHolonomy realization start
              (oppositeDirection direction ∷ []))
            (walkReverseOpposite stepLaws
              (Bond.walkStep site direction) directions))
          (trans
            (singletonHolonomy realization
              (Bond.walkStep site direction) (oppositeDirection direction))
            (orientedLinkOpposite stepLaws realization site direction))))
      (sym (Bond.inverseProduct group
        (Bond.orientedLink realization site direction)
        (Bond.pathHolonomy realization
          (Bond.walkStep site direction) directions))))

pathFollowedByReverseHasIdentityHolonomy :
  ∀ {n Value} {group : Bond.ExactLinkGroup Value}
    (stepLaws : Covariance.PeriodicStepInverseLaws n)
    (realization : Bond.PeriodicBondGaugeRealization n Value group)
    site directions →
  Bond.pathHolonomy realization site
    (directions ++ reverseOpposite directions)
  ≡ Bond.identity group
pathFollowedByReverseHasIdentityHolonomy {group = group}
  stepLaws realization site directions =
  trans
    (holonomyAppend realization site directions
      (reverseOpposite directions))
    (trans
      (cong
        (Bond.multiply group (Bond.pathHolonomy realization site directions))
        (pathHolonomyReverseOpposite stepLaws realization site directions))
      (Bond.inverseRight group
        (Bond.pathHolonomy realization site directions)))

record TransportedSixFaceBoundaryDecomposition
    (n : Agda.Builtin.Nat.Nat)
    (Value : Set)
    (group : Bond.ExactLinkGroup Value)
    (realization : Bond.PeriodicBondGaugeRealization n Value group) : Set₁ where
  field
    cubeBase : Periodic.PeriodicBlock n
    cancellationHalf : List SignedAxis4
    transportedSixFaceBoundary : List SignedAxis4
    transportedFacesFormCancellableBoundary :
      transportedSixFaceBoundary
      ≡ cancellationHalf ++ reverseOpposite cancellationHalf

open TransportedSixFaceBoundaryDecomposition public

latticeBianchiFromTransportedFaceDecomposition :
  ∀ {n Value} {group : Bond.ExactLinkGroup Value}
    {realization : Bond.PeriodicBondGaugeRealization n Value group} →
  (stepLaws : Covariance.PeriodicStepInverseLaws n) →
  (decomposition : TransportedSixFaceBoundaryDecomposition
    n Value group realization) →
  Bond.pathHolonomy realization
    (cubeBase decomposition)
    (transportedSixFaceBoundary decomposition)
  ≡ Bond.identity group
latticeBianchiFromTransportedFaceDecomposition
  stepLaws decomposition =
  subst
    (λ boundary →
      Bond.pathHolonomy _ (cubeBase decomposition) boundary
      ≡ Bond.identity _)
    (sym (transportedFacesFormCancellableBoundary decomposition))
    (pathFollowedByReverseHasIdentityHolonomy
      stepLaws _ (cubeBase decomposition) (cancellationHalf decomposition))

periodicPathReverseGeometryLevel : ProofLevel
periodicPathReverseGeometryLevel = machineChecked

orientedLinkInverseTraversalLevel : ProofLevel
orientedLinkInverseTraversalLevel = machineChecked

pathHolonomyInverseLevel : ProofLevel
pathHolonomyInverseLevel = machineChecked

transportedBianchiCancellationLevel : ProofLevel
transportedBianchiCancellationLevel = machineChecked

literalSixTransportedFaceDecompositionInputsLevel : ProofLevel
literalSixTransportedFaceDecompositionInputsLevel = conditional
