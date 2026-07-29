module DASHI.Physics.YangMills.BalabanClayGate4LiteralCubeBianchiExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (Axis4)
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact using (SignedAxis4)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact as Covariance
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact as Path
open Path using (_++_)

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
-- The ordered word below is the product
--   F_ab · T_b(F_ca^{-1}) · F_bc · T_c(F_ab^{-1})
--        · F_ca · T_a(F_bc^{-1}),
-- where T_d transports a shifted opposite face back to the common cube base.
-- Every oriented cube edge appears once with each orientation. The proof is
-- non-Abelian: the order and transports are part of the theorem statement.
------------------------------------------------------------------------

positiveDirection negativeDirection : Axis4 → SignedAxis4
positiveDirection = Bond.positiveDirection
negativeDirection = Bond.negativeDirection

faceBoundary : Axis4 → Axis4 → List SignedAxis4
faceBoundary firstAxis secondAxis =
  positiveDirection firstAxis ∷
  positiveDirection secondAxis ∷
  negativeDirection firstAxis ∷
  negativeDirection secondAxis ∷ []

transportedOppositeFace :
  Axis4 → List SignedAxis4 → List SignedAxis4
transportedOppositeFace transportAxis face =
  positiveDirection transportAxis ∷
  (Path.reverseOpposite face ++
    (negativeDirection transportAxis ∷ []))

cubeSixFaceBoundary : Axis4 → Axis4 → Axis4 → List SignedAxis4
cubeSixFaceBoundary axisA axisB axisC =
  faceBoundary axisA axisB ++
  transportedOppositeFace axisB (faceBoundary axisC axisA) ++
  faceBoundary axisB axisC ++
  transportedOppositeFace axisC (faceBoundary axisA axisB) ++
  faceBoundary axisC axisA ++
  transportedOppositeFace axisA (faceBoundary axisB axisC)

------------------------------------------------------------------------
-- Freely cancellable path words.
------------------------------------------------------------------------

data CancellableBoundary : List SignedAxis4 → Set where
  boundaryEmpty : CancellableBoundary []
  boundaryWrap : ∀ direction {inside rest} →
    CancellableBoundary inside →
    CancellableBoundary rest →
    CancellableBoundary
      (direction ∷
        (inside ++
          (Path.oppositeDirection direction ∷ rest)))

record BoundaryIdentity
    {n Value}
    {group : Bond.ExactLinkGroup Value}
    (realization : Bond.PeriodicBondGaugeRealization n Value group)
    (site : Periodic.PeriodicBlock n)
    (word : List SignedAxis4) : Set₁ where
  field
    boundaryCloses : Bond.walk site word ≡ site
    boundaryHolonomyIdentity :
      Bond.pathHolonomy realization site word ≡ Bond.identity group

open BoundaryIdentity public

wrappedTailHolonomy :
  ∀ {n Value} {group : Bond.ExactLinkGroup Value}
    (stepLaws : Covariance.PeriodicStepInverseLaws n)
    (realization : Bond.PeriodicBondGaugeRealization n Value group)
    site direction rest →
  BoundaryIdentity realization site rest →
  Bond.pathHolonomy realization (Bond.walkStep site direction)
    (Path.oppositeDirection direction ∷ rest)
  ≡ Bond.inverse group (Bond.orientedLink realization site direction)
wrappedTailHolonomy {group = group} stepLaws realization site direction rest
  restIdentity =
  trans
    (cong₂ (Bond.multiply group)
      (Path.orientedLinkOpposite stepLaws realization site direction)
      (subst
        (λ returnedSite →
          Bond.pathHolonomy realization returnedSite rest
          ≡ Bond.identity group)
        (sym (Path.walkOppositeStep stepLaws site direction))
        (boundaryHolonomyIdentity restIdentity)))
    (Bond.identityRight group
      (Bond.inverse group (Bond.orientedLink realization site direction)))

cancellableBoundaryIdentity :
  ∀ {n Value} {group : Bond.ExactLinkGroup Value}
    (stepLaws : Covariance.PeriodicStepInverseLaws n)
    (realization : Bond.PeriodicBondGaugeRealization n Value group)
    {word} →
  CancellableBoundary word →
  (site : Periodic.PeriodicBlock n) →
  BoundaryIdentity realization site word
cancellableBoundaryIdentity stepLaws realization boundaryEmpty site = record
  { BoundaryIdentity.boundaryCloses = refl
  ; BoundaryIdentity.boundaryHolonomyIdentity = refl
  }
cancellableBoundaryIdentity {group = group} stepLaws realization
  (boundaryWrap direction {inside = inside} {rest = rest}
    insideProof restProof) site =
  let
    stepped = Bond.walkStep site direction
    tail : List SignedAxis4
    tail = Path.oppositeDirection direction ∷ rest
    insideIdentity =
      cancellableBoundaryIdentity stepLaws realization insideProof stepped
    restIdentity =
      cancellableBoundaryIdentity stepLaws realization restProof site
    tailHolonomy =
      wrappedTailHolonomy stepLaws realization site direction rest restIdentity
  in record
  { BoundaryIdentity.boundaryCloses =
      trans
        (Path.walkAppend stepped inside tail)
        (trans
          (cong (λ intermediate → Bond.walk intermediate tail)
            (boundaryCloses insideIdentity))
          (trans
            (cong (λ intermediate → Bond.walk intermediate rest)
              (Path.walkOppositeStep stepLaws site direction))
            (boundaryCloses restIdentity)))
  ; BoundaryIdentity.boundaryHolonomyIdentity =
      trans
        (cong
          (Bond.multiply group
            (Bond.orientedLink realization site direction))
          (Path.holonomyAppend realization stepped inside tail))
        (trans
          (cong
            (Bond.multiply group
              (Bond.orientedLink realization site direction))
            (cong₂ (Bond.multiply group)
              (boundaryHolonomyIdentity insideIdentity)
              (subst
                (λ insideEnd →
                  Bond.pathHolonomy realization insideEnd tail
                  ≡ Bond.inverse group
                      (Bond.orientedLink realization site direction))
                (sym (boundaryCloses insideIdentity))
                tailHolonomy)))
          (trans
            (cong
              (Bond.multiply group
                (Bond.orientedLink realization site direction))
              (Bond.identityLeft group
                (Bond.inverse group
                  (Bond.orientedLink realization site direction))))
            (Bond.inverseRight group
              (Bond.orientedLink realization site direction))))
  }

------------------------------------------------------------------------
-- The literal six-face word is freely cancellable.
------------------------------------------------------------------------

literalCubeBoundaryCancellable : ∀ axisA axisB axisC →
  CancellableBoundary (cubeSixFaceBoundary axisA axisB axisC)
literalCubeBoundaryCancellable axisA axisB axisC =
  boundaryWrap (positiveDirection axisA)
    (boundaryWrap (positiveDirection axisB)
      (boundaryWrap (negativeDirection axisA)
        (boundaryWrap (negativeDirection axisB)
          boundaryEmpty
          boundaryEmpty)
        (boundaryWrap (positiveDirection axisC)
          (boundaryWrap (negativeDirection axisA)
            (boundaryWrap (negativeDirection axisC)
              (boundaryWrap (negativeDirection axisB)
                boundaryEmpty
                boundaryEmpty)
              (boundaryWrap (negativeDirection axisB)
                (boundaryWrap (negativeDirection axisC)
                  boundaryEmpty
                  boundaryEmpty)
                boundaryEmpty))
            (boundaryWrap (negativeDirection axisB)
              (boundaryWrap (negativeDirection axisA)
                (boundaryWrap (negativeDirection axisC)
                  boundaryEmpty
                  boundaryEmpty)
                (boundaryWrap (negativeDirection axisC)
                  (boundaryWrap (negativeDirection axisA)
                    boundaryEmpty
                    boundaryEmpty)
                  boundaryEmpty))
              boundaryEmpty))
          boundaryEmpty))
      boundaryEmpty)
    boundaryEmpty

literalCubeBoundaryIdentity :
  ∀ {n Value} {group : Bond.ExactLinkGroup Value}
    (stepLaws : Covariance.PeriodicStepInverseLaws n)
    (realization : Bond.PeriodicBondGaugeRealization n Value group)
    site axisA axisB axisC →
  BoundaryIdentity realization site
    (cubeSixFaceBoundary axisA axisB axisC)
literalCubeBoundaryIdentity stepLaws realization site axisA axisB axisC =
  cancellableBoundaryIdentity stepLaws realization
    (literalCubeBoundaryCancellable axisA axisB axisC) site

literalCubeBianchi :
  ∀ {n Value} {group : Bond.ExactLinkGroup Value}
    (stepLaws : Covariance.PeriodicStepInverseLaws n)
    (realization : Bond.PeriodicBondGaugeRealization n Value group)
    site axisA axisB axisC →
  Bond.pathHolonomy realization site
    (cubeSixFaceBoundary axisA axisB axisC)
  ≡ Bond.identity group
literalCubeBianchi stepLaws realization site axisA axisB axisC =
  boundaryHolonomyIdentity
    (literalCubeBoundaryIdentity
      stepLaws realization site axisA axisB axisC)

literalSixFaceBoundaryDefinitionLevel : ProofLevel
literalSixFaceBoundaryDefinitionLevel = machineChecked

cancellableBoundaryAlgebraLevel : ProofLevel
cancellableBoundaryAlgebraLevel = machineChecked

literalCubeBoundaryCancellationLevel : ProofLevel
literalCubeBoundaryCancellationLevel = machineChecked

literalCubeBianchiLevel : ProofLevel
literalCubeBianchiLevel = machineChecked
