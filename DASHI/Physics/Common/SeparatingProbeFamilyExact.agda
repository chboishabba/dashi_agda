module DASHI.Physics.Common.SeparatingProbeFamilyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Formalize the shared verification rule:
--
--   matching aggregate dimensions or constants is necessary but insufficient;
--   agreement on a separating family of local probes determines the object.
--
-- Intended instantiations include Monster character values on selected
-- conjugacy classes, sixteen Wilson placement atoms, Navier--Stokes HH/LH/HL/CC
-- classes and literal Hessian stencil rows.  This module supplies only the
-- domain-free exact principle.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

record SeparatingProbeSystem (Candidate Observation : Set) : Set₁ where
  constructor separatingProbeSystem
  field
    Probe : Set
    observe : Probe → Candidate → Observation
    probesSeparate :
      ∀ left right →
      ((probe : Probe) → observe probe left ≡ observe probe right) →
      left ≡ right

open SeparatingProbeSystem public

agreementOnSeparatingProbes :
  ∀ {Candidate Observation}
    (system : SeparatingProbeSystem Candidate Observation)
    left right →
  ((probe : Probe system) →
    observe system probe left ≡ observe system probe right) →
  left ≡ right
agreementOnSeparatingProbes system left right agreement =
  probesSeparate system left right agreement

data PairProbe : Set where
  firstProbe : PairProbe
  secondProbe : PairProbe

observePair : PairProbe → Nat × Nat → Nat
observePair firstProbe (first , second) = first
observePair secondProbe (first , second) = second

pairProbesSeparate :
  ∀ left right →
  ((probe : PairProbe) → observePair probe left ≡ observePair probe right) →
  left ≡ right
pairProbesSeparate (leftFirst , leftSecond) (rightFirst , rightSecond) agreement
  rewrite agreement firstProbe
        | agreement secondProbe = refl

canonicalPairProbeSystem : SeparatingProbeSystem (Nat × Nat) Nat
canonicalPairProbeSystem =
  separatingProbeSystem PairProbe observePair pairProbesSeparate

data CrossDomainProbeKind : Set where
  characterValueProbe : CrossDomainProbeKind
  wilsonPlacementProbe : CrossDomainProbeKind
  navierStokesInteractionProbe : CrossDomainProbeKind
  hessianStencilProbe : CrossDomainProbeKind
  restrictedExpressionProbe : CrossDomainProbeKind

record ProbeAuthorityBoundary : Set₁ where
  constructor probeAuthorityBoundary
  field
    matchingTotalsImplyMatchingObjects : Set
    matchingTotalsDoNotImplyMatchingObjects :
      matchingTotalsImplyMatchingObjects → Set

    separatingProbeFamilyStillNeedsDomainInstantiation : Set
    separatingProbeFamilyStillNeedsDomainInstantiationWitness :
      separatingProbeFamilyStillNeedsDomainInstantiation

canonicalProbeAuthorityBoundary : ProbeAuthorityBoundary
canonicalProbeAuthorityBoundary =
  probeAuthorityBoundary
    ⊥ (λ impossible → ⊥)
    ⊤ tt
  where
  open import Data.Empty using (⊥)
  open import Data.Unit using (⊤; tt)
