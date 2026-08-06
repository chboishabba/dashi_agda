module DASHI.Physics.Common.SeparatingProbeFamilyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
-- Roger A. Horn and Charles R. Johnson, "Matrix Analysis", second edition.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
-- Matching totals are weaker than matching a separating family of local probes.
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
  rewrite agreement firstProbe | agreement secondProbe = refl

canonicalPairProbeSystem : SeparatingProbeSystem (Nat × Nat) Nat
canonicalPairProbeSystem =
  separatingProbeSystem PairProbe observePair pairProbesSeparate

data CrossDomainProbeKind : Set where
  characterValueProbe : CrossDomainProbeKind
  wilsonPlacementProbe : CrossDomainProbeKind
  navierStokesInteractionProbe : CrossDomainProbeKind
  hessianStencilProbe : CrossDomainProbeKind
