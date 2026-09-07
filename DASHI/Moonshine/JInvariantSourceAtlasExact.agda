module DASHI.Moonshine.JInvariantSourceAtlasExact where

------------------------------------------------------------------------
-- REVISION-PINNED J-INVARIANT SOURCE ATLAS
--
-- Attribution policy follows DASHI.Core.ProofDebtRouterExact:
-- source identity, exact source claim, local transcription, and kernel proof
-- are separate coordinates.  The inspected Wikipedia revision below is a
-- secondary reference carrier.  It is useful for exact statement discovery
-- and bibliographic routing, but it is not promoted into theorem proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofDebtRouterExact as Debt

------------------------------------------------------------------------
-- 1. Exact inspected carrier.
------------------------------------------------------------------------

wikipediaJInvariantRevision : Debt.SourceIdentity
wikipediaJInvariantRevision =
  Debt.source-identity
    "Wikipedia contributors"
    "j-invariant"
    "Wikipedia oldid 1367363754"
    "https://en.wikipedia.org/w/index.php?title=J-invariant&oldid=1367363754"
    "oldid=1367363754; page last edited 2026-08-02; inspected 2026-09-08"

------------------------------------------------------------------------
-- 2. Source-entitled claims transcribed from that exact revision.
--
-- These strings are provenance-bearing statement snapshots only.  No field
-- below contains an inhabitant of the corresponding analytic theorem.
------------------------------------------------------------------------

record JReferenceClaim : Set where
  constructor j-reference-claim
  field
    source : Debt.SourceIdentity
    exactSourceClaim : String
    localUseScope : String
    inspectedForExactClaim : Bool
    secondaryReferenceOnly : Bool

open JReferenceClaim public

jDefinitionClaim : JReferenceClaim
jDefinitionClaim =
  j-reference-claim wikipediaJInvariantRevision
    "j is a weight-zero modular function on the upper half-plane, invariant under the modular group, with j(exp(2*pi*i/3)) = 0 and j(i) = 1728."
    "statement discovery for the modular quotient / symmetry carrier"
    true true

jG2G3FormulaClaim : JReferenceClaim
jG2G3FormulaClaim =
  j-reference-claim wikipediaJInvariantRevision
    "j(tau) = 1728*g2(tau)^3/(g2(tau)^3 - 27*g3(tau)^2)."
    "exact formula snapshot; no local complex-analysis proof supplied here"
    true true

jThetaTripleClaim : JReferenceClaim
jThetaTripleClaim =
  j-reference-claim wikipediaJInvariantRevision
    "For a=theta2, b=theta3, c=theta4 with a^4-b^4+c^4=0, j = 32*(a^8+b^8+c^8)^3/(abc)^8."
    "three-theta-coordinate source snapshot; visual trivalence is not identified with this theorem"
    true true

jLambdaSixOrbitClaim : JReferenceClaim
jLambdaSixOrbitClaim =
  j-reference-claim wikipediaJInvariantRevision
    "j is unchanged when lambda is replaced by any of: lambda, 1/(1-lambda), (lambda-1)/lambda, 1/lambda, lambda/(lambda-1), 1-lambda."
    "six-label modular-lambda orbit used only for finite indexing and source-alignment demand"
    true true

jBelyiBranchClaim : JReferenceClaim
jBelyiBranchClaim =
  j-reference-claim wikipediaJInvariantRevision
    "The branch points of j are at {0,1,infinity}, so j is a Belyi function."
    "three-branch-point source snapshot; no identification with Base369 geometry"
    true true

jMoonshineClaim : JReferenceClaim
jMoonshineClaim =
  j-reference-claim wikipediaJInvariantRevision
    "Positive q-expansion coefficients of j are dimensions of graded parts of the moonshine module for the Monster group; the q coefficient is 196884."
    "bibliographic / representation-theoretic routing only"
    true true

------------------------------------------------------------------------
-- 3. Bibliographic pointers exposed by the inspected reference.
--
-- These have NOT been inspected here for the exact theorem statements, so
-- they remain pointers rather than source-entitled theorem carriers.
------------------------------------------------------------------------

record UninspectedBibliographicPointer : Set where
  constructor uninspected-bibliographic-pointer
  field
    responsibleAuthor : String
    title : String
    stableIdentifier : String
    citedFor : String
    inspectedForExactClaim : Bool

open UninspectedBibliographicPointer public

chandrasekharanLambdaPointer : UninspectedBibliographicPointer
chandrasekharanLambdaPointer =
  uninspected-bibliographic-pointer
    "K. Chandrasekharan"
    "Elliptic Functions"
    "ISBN 978-3-540-15295-8; Springer Grundlehren 281, p.110"
    "the six modular-lambda replacements leaving j unchanged"
    false

conwayNortonMoonshinePointer : UninspectedBibliographicPointer
conwayNortonMoonshinePointer =
  uninspected-bibliographic-pointer
    "John H. Conway and Simon P. Norton"
    "Monstrous moonshine"
    "DOI 10.1112/blms/11.3.308"
    "Monster / genus-zero modular-function background"
    false

------------------------------------------------------------------------
-- 4. Attribution and proof-debt firewall.
------------------------------------------------------------------------

record JSourceAttributionBoundary : Set where
  constructor j-source-attribution-boundary
  field
    inspectedRevisionPinned : Bool
    exactSourceClaimStored : Bool
    secondaryReferenceIsPrimaryInspection : Bool
    bibliographicPointerIsInspectedTheorem : Bool
    visualPatternIsSourceEntitledClaim : Bool
    sourceClaimAutomaticallyCreatesKernelProof : Bool
    monsterConnectionAutomaticallyExplainsBase369 : Bool
    rhAutomaticallyProvesJInvariant : Bool

canonicalJSourceAttributionBoundary : JSourceAttributionBoundary
canonicalJSourceAttributionBoundary =
  j-source-attribution-boundary true true false false false false false false

secondaryReferenceDoesNotPromotePrimaryInspection :
  JSourceAttributionBoundary.secondaryReferenceIsPrimaryInspection
    canonicalJSourceAttributionBoundary ≡ false
secondaryReferenceDoesNotPromotePrimaryInspection = refl

visualPatternDoesNotBecomeSourceClaim :
  JSourceAttributionBoundary.visualPatternIsSourceEntitledClaim
    canonicalJSourceAttributionBoundary ≡ false
visualPatternDoesNotBecomeSourceClaim = refl
