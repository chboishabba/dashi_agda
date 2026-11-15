module DASHI.Physics.QFT.NeutrinoHornedExteriorFifthPowerNoGoExact where

------------------------------------------------------------------------
-- CROSS-PR MAX-CUT: UNBOUNDED MERIDIAN ORDER IS NOT THE SAME
-- AS INFINITE-ORDER COMPLEX PMNS RESIDUAL PRODUCT.
--
-- ORIGINAL CLASSICAL SOURCES
-- J. W. Alexander (1924), wild/horned sphere.
-- A. Hatcher, Algebraic Topology, Example 2B.2, free-group tower,
--   injective commutator substitutions and perfectness of the limit.
-- N. W. Riebe (1968), representations of related horned spheres:
--   DOI 10.26076/c3c1-48f0 (NOT independent rediscovery of Hatcher).
--
-- RELATED EXISTING SOURCE PR #1244, separate unmerged branch:
--   DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact
--   DASHI.Mathematics.Topology.AlexanderHornedC3CharactersExact
--   DASHI.Mathematics.Topology.AlexanderHornedC3VOAKernelBidiExact
--   Docs/topology/AlexanderHornedC3VOARealizationMaxCut.md
--   The algebraic 3-sector group G has infinite-order meridian m,
--   r in Aut(G) with r^3=1 but r NOT internal order-three element.
--   The selected quotient q:G -> A5^3 sends m to element of order 5.
--   Consequently q(m^5)=1 although m^5 != 1 in G.
--
-- EXISTING SOURCE PR #1247 (THIS BRANCH):
--   NeutrinoExistingCPSectorLeptonBridgeExact: CP-nonzero 3x3 U.
--   NeutrinoExistingCPFiniteResidualNoGoExact: T*S1 has infinite
--   order by a noninteger relative Galois trace, invoking standard
--   external algebraic-integer results NOT proved in Agda.
--
-- NEW ORIGINAL CONTRIBUTION:
-- A generic transport POWER-FIVE theorem, with a contradiction
-- whenever the horn meridian is represented through the SELECTED
-- A5^3 quotient but is required to map to the infinite-order T*S1.
-- The theorem is conditional on a declared representation
-- homomorphism and the nonidentity of the target fifth power.
-- The new independent exact rational matrix audit calculates
-- the fifth power explicitly, without an analytic approximation.
--
-- No horn-complement geometric pi1 theorem imported across branches;
-- no finite-VOA or Monster action is identified with PMNS dynamics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; trans; sym)

power : {A : Set} →
  (A → A → A) → A → A → Nat → A
power multiply identity x zero = identity
power multiply identity x (suc n) =
  multiply x (power multiply identity x n)

-- The actor here is the image of the HATCHER MERIDIAN in the
-- A5^3 quotient, not the abstract torsion-free source group.
record SelectedFiniteHornActorTransfer : Set₁ where
  field
    FiniteActor : Set
    MatrixCarrier : Set
    actorIdentity : FiniteActor
    actorMultiply : FiniteActor → FiniteActor → FiniteActor
    selectedQuotientMeridian : FiniteActor
    actorMeridianFifthPowerIsIdentity :
      power actorMultiply actorIdentity
        selectedQuotientMeridian 5 ≡ actorIdentity

    matrixIdentity : MatrixCarrier
    matrixMultiply : MatrixCarrier → MatrixCarrier → MatrixCarrier
    actorToMatrix : FiniteActor → MatrixCarrier
    actorToMatrixIdentity :
      actorToMatrix actorIdentity ≡ matrixIdentity
    actorToMatrixMultiply : ∀ a b →
      actorToMatrix (actorMultiply a b) ≡
        matrixMultiply (actorToMatrix a) (actorToMatrix b)

    candidateTS : MatrixCarrier
    meridianIsCandidateTS :
      actorToMatrix selectedQuotientMeridian ≡ candidateTS

    candidateTSFifthPowerNotIdentity :
      power matrixMultiply matrixIdentity candidateTS 5
        ≡ matrixIdentity → ⊥

open SelectedFiniteHornActorTransfer public

actorPowerTransport :
  (bridge : SelectedFiniteHornActorTransfer) →
  (a : FiniteActor bridge) (n : Nat) →
  actorToMatrix bridge
    (power (actorMultiply bridge) (actorIdentity bridge) a n)
  ≡
  power (matrixMultiply bridge) (matrixIdentity bridge)
    (actorToMatrix bridge a) n
actorPowerTransport bridge a zero =
  actorToMatrixIdentity bridge
actorPowerTransport bridge a (suc n) =
  trans
    (actorToMatrixMultiply bridge a
      (power (actorMultiply bridge) (actorIdentity bridge) a n))
    (cong
      (matrixMultiply bridge (actorToMatrix bridge a))
      (actorPowerTransport bridge a n))

selectedFiniteHornQuotientCannotGiveInfiniteOrderTS :
  SelectedFiniteHornActorTransfer → ⊥
selectedFiniteHornQuotientCannotGiveInfiniteOrderTS bridge =
  candidateTSFifthPowerNotIdentity bridge
    (trans
      (sym
        (cong
          (λ x →
            power (matrixMultiply bridge) (matrixIdentity bridge) x 5)
          (meridianIsCandidateTS bridge)))
      (trans
        (sym
          (actorPowerTransport bridge
            (selectedQuotientMeridian bridge) 5))
        (trans
          (cong (actorToMatrix bridge)
            (actorMeridianFifthPowerIsIdentity bridge))
          (actorToMatrixIdentity bridge))))

------------------------------------------------------------------------
-- INTERPRETATION / NONPROMOTION
--
-- 1. G horned source perfect + torsion free:
--    every nonidentity meridian infinite order, no nontrivial
--    homomorphism G->C3 / U1 / other abelian target.
-- 2. r in Aut(G) (and [r] in Out(G)) order 3:
--    NOT an element of order 3 INSIDE G.
-- 3. The external extension G ⋊_r C3 does contain a genuine
--    order-3 element (1,r), and HAS a C3 quotient.
-- 4. A5^3 finite action/VOA sees q(m) of order 5 but kills m^5.
--    It CANNOT host TS with TS^5 != I as its selected meridian.
-- 5. A DIFFERENT infinite-image/nonabelian SU(3) representation
--    of G is not excluded by this finite-quotient argument.
--    It requires explicit commutator-tower compatibility and
--    r-equivariant intertwining on the SAME Hilbert space.
-- 6. Source-written conditional proof != Agda kernel receipt.
------------------------------------------------------------------------
