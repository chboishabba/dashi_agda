module DASHI.Mathematics.Topology.AlexanderHornedBalancedTernaryRiemannSquareExact where

------------------------------------------------------------------------
-- Reuse-first horned C3 x balanced ternary x Riemann reflection square.
--
-- ORIGINAL OWNERS / DO NOT REPROVE:
-- Alexander (1924), Hatcher AT Example 2B.2 (binary HORN geometry);
-- Riemann (1859) and NIST DLMF 25.4 (completed xi reflection);
-- DASHI AlexanderHornedBinaryTernaryExistingCodecWeldExact (bit/trit);
-- DASHI RiemannXiSymmetryExact (rational complex coordinate laws);
-- DASHI C3RiemannConjugationBridgeExact (reflection/conjugation locus).
--
-- New contribution: full three-symbol *observer* over the two-child
-- horn tree, explicit lossy retraction, sector C3 commuting square,
-- independent zeta reflection square and fixed-centre witness.
-- No claim that trinary words are geometrical Hatcher meridians,
-- that the full C3 acts on the embedded nonzero trit subcarrier, or
-- that reflection symmetry proves RH.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as H
import DASHI.Mathematics.Topology.AlexanderHornedBinaryTernaryExistingCodecWeldExact as Codec
import DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact as Xi
import DASHI.Moonshine.C3RiemannConjugationBridgeExact as Zeta

-- The inherited Horn word has only two actual topological children.
-- The zero trit creates an additional OBSERVER choice, not a new horn.
embed : H.Bit → BT.Trit
embed H.left  = BT.neg
embed H.right = BT.pos

collapse : BT.Trit → H.Bit
collapse BT.neg  = H.left
collapse BT.zero = H.left
collapse BT.pos  = H.right

collapseEmbed : ∀ bit → collapse (embed bit) ≡ bit
collapseEmbed H.left = refl
collapseEmbed H.right = refl

-- This genuine collapse is not injective: it forgets a neutral fibre.
neutralCollision : collapse BT.neg ≡ collapse BT.zero
neutralCollision = refl

neutralIsNotNegative : BT.zero ≡ BT.neg → ⊥
neutralIsNotNegative ()

-- The actual existing codec agrees on the two literal horn symbols.
selectedHornBitIsCanonical :
  ∀ bit → Codec.tritAsHornBit (Codec.hornBitAsTrit bit) ≡ bit
selectedHornBitIsCanonical = Codec.hornBinaryInExistingBalancedTernaryRoundTrip

embedWord : List H.Bit → List BT.Trit
embedWord [] = []
embedWord (x ∷ xs) = embed x ∷ embedWord xs

collapseWord : List BT.Trit → List H.Bit
collapseWord [] = []
collapseWord (x ∷ xs) = collapse x ∷ collapseWord xs

collapseEmbedWord : ∀ w → collapseWord (embedWord w) ≡ w
collapseEmbedWord [] = refl
collapseEmbedWord (x ∷ xs)
  rewrite collapseEmbed x | collapseEmbedWord xs = refl

-- Newest-first storage from H is PRESERVED, not reinterpreted as
-- chronological; consumers must use the existing Bin.chronological.
record BalancedHornAddress : Set where
  constructor balanced-horn-address
  field
    sector : C3.C3
    tritsNewestFirst : List BT.Trit

embedAddress : H.HornAddress → BalancedHornAddress
embedAddress (H.address c w) = balanced-horn-address c (embedWord w)

collapseAddress : BalancedHornAddress → H.HornAddress
collapseAddress (balanced-horn-address c w) =
  H.address c (collapseWord w)

collapseEmbedAddress : ∀ a → collapseAddress (embedAddress a) ≡ a
collapseEmbedAddress (H.address c w)
  rewrite collapseEmbedWord w = refl

rotateBalanced : BalancedHornAddress → BalancedHornAddress
rotateBalanced (balanced-horn-address c w) =
  balanced-horn-address (H.rotateSector c) w

balancedAddressRotateSquare :
  ∀ a → rotateBalanced (embedAddress a) ≡
    embedAddress (H.rotateAddress a)
balancedAddressRotateSquare (H.address c w) = refl

-- The balanced sign involution fixes ZERO; it is NOT the external C3.
balancedReflect : BT.Trit → BT.Trit
balancedReflect = BT.negate

balancedReflectSquared : ∀ t → balancedReflect (balancedReflect t) ≡ t
balancedReflectSquared BT.neg = refl
balancedReflectSquared BT.zero = refl
balancedReflectSquared BT.pos = refl

-- Riemann's critical reflection is a different involution.
-- The commuting square below is a PRODUCT construction, not an
-- identification between the analytic zeta function and C3 phases.
record TernaryXiState : Set where
  constructor ternary-xi
  field
    externalSector : C3.C3
    balancedObserver : BT.Trit
    xiCoordinate : Xi.ComplexCoordinate

rotateState : TernaryXiState → TernaryXiState
rotateState (ternary-xi c t p) =
  ternary-xi (H.rotateSector c) t p

reflectState : TernaryXiState → TernaryXiState
reflectState (ternary-xi c t p) =
  ternary-xi c (balancedReflect t) (Xi.criticalReflection p)

rotationReflectionCommute :
  ∀ state → rotateState (reflectState state) ≡
    reflectState (rotateState state)
rotationReflectionCommute (ternary-xi c t p) = refl

stateRotateCubed :
  ∀ state → rotateState (rotateState (rotateState state)) ≡ state
stateRotateCubed (ternary-xi c t p) =
  cong (λ c' → ternary-xi c' t p) (H.rotateSectorCubed c)

stateReflectionSquared :
  ∀ state → reflectState (reflectState state) ≡ state
stateReflectionSquared (ternary-xi c BT.neg p) =
  cong (λ p' → ternary-xi c BT.neg p') (Xi.criticalReflectionInvolutive p)
stateReflectionSquared (ternary-xi c BT.zero p) =
  cong (λ p' → ternary-xi c BT.zero p') (Xi.criticalReflectionInvolutive p)
stateReflectionSquared (ternary-xi c BT.pos p) =
  cong (λ p' → ternary-xi c BT.pos p') (Xi.criticalReflectionInvolutive p)

-- The zero observer is exactly reflection-fixed ON the critical line.
-- This is a fixed-locus property, NOT "all zeta zeros on the line".
zeroObserverCriticalFixed :
  ∀ c p → Xi.CriticalLine p →
    reflectState (ternary-xi c BT.zero p) ≡
      ternary-xi c BT.zero p
zeroObserverCriticalFixed c p onLine =
  cong (λ p' → ternary-xi c BT.zero p')
    (Xi.criticalLineFixedByReflection p onLine)

-- The analytic coincidence proof is reused rather than rederived.
zetaReflectionConjugationOnCritical :
  ∀ p → Xi.CriticalLine p →
    Xi.functionalReflection p ≡ Xi.conjugateCoordinate p
zetaReflectionConjugationOnCritical =
  Zeta.criticalLineImpliesFunctionalEqualsConjugate
