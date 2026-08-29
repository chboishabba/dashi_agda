module DASHI.Physics.YangMills.BalabanWilsonTransferIntertwinerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Martin Lüscher,
-- "Construction of a Selfadjoint, Strictly Positive Transfer Matrix for
-- Euclidean Lattice Gauge Theories", Communications in Mathematical Physics
-- 54 (1977), 283--292. DOI: 10.1007/BF01614090.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- Volker Bach, Thomas Chen, Jürg Fröhlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- DASHI CONTRIBUTION
--
-- Replace the historical Boolean W5 compatibility surface by the actual
-- equation needed by the direct-transfer programme.  A compatibility witness
-- carries one fine observable space, one coarse observable space, their two
-- transfer evolutions, the coarse-to-fine lift, and the literal intertwining
-- equation
--
--     lift (T_coarse f) = T_fine (lift f).
--
-- This is strictly stronger than a receipt saying "compatibility = true".
-- It is also compositional: once the source-facing theorem is proved at each
-- Bałaban step, compatibility at arbitrary finite depth follows without a new
-- physical assumption.
--
-- We then weld this transfer equation to the already-existing exact OS
-- pullback structure.  Reflection positivity and transfer intertwining remain
-- distinct fields on the SAME blocking step; neither is inferred from the
-- other.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.FiniteReflectionPositivity as RP
import DASHI.Physics.YangMills.ReflectionPositiveBlocking as Block
import DASHI.Physics.YangMills.BalabanWilsonTransferBlockingExact as WilsonBlock

record TransferIntertwiner (Fine Coarse : Set) : Set₁ where
  field
    liftObservable : Coarse → Fine
    fineTransfer : Fine → Fine
    coarseTransfer : Coarse → Coarse
    intertwines :
      ∀ coarse →
      liftObservable (coarseTransfer coarse)
      ≡ fineTransfer (liftObservable coarse)

open TransferIntertwiner public

composeTransferIntertwiner :
  ∀ {Fine Middle Coarse : Set} →
  TransferIntertwiner Fine Middle →
  TransferIntertwiner Middle Coarse →
  TransferIntertwiner Fine Coarse
composeTransferIntertwiner first second = record
  { liftObservable =
      λ coarse →
        liftObservable first (liftObservable second coarse)
  ; fineTransfer = fineTransfer first
  ; coarseTransfer = coarseTransfer second
  ; intertwines = λ coarse →
      trans
        (cong (liftObservable first) (intertwines second coarse))
        (intertwines first (liftObservable second coarse))
  }

composedTransferLiftExact :
  ∀ {Fine Middle Coarse : Set}
    (first : TransferIntertwiner Fine Middle)
    (second : TransferIntertwiner Middle Coarse)
    coarse →
  liftObservable (composeTransferIntertwiner first second) coarse
  ≡ liftObservable first (liftObservable second coarse)
composedTransferLiftExact first second coarse = refl

------------------------------------------------------------------------
-- Same-step OS + transfer package.
------------------------------------------------------------------------

record ReflectionPositiveTransferBlocking
    (Fine Coarse Scalar : Set)
    (scalar : RP.PositiveAdditiveScalar Scalar)
    (fineRP : RP.FiniteReflectionPositive Fine Scalar scalar) : Set₁ where
  field
    osBlocking :
      Block.ReflectionPositiveBlocking Fine Coarse Scalar scalar fineRP
    transferIntertwiner :
      TransferIntertwiner Fine Coarse

open ReflectionPositiveTransferBlocking public

composeReflectionPositiveTransferBlocking :
  ∀ {Fine Middle Coarse Scalar : Set}
    {scalar : RP.PositiveAdditiveScalar Scalar}
    {fineRP : RP.FiniteReflectionPositive Fine Scalar scalar}
    (first :
      ReflectionPositiveTransferBlocking
        Fine Middle Scalar scalar fineRP)
    (second :
      ReflectionPositiveTransferBlocking
        Middle Coarse Scalar scalar
        (Block.blockedReflectionPositive (osBlocking first))) →
  ReflectionPositiveTransferBlocking Fine Coarse Scalar scalar fineRP
composeReflectionPositiveTransferBlocking first second = record
  { osBlocking =
      WilsonBlock.composeReflectionPositiveBlocking
        (osBlocking first)
        (osBlocking second)
  ; transferIntertwiner =
      composeTransferIntertwiner
        (transferIntertwiner first)
        (transferIntertwiner second)
  }

coarseReflectionPositivityFromDirectTransferStep :
  ∀ {Fine Coarse Scalar : Set}
    {scalar : RP.PositiveAdditiveScalar Scalar}
    {fineRP : RP.FiniteReflectionPositive Fine Scalar scalar}
    (step :
      ReflectionPositiveTransferBlocking
        Fine Coarse Scalar scalar fineRP) →
  RP.FiniteReflectionPositive Coarse Scalar scalar
coarseReflectionPositivityFromDirectTransferStep step =
  Block.blockedReflectionPositive (osBlocking step)

transferIntertwinerCompositionLevel : ProofLevel
transferIntertwinerCompositionLevel = machineChecked

osAndTransferSameStepCompositionLevel : ProofLevel
osAndTransferSameStepCompositionLevel = machineChecked

literalBalabanWilsonOneStepTransferIntertwinerLevel : ProofLevel
literalBalabanWilsonOneStepTransferIntertwinerLevel = conditional

historicalBooleanW5IsNotThisEquationLevel : ProofLevel
historicalBooleanW5IsNotThisEquationLevel = conjectural
