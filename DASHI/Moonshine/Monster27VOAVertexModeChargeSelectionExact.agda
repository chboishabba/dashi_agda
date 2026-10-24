module DASHI.Moonshine.Monster27VOAVertexModeChargeSelectionExact where

-- Source-specific *uninhabited* completion interface on SAME genuine
-- Moonshine VOA literal action, selected 3B and order27 parent.
-- The group automorphism axiom implies vertex-mode charge additivity.
-- This interface demands the actual mode/sector intertwiner, preserving
-- the old twisted-VOA construction obligations; it does not manufacture it.
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ)
open import Data.Product using (Σ; _,_)
open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (Trit; pos; zer; []; _∷_)

import DASHI.Moonshine.VertexOperatorAlgebraCore as Core
import DASHI.Moonshine.MonsterGradedVOALiteralActionSameObjectBidiExact as Weld
import DASHI.Moonshine.MonsterGradedVOASelected3BSameElementBidiExact as Selected
import DASHI.Moonshine.Monster27VOAOnsiteCube369BridgeExact as Parent
import DASHI.Moonshine.JInvariant369Cube27CuspCodecNonIsometryExact as Chart
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic

record LiteralMonster27ModeChargeReceipt
  {Monster K : Set}
  (source : Parent.Monster27VOAOnCubeSource Monster K) : Setω where
  field
    -- This is precisely the selected SAME literal VOA, NOT a generic
    -- newly invented graded carrier.
    Sector : Q.Residue3Pow 3 → Set

    embed :
      ∀ charge → Sector charge →
      Core.GradedModule.Carrier
        (Core.VertexOperatorAlgebra.gradedModule
          (Core.MoonshineVOABridge.voa
            (Weld.literalVOA
              (Selected.weld (Parent.selected3B source)))))

    generatorPhase :
      Q.Residue3Pow 3 →
      Core.GradedModule.Scalar
        (Core.VertexOperatorAlgebra.gradedModule
          (Core.MoonshineVOABridge.voa
            (Weld.literalVOA
              (Selected.weld (Parent.selected3B source)))))

    -- Vertex mode charge is cyclic ADDITION of already source-owned
    -- balanced ternary digits; this proves which operator is needed
    -- to connect adjacent cube charge sectors.
    actualVOAModeChargeOutput :
      ∀ left right (u : Sector left) (v : Sector right) (n : ℤ) →
      Σ (Sector (Arithmetic.addResidue left right))
        (λ out →
          embed (Arithmetic.addResidue left right) out
          ≡ Core.VertexOperatorData.mode
              (Core.VertexOperatorAlgebra.vertexData
                (Core.MoonshineVOABridge.voa
                  (Weld.literalVOA
                    (Selected.weld (Parent.selected3B source)))))
              (embed left u) n (embed right v))

open LiteralMonster27ModeChargeReceipt public

-- Concrete *spatial* cube x/y/z positive-axis neighbour charge
-- increments in the chosen signed-digit chart are exactly +1,+3,+9.
-- A physical link between two different charge sectors needs a
-- corresponding charged vertex mode or an independent gauge link.
positiveXCharge : Q.Residue3Pow 3
positiveXCharge = pos ∷ zer ∷ zer ∷ []

positiveYCharge : Q.Residue3Pow 3
positiveYCharge = zer ∷ pos ∷ zer ∷ []

positiveZCharge : Q.Residue3Pow 3
positiveZCharge = zer ∷ zer ∷ pos ∷ []

positiveXAxisSite :
  Chart.encodeCubeDigits
    (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero)
  ≡ positiveXCharge
positiveXAxisSite = refl

positiveYAxisSite :
  Chart.encodeCubeDigits
    (Cube.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero)
  ≡ positiveYCharge
positiveYAxisSite = refl

positiveZAxisSite :
  Chart.encodeCubeDigits
    (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne)
  ≡ positiveZCharge
positiveZAxisSite = refl

-- The actual g-twisted module W(g) and its modular S/T multipliers
-- are *another* existing owner: TwistedModuleModularity.agda.
-- Ordinary untwisted eigenspaces of V^natural are not g-twisted modules.
