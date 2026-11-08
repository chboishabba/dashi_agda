module DASHI.Moonshine.VNaturalOriginalPairedFourSectorModesExact where

------------------------------------------------------------------------
-- ORIGINAL FLM-STYLE PAIRED ORBIFOLD: SOURCE-OWNED FOUR-BLOCK MODES
--
-- The legacy tagged A ⊎ B cannot be a LINEAR two-summand VOA because
-- its original fixed/twisted zero embeddings are disjoint (proved in
-- VNaturalOrbifoldConstruction). Work instead on the existing *correct*
-- paired graded module A × B = A ⊕ B (as underlying set).
--
-- Strongest reuse:
--  FF = actual mode of original fixedPoint.fixedVOA (NOT a chosen op);
--  FT = actual Leech theta-twisted module action restricted to the
--       selected twisted-even sector (with a necessary closure witness);
--  TF = genuinely selected twisted/fixed intertwining source;
--  TT = genuinely selected twisted/twisted -> fixed intertwiner.
--
-- Construct all modes in the SAME paired graded carrier, with no
-- invented Griess product and no arbitrary tagged sum.
--
-- WHAT IS NOT AUTOMATIC: TT/TF intertwiners, sector grading of modes,
-- skew symmetry, locality/Jacobi, central charge and algebraic
-- nontriviality. These must be proved on actual Leech sources.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN

module Selected (construction : VN.VNaturalConstruction)
                (source :
                  VN.SelectedPairedGradedModule.OriginalFixedVOAAndTwistedEvenSource
                    construction) where

  module N = VN.SelectedPairedGradedModule construction

  grading : N.SourceSectorGrading
  grading = N.nativeFixedAndTwistedGrading source

  Fixed : Set
  Fixed = N.Fixed

  Twisted : Set
  Twisted = N.Twisted

  originalFixedVOA : VOA.VertexOperatorAlgebra
  originalFixedVOA = VN.FixedPointVOA.fixedVOA N.fixed

  fixedY : VOA.VertexOperatorData N.fixedGM
  fixedY = VOA.VertexOperatorAlgebra.vertexData originalFixedVOA

  fixedMode : Fixed → ℤ → Fixed → Fixed
  fixedMode a n b =
    N.fixedFromOriginal source
      (VOA.VertexOperatorData.mode fixedY
        (N.fixedToOriginal source a) n
        (N.fixedToOriginal source b))

  fixedModeIsOriginal : (a : Fixed) (n : ℤ) (b : Fixed) →
    N.fixedToOriginal source (fixedMode a n b)
    ≡ VOA.VertexOperatorData.mode fixedY
        (N.fixedToOriginal source a) n
        (N.fixedToOriginal source b)
  fixedModeIsOriginal a n b =
    N.fixedOriginalAfterFrom source
      (VOA.VertexOperatorData.mode fixedY
        (N.fixedToOriginal source a) n
        (N.fixedToOriginal source b))

  record OriginalMixedSectorIntertwiners : Setω where
    field
      -- A selected INTEGER mode corresponds to an actual theta-twisted
      -- index. Do not silently coerce integers to half-integer modes.
      originalTwistIndex : ℤ → VN.TwistedModule.TwistIndex N.twisted

      fixedTwisted : Fixed → ℤ → Twisted → Twisted
      fixedTwistedIsOriginal : (a : Fixed) (n : ℤ) (t : Twisted) →
        VN.TwistedEvenSector.includePlus N.plus (fixedTwisted a n t)
        ≡ VN.TwistedModule.twistedMode N.twisted
            (VN.FixedPointVOA.includeFixed N.fixed a)
            (originalTwistIndex n)
            (VN.TwistedEvenSector.includePlus N.plus t)

      -- The other two blocks require genuine original intertwining
      -- operators. Ordinary twisted-module action only supplies FT.
      twistedFixed : Twisted → ℤ → Fixed → Twisted
      twistedTwisted : Twisted → ℤ → Twisted → Fixed
      twistedTranslation : Twisted → Twisted

  open OriginalMixedSectorIntertwiners public

  pairedCarrier : Set
  pairedCarrier = VN.LinearOrbifoldCarrier N.fixed N.twisted N.plus

  pairedMode :
    OriginalMixedSectorIntertwiners →
    pairedCarrier → ℤ → pairedCarrier → pairedCarrier
  pairedMode blocks (a , t) n (b , s) =
    N.fixedAdd grading
      (fixedMode a n b)
      (twistedTwisted blocks t n s) ,
    N.twistedAdd grading
      (fixedTwisted blocks a n s)
      (twistedFixed blocks t n b)

  -- The constructor of every state/mode of the new vertex datum is tied
  -- to the ORIGINAL fixed-sector VOA plus the actual twisted source.
  pairedVertexData :
    OriginalMixedSectorIntertwiners →
    VOA.VertexOperatorData (N.actualSourceGradedPair source)
  pairedVertexData blocks = record
    { VOA.VertexOperatorData.vacuum =
        N.fixedFromOriginal source
          (VOA.VertexOperatorData.vacuum fixedY) ,
        N.twistedZeroOriginal source
    ; VOA.VertexOperatorData.conformalVector =
        N.fixedFromOriginal source
          (VOA.VertexOperatorData.conformalVector fixedY) ,
        N.twistedZeroOriginal source
    ; VOA.VertexOperatorData.mode = pairedMode blocks
    ; VOA.VertexOperatorData.translation = λ p →
        N.fixedFromOriginal source
          (VOA.VertexOperatorData.translation fixedY
            (N.fixedToOriginal source (proj₁ p))) ,
        twistedTranslation blocks (proj₂ p)
    }

  originalFFDecoded :
    (blocks : OriginalMixedSectorIntertwiners)
    (a b : Fixed) (n : ℤ) →
    N.fixedToOriginal source (fixedMode a n b)
    ≡ VOA.VertexOperatorData.mode fixedY
      (N.fixedToOriginal source a) n
      (N.fixedToOriginal source b)
  originalFFDecoded blocks a b n = fixedModeIsOriginal a n b

  exactFourBlockExpansion :
    (blocks : OriginalMixedSectorIntertwiners)
    (a b : Fixed) (t s : Twisted) (n : ℤ) →
    VOA.VertexOperatorData.mode (pairedVertexData blocks)
      (a , t) n (b , s)
    ≡
    (N.fixedAdd grading
      (fixedMode a n b)
      (twistedTwisted blocks t n s) ,
     N.twistedAdd grading
      (fixedTwisted blocks a n s)
      (twistedFixed blocks t n b))
  exactFourBlockExpansion blocks a b t s n = refl

  originalFTDecoded :
    (blocks : OriginalMixedSectorIntertwiners)
    (a : Fixed) (n : ℤ) (s : Twisted) →
    VN.TwistedEvenSector.includePlus N.plus
      (fixedTwisted blocks a n s)
    ≡ VN.TwistedModule.twistedMode N.twisted
      (VN.FixedPointVOA.includeFixed N.fixed a)
      (originalTwistIndex blocks n)
      (VN.TwistedEvenSector.includePlus N.plus s)
  originalFTDecoded blocks a n s =
    fixedTwistedIsOriginal blocks a n s
