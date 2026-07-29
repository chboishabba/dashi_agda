module DASHI.Physics.YangMills.BalabanClayGate4PeriodicTraversalGeometryReuseExact where

open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT2PeriodicTraversalDecoderExact as Decoder
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond

------------------------------------------------------------------------
-- Repository-specific finite geometry.  The conventional link reversal is
-- standard; the actual proof below reuses DASHI's exact cyclic-coordinate laws.
--
-- Michael Creutz, "Quarks, Gluons and Lattices", Cambridge University Press,
-- open-access reissue (2022). DOI: 10.1017/9781009290395.
------------------------------------------------------------------------

periodicDirectionInverseLaw : ∀ n → Decoder.DirectionInverseLaw n
periodicDirectionInverseLaw n = record
  { Decoder.DirectionInverseLaw.forwardThenReverse =
      λ { block (pair axis Agda.Builtin.Bool.true) →
            Geometry.negativeAfterPositiveBlock block axis
        ; block (pair axis Agda.Builtin.Bool.false) →
            Geometry.positiveAfterNegativeBlock block axis
        }
  }

periodicSingleEdgeReturns :
  ∀ {n} block direction →
  Decoder.replayTerminal block
    (direction Decoder.∷ Decoder.reverseDirection direction Decoder.∷ Decoder.[])
  ≡ block
periodicSingleEdgeReturns {n} =
  Decoder.singleEdgeReturns (periodicDirectionInverseLaw n)

periodicTraversalDirectionInverseLevel : ProofLevel
periodicTraversalDirectionInverseLevel = machineChecked

periodicSingleEdgeReturnLevel : ProofLevel
periodicSingleEdgeReturnLevel = machineChecked
