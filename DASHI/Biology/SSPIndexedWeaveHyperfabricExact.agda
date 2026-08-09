module DASHI.Biology.SSPIndexedWeaveHyperfabricExact where

open import DASHI.Core.Prelude

import DASHI.Core.IndexedWeaveHyperfabricExact as Indexed
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Biology.SSPHyperfibreSymmetryTowerExact as Tower

------------------------------------------------------------------------
-- The SSP weave is concretely an SSPPrime-indexed family.  Paths carry one
-- bit of transport parity.  Reverse paths flip the balanced lane state;
-- composing two reversals preserves it.  All category and action laws are
-- proved by finite case analysis.
------------------------------------------------------------------------

data LaneParity : Set where
  preserveParity : LaneParity
  reverseParity : LaneParity

composeParity : LaneParity → LaneParity → LaneParity
composeParity preserveParity parity = parity
composeParity reverseParity preserveParity = reverseParity
composeParity reverseParity reverseParity = preserveParity

composeParityIdLeft :
  (parity : LaneParity) →
  composeParity preserveParity parity ≡ parity
composeParityIdLeft preserveParity = refl
composeParityIdLeft reverseParity = refl

composeParityIdRight :
  (parity : LaneParity) →
  composeParity parity preserveParity ≡ parity
composeParityIdRight preserveParity = refl
composeParityIdRight reverseParity = refl

composeParityAssoc :
  (r q p : LaneParity) →
  composeParity (composeParity r q) p
  ≡ composeParity r (composeParity q p)
composeParityAssoc preserveParity preserveParity preserveParity = refl
composeParityAssoc preserveParity preserveParity reverseParity = refl
composeParityAssoc preserveParity reverseParity preserveParity = refl
composeParityAssoc preserveParity reverseParity reverseParity = refl
composeParityAssoc reverseParity preserveParity preserveParity = refl
composeParityAssoc reverseParity preserveParity reverseParity = refl
composeParityAssoc reverseParity reverseParity preserveParity = refl
composeParityAssoc reverseParity reverseParity reverseParity = refl

SSPWeaveState : SSP.SSPPrime → Set
SSPWeaveState lane = Tower.LaneState

data SSPWeavePath : SSP.SSPPrime → SSP.SSPPrime → Set where
  lanePath :
    {source target : SSP.SSPPrime} →
    LaneParity →
    SSPWeavePath source target

pathParity :
  {source target : SSP.SSPPrime} →
  SSPWeavePath source target →
  LaneParity
pathParity (lanePath parity) = parity

identitySSPPath :
  (lane : SSP.SSPPrime) →
  SSPWeavePath lane lane
identitySSPPath lane = lanePath preserveParity

infixr 40 _thenSSP_

_thenSSP_ :
  {source middle target : SSP.SSPPrime} →
  SSPWeavePath middle target →
  SSPWeavePath source middle →
  SSPWeavePath source target
_thenSSP_ (lanePath q) (lanePath p) =
  lanePath (composeParity q p)

sspPathIdLeft :
  {source target : SSP.SSPPrime} →
  (path : SSPWeavePath source target) →
  identitySSPPath target thenSSP path ≡ path
sspPathIdLeft (lanePath preserveParity) = refl
sspPathIdLeft (lanePath reverseParity) = refl

sspPathIdRight :
  {source target : SSP.SSPPrime} →
  (path : SSPWeavePath source target) →
  path thenSSP identitySSPPath source ≡ path
sspPathIdRight (lanePath preserveParity) = refl
sspPathIdRight (lanePath reverseParity) = refl

sspPathAssoc :
  {i j k l : SSP.SSPPrime} →
  (r : SSPWeavePath k l) →
  (q : SSPWeavePath j k) →
  (p : SSPWeavePath i j) →
  (r thenSSP q) thenSSP p ≡ r thenSSP (q thenSSP p)
sspPathAssoc (lanePath r) (lanePath q) (lanePath p)
  rewrite composeParityAssoc r q p = refl

transportParity : LaneParity → Tower.LaneState → Tower.LaneState
transportParity preserveParity state = state
transportParity reverseParity state =
  Tower.laneOrientationAction SSP.inverseOrientation state

transportSSP :
  {source target : SSP.SSPPrime} →
  SSPWeavePath source target →
  SSPWeaveState source →
  SSPWeaveState target
transportSSP (lanePath parity) state = transportParity parity state

transportParityComposition :
  (q p : LaneParity) →
  (state : Tower.LaneState) →
  transportParity (composeParity q p) state
  ≡ transportParity q (transportParity p state)
transportParityComposition preserveParity preserveParity state = refl
transportParityComposition preserveParity reverseParity state = refl
transportParityComposition reverseParity preserveParity state = refl
transportParityComposition reverseParity reverseParity Tower.negativeLaneState = refl
transportParityComposition reverseParity reverseParity Tower.mediatedLaneState = refl
transportParityComposition reverseParity reverseParity Tower.positiveLaneState = refl

transportSSPIdentity :
  (lane : SSP.SSPPrime) →
  (state : SSPWeaveState lane) →
  transportSSP (identitySSPPath lane) state ≡ state
transportSSPIdentity lane state = refl

transportSSPComposition :
  {source middle target : SSP.SSPPrime} →
  (q : SSPWeavePath middle target) →
  (p : SSPWeavePath source middle) →
  (state : SSPWeaveState source) →
  transportSSP (q thenSSP p) state
  ≡ transportSSP q (transportSSP p state)
transportSSPComposition (lanePath q) (lanePath p) state =
  transportParityComposition q p state

SSPResidual : SSP.SSPPrime → Set
SSPResidual lane = LaneParity

sspStateResidual :
  (lane : SSP.SSPPrime) →
  SSPWeaveState lane →
  SSPResidual lane
sspStateResidual lane state = preserveParity

sspResidualAfter :
  {source target : SSP.SSPPrime} →
  SSPWeavePath source target →
  SSPWeaveState source →
  SSPResidual target
sspResidualAfter path state = pathParity path

sspResidualIdentity :
  (lane : SSP.SSPPrime) →
  (state : SSPWeaveState lane) →
  sspResidualAfter (identitySSPPath lane) state
  ≡ sspStateResidual lane state
sspResidualIdentity lane state = refl

canonicalSSPIndexedWeave :
  Indexed.IndexedWeave SSP.SSPPrime SSPWeaveState
canonicalSSPIndexedWeave =
  record
    { Path = SSPWeavePath
    ; idPath = identitySSPPath
    ; _∙_ = _thenSSP_
    ; pathIdLeft = sspPathIdLeft
    ; pathIdRight = sspPathIdRight
    ; pathAssoc = sspPathAssoc
    ; transport = transportSSP
    ; transportId = transportSSPIdentity
    ; transportComp = transportSSPComposition
    ; Residual = SSPResidual
    ; stateResidual = sspStateResidual
    ; residualAfter = sspResidualAfter
    ; residualId = sspResidualIdentity
    }

reverseTwicePreservesEveryLaneState :
  (source middle target : SSP.SSPPrime) →
  (state : SSPWeaveState source) →
  transportSSP
    (_thenSSP_
      (lanePath {source = middle} {target = target} reverseParity)
      (lanePath {source = source} {target = middle} reverseParity))
    state
  ≡ state
reverseTwicePreservesEveryLaneState source middle target state =
  transportParityComposition reverseParity reverseParity state

reversePathRetainsTargetResidual :
  {source target : SSP.SSPPrime} →
  (state : SSPWeaveState source) →
  sspResidualAfter
    (lanePath {source = source} {target = target} reverseParity)
    state
  ≡ reverseParity
reversePathRetainsTargetResidual state = refl
