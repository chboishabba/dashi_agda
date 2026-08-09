module DASHI.Biology.SSPIndexedWeaveModularIntegrationExact where

open import DASHI.Core.Prelude

import DASHI.Core.IndexedWeaveHyperfabricExact as Indexed
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Biology.SSPIndexedWeaveHyperfabricExact as SSPWeave
import DASHI.Biology.ModularCoarseFineAddressFibrationExact as Modular

------------------------------------------------------------------------
-- Cross-pollination theorem.
--
-- An integrated site is an SSP lane over one coarse modular address.  Its
-- fibre contains the ten-sector fine address together with the lane state.
-- Typed paths may move between SSP lanes but must preserve the coarse base.
-- Fine data are transported in the preserved base fibre, while the SSP state
-- follows the proved parity action.
------------------------------------------------------------------------

SSPModularIndex : Set
SSPModularIndex = SSP.SSPPrime × Modular.CoarseAddress

IntegratedState : SSPModularIndex → Set
IntegratedState index =
  Modular.FineAddress
  × SSPWeave.SSPWeaveState (fst index)

IntegratedPath : SSPModularIndex → SSPModularIndex → Set
IntegratedPath source target =
  SSPWeave.SSPWeavePath (fst source) (fst target)
  × (snd source ≡ snd target)

identityIntegratedPath :
  (index : SSPModularIndex) →
  IntegratedPath index index
identityIntegratedPath index =
  SSPWeave.identitySSPPath (fst index) , refl

infixr 40 _thenIntegrated_

_thenIntegrated_ :
  {source middle target : SSPModularIndex} →
  IntegratedPath middle target →
  IntegratedPath source middle →
  IntegratedPath source target
_thenIntegrated_ (q , qBase) (p , pBase) =
  SSPWeave._thenSSP_ q p , trans pBase qBase

integratedPathIdLeft :
  {source target : SSPModularIndex} →
  (path : IntegratedPath source target) →
  identityIntegratedPath target thenIntegrated path ≡ path
integratedPathIdLeft (path , refl)
  rewrite SSPWeave.sspPathIdLeft path = refl

integratedPathIdRight :
  {source target : SSPModularIndex} →
  (path : IntegratedPath source target) →
  path thenIntegrated identityIntegratedPath source ≡ path
integratedPathIdRight (path , refl)
  rewrite SSPWeave.sspPathIdRight path = refl

integratedPathAssoc :
  {i j k l : SSPModularIndex} →
  (r : IntegratedPath k l) →
  (q : IntegratedPath j k) →
  (p : IntegratedPath i j) →
  (r thenIntegrated q) thenIntegrated p
  ≡ r thenIntegrated (q thenIntegrated p)
integratedPathAssoc (r , refl) (q , refl) (p , refl)
  rewrite SSPWeave.sspPathAssoc r q p = refl

transportIntegrated :
  {source target : SSPModularIndex} →
  IntegratedPath source target →
  IntegratedState source →
  IntegratedState target
transportIntegrated (path , refl) (fine , laneState) =
  fine , SSPWeave.transportSSP path laneState

transportIntegratedIdentity :
  (index : SSPModularIndex) →
  (state : IntegratedState index) →
  transportIntegrated (identityIntegratedPath index) state ≡ state
transportIntegratedIdentity index (fine , laneState)
  rewrite SSPWeave.transportSSPIdentity (fst index) laneState = refl

transportIntegratedComposition :
  {source middle target : SSPModularIndex} →
  (q : IntegratedPath middle target) →
  (p : IntegratedPath source middle) →
  (state : IntegratedState source) →
  transportIntegrated (q thenIntegrated p) state
  ≡ transportIntegrated q (transportIntegrated p state)
transportIntegratedComposition
  (q , refl) (p , refl) (fine , laneState)
  rewrite SSPWeave.transportSSPComposition q p laneState = refl

IntegratedResidual : SSPModularIndex → Set
IntegratedResidual index = SSPWeave.LaneParity

integratedStateResidual :
  (index : SSPModularIndex) →
  IntegratedState index →
  IntegratedResidual index
integratedStateResidual index state = SSPWeave.preserveParity

integratedResidualAfter :
  {source target : SSPModularIndex} →
  IntegratedPath source target →
  IntegratedState source →
  IntegratedResidual target
integratedResidualAfter (path , baseEquality) state =
  SSPWeave.pathParity path

integratedResidualIdentity :
  (index : SSPModularIndex) →
  (state : IntegratedState index) →
  integratedResidualAfter (identityIntegratedPath index) state
  ≡ integratedStateResidual index state
integratedResidualIdentity index state = refl

canonicalSSPModularIndexedWeave :
  Indexed.IndexedWeave SSPModularIndex IntegratedState
canonicalSSPModularIndexedWeave =
  record
    { Path = IntegratedPath
    ; idPath = identityIntegratedPath
    ; _∙_ = _thenIntegrated_
    ; pathIdLeft = integratedPathIdLeft
    ; pathIdRight = integratedPathIdRight
    ; pathAssoc = integratedPathAssoc
    ; transport = transportIntegrated
    ; transportId = transportIntegratedIdentity
    ; transportComp = transportIntegratedComposition
    ; Residual = IntegratedResidual
    ; stateResidual = integratedStateResidual
    ; residualAfter = integratedResidualAfter
    ; residualId = integratedResidualIdentity
    }

coarseBaseOf : SSPModularIndex → Modular.CoarseAddress
coarseBaseOf = snd

integratedPathsPreserveCoarseBase :
  {source target : SSPModularIndex} →
  IntegratedPath source target →
  coarseBaseOf source ≡ coarseBaseOf target
integratedPathsPreserveCoarseBase path = snd path

fineAddressSurvivesLaneTransport :
  {source target : SSPModularIndex} →
  (path : IntegratedPath source target) →
  (state : IntegratedState source) →
  fst (transportIntegrated path state) ≡ fst state
fineAddressSurvivesLaneTransport (path , refl) (fine , laneState) = refl
