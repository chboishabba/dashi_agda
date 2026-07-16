module DASHI.Moonshine.MaassMoonshineClosureFull where

open import Agda.Primitive using (Setω)

import DASHI.Moonshine.SpecificMaassMoonshineBridge as SMB

------------------------------------------------------------------------
-- The shared-base promotion is owned by
-- MaassMoonshineSharedBaseClosure.  This module is intentionally the
-- *stronger*, optional endpoint: it can be inhabited only when a named
-- construction really intertwines the selected restricted fibres.

record MaassMoonshineIntertwinerClosure
  (SharedBase MaassForm McKayThompsonSeries Prime : Set)
  (certifiedMaass : SharedBase → MaassForm)
  (certifiedSeries : SharedBase → McKayThompsonSeries)
  (ConstructionDomain : MaassForm → Set)
  (maassHecke : Prime → MaassForm → MaassForm)
  (moonshineHecke : Prime → McKayThompsonSeries → McKayThompsonSeries)
  (coefficientTraceLaw : McKayThompsonSeries → Set)
  : Setω where
  field
    sharedBase : SharedBase
    bridge :
      SMB.SpecificMaassMoonshineBridge MaassForm McKayThompsonSeries Prime
        ConstructionDomain maassHecke moonshineHecke coefficientTraceLaw
        (certifiedMaass sharedBase) (certifiedSeries sharedBase)

-- Retained as the spelling for the full/named-intertwiner endpoint.  It is
-- not the promotion type for mere shared modular-group compatibility.
record MaassMoonshineClosureFull
  (SharedBase MaassForm McKayThompsonSeries Prime : Set)
  (certifiedMaass : SharedBase → MaassForm)
  (certifiedSeries : SharedBase → McKayThompsonSeries)
  (ConstructionDomain : MaassForm → Set)
  (maassHecke : Prime → MaassForm → MaassForm)
  (moonshineHecke : Prime → McKayThompsonSeries → McKayThompsonSeries)
  (coefficientTraceLaw : McKayThompsonSeries → Set)
  : Setω where
  field
    namedIntertwiner :
      MaassMoonshineIntertwinerClosure SharedBase MaassForm McKayThompsonSeries
        Prime certifiedMaass certifiedSeries ConstructionDomain maassHecke
        moonshineHecke coefficientTraceLaw

data NamedMaassMoonshineIntertwinerPromotion
  {SharedBase MaassForm McKayThompsonSeries Prime certifiedMaass certifiedSeries
    ConstructionDomain maassHecke moonshineHecke coefficientTraceLaw}
  : Setω where
  promoteNamedIntertwiner :
    MaassMoonshineIntertwinerClosure SharedBase MaassForm McKayThompsonSeries
      Prime certifiedMaass certifiedSeries ConstructionDomain maassHecke
      moonshineHecke coefficientTraceLaw →
    NamedMaassMoonshineIntertwinerPromotion

