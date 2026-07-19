module DASHI.Regulation.RegulatoryCategoricalBridge where

open import Agda.Builtin.String using (String)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ProjectionFibre as PF
import DASHI.Core.ResidualNaturality as RN
import DASHI.Core.PromotionTransformation as PT

open import DASHI.Regulation.RegulatoryProjectionCore

record RegulatoryCategoricalBridge
  (ProjectionCat AuthorityCat : PC.ProjectionCategory)
  (Fibre : PF.ProjectionFibre ProjectionCat)
  (Residual : RN.ResidualNaturality ProjectionCat AuthorityCat)
  (Promotion : PT.PromotionTransformation ProjectionCat AuthorityCat Residual)
  : Set₁ where
  field
    regulatoryProjection : RegulatoryProjection

    -- The regulatory carrier and observable are interpreted by the
    -- existing DASHI projection/fibre machinery rather than a parallel
    -- notion of projection.
    carrierObjectMatches :
      PC.Obj ProjectionCat
    observableObjectMatches :
      PC.Obj ProjectionCat

    -- Promotion remains downstream of residual closure through the
    -- existing PromotionTransformation supplied above.
    bridgeReading : String

open RegulatoryCategoricalBridge public

record RegulatoryFibreRestriction (P : RegulatoryProjection) : Set₁ where
  field
    Evidence : Set
    admissibleBefore : HiddenActivity P → Set
    admissibleAfter  : Evidence → HiddenActivity P → Set

    restriction :
      (e : Evidence) →
      (h : HiddenActivity P) →
      admissibleAfter e h → admissibleBefore h

    -- Evidence may narrow a fibre but may not manufacture a global
    -- inverse to the public projection.
    nonReconstruction : NoSection P
    restrictionReading : String

open RegulatoryFibreRestriction public
