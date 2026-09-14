module DASHI.Culture.MissingDeceasedPlanetarySmallBodyObservatoryBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T
import DASHI.Core.RealObjectApplicationBidiExact as R

planetarySource : Source.AttributedSource
planetarySource = Source.mkNoDOISource
  "DASHI / retained Hicks primary-source lineage"
  "Planetary small-body optical observing and physical-inference object"
  "JPL/CNEOS/retained Hicks source surfaces"
  "current formalisation"
  "DASHI Hicks source owners"
  (Source.namedSourceKind "formalisation composite")
  "Pays a real small-body observing/characterisation object class; not a shared historical programme for the retained cohort."
  Source.publicAttribution

planetaryAtlas : Source.AttributedSourceAtlas
planetaryAtlas = Source.mkSourceAtlas
  "planetary-small-body object atlas"
  "DASHI.Culture.MissingDeceasedPlanetarySmallBodyObservatoryBidiExact"
  (planetarySource ∷ [])
  "Science-object fit does not import mission participation or event causation."

photometryRequirement : R.RealObjectRequirement
photometryRequirement = R.mkRequirement
  "small-body time-series photometry"
  "obtain calibrated lightcurves under known geometry and infer rotation/shape/compositional constraints"
  "Hicks small-body photometry owners"
  (T.acquireValidationCorpus ∷ T.acquireApplicationGeometry ∷ T.acquireUncertaintyModel ∷ [])
  "Raw fluxes, timestamps, calibration stars, viewing geometry and model degeneracy are required before unique physical inference."

planetarySmallBodyObservatoryObject : R.RealEngineeringObject
planetarySmallBodyObservatoryObject = R.real-engineering-object
  "planetary small-body observatory / survey platform"
  "benign planetary-science observing object"
  planetaryAtlas
  (photometryRequirement ∷ [])
  "measure asteroid/comet lightcurves and infer bounded physical properties"
  "Object relevance does not establish participation in any particular mission or common programme."

hicksFit : R.ScientistObjectFit
hicksFit = R.mkFit
  "Michael David Hicks"
  "DASHI Hicks small-body photometry owners"
  "asteroid/comet time-series photometry and physical inference"
  photometryRequirement R.directSourceFit
  "retained Hicks/JPL/CNEOS observing lineage"
  "Direct source fit to the observing/characterisation subsystem."
  "recover raw lightcurve, viewing geometry, calibration and uncertainty model for one exact campaign"
  false
  "Direct science fit does not pay shared programme identity, custody or event cause."

hicksDirectFit : Bool
hicksDirectFit = true

historicalParticipationPaid : Bool
historicalParticipationPaid = false
