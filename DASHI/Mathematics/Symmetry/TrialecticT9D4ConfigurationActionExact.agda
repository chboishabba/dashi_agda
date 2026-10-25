module DASHI.Mathematics.Symmetry.TrialecticT9D4ConfigurationActionExact where

-- Spatial D4 action lifted to the pre-existing nine-position observer
-- matrix. This permutes *positions*, leaving the View values untouched.
-- No claim that participant identities should be physically rotated.
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Obs

rotate : {View : Set} → Obs.ObserverMatrix3 View → Obs.ObserverMatrix3 View
rotate (Obs.observerMatrix3 aa ab ac ba bb bc ca cb cc) =
  Obs.observerMatrix3 ca ba aa cb bb ab cc bc ac

reflect : {View : Set} → Obs.ObserverMatrix3 View → Obs.ObserverMatrix3 View
reflect (Obs.observerMatrix3 aa ab ac ba bb bc ca cb cc) =
  Obs.observerMatrix3 ac ab aa bc bb ba cc cb ca

rotate4 : {View : Set} → (m : Obs.ObserverMatrix3 View) →
  rotate (rotate (rotate (rotate m))) ≡ m
rotate4 (Obs.observerMatrix3 aa ab ac ba bb bc ca cb cc) = refl

reflect2 : {View : Set} → (m : Obs.ObserverMatrix3 View) →
  reflect (reflect m) ≡ m
reflect2 (Obs.observerMatrix3 aa ab ac ba bb bc ca cb cc) = refl

reflectRotateReflect : {View : Set} →
  (m : Obs.ObserverMatrix3 View) →
  reflect (rotate (reflect m)) ≡ rotate (rotate (rotate m))
reflectRotateReflect (Obs.observerMatrix3 aa ab ac ba bb bc ca cb cc) = refl
