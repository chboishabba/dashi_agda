# Constructive Earth-like stabilised radion fixture (2026-10-24)

## Precise scope
Define a scalar EFT with canonical mass m>0 and a uniform spherical source S=s*rho:
(Delta-m²)phi=-S inside radius R, and zero outside. This is a **linear scalar sector** and its source coefficient is declared, not derived from a specified 5D matter action.

The regular origin / decaying infinity solutions are:
phi_in = S/m² - S*(mR+1)*exp(-mR)*sinh(mr)/(m³ r)
phi_out = S*(mR*cosh(mR)-sinh(mR))*exp(-mr)/(m³ r)
The C1 boundary matching is exact. The fixture verifies both differential equations, boundary values, derivative junction, regular center, and exterior falloff. Command:
python3 scripts/check_kk_radion_spherical_match.py

## Why it helps and where promotion stops
A massive radion has finite-range response, permitting suppression far from Earth. This constructs a real nontrivial sourced scalar boundary solution, unlike the black-string vacuum exterior. However, it is NOT yet a coupled solution of 5D Einstein equations or even fully sourced four-dimensional EMD equations. A 5D stabilization mechanism, action and matter coupling must be supplied; scalar backreaction, pressure, gauge fields, external mass-spin calibration, rotation, and observational prediction remain open. In 5D pure Einstein gravity on S1 there is no arbitrary radion mass potential: adding it changes the theory. Strong, electromagnetic, and Higgs sectors can contribute only after precise action/source derivation, not by relabeling scalar stress.

## Ownership
Existing PR #1241 boosted KK/orbit pipeline; #1238/#1239 curvature and gauge geometry; W4 source boundary may be reused. No PNF, W3 or SensibLaw dependency. Literature anchors: classical KK EMD with sqrt(3) dilaton coupling; stabilised compactification is a *different theory* until same action is proven. No experimental claims or Agda kernel receipt.
