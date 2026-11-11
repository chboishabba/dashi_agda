# Filsinger golden-rectangle two-source/modal optimisation (2026-11-11)

## Actual source claims and provenance
The presenter distinguishes the demonstrated **Earth-ground ZVS/RC circuit** (variable megohm shunts, toroidal magnetic circuits, white 3.33uF banks, three blue capacitors in new footage, green high-voltage rectifier candidates, capacitors/bridge ground connection) from the **proposed portable common-midpoint + 1:1.618 plate/antenna version**, described as "cosmic radiation" harvesting. The latter has not been shown completed. "Cosmic radiation" may refer colloquially to ambient EM fields but ionizing cosmic rays are not the same source as coherent ambient RF or Earth atmospheric-electric fields: keep Earth galvanic/geoelectric, atmospheric DC/ion, RF and ionizing radiation **distinct ports** and sources with distinct physically available input powers. Do not attribute energy source from capacitor voltage.

## External modern science
Single-fed circular-polarization microstrip antenna literature uses deliberately slightly split orthogonal modes and feed perturbations to create 90-degree quadrature; the geometry/phase mechanism is real, but a ratio of 1.618 is not a universal phase angle. One-port temporal coupled-mode theory puts maximum absorption at critical coupling (external leakage = internal+extractive damping); for a power harvester, useful-load extraction and internal losses must be tracked separately. Prior art sources: https://www.microwavejournal.com/articles/935-a-design-procedure-for-a-circular-polarized-nearly-square-patch-antenna ; https://ietresearch.onlinelibrary.wiley.com/doi/10.1049/iet-map.2016.0216 ; https://www.nature.com/articles/s41598-025-05446-7 .

## Local executable model (conditional)
`/mnt/data/filsinger_twoport_modal_optimization.py` executes using numpy and matplotlib. It passed tests for passive-power bound, ratio/frequency-matching, local polarisation limits and correct finite-load extraction. Graph and machine-readable output: `filsinger_twoport_modal_comparison.png`, `filsinger_twoport_modal_results.json`, `filsinger_twoport_modal_curves.csv`. The two resonant modes have `f_x=f_center/sqrt(r)`, `f_y=f_center*sqrt(r)` (fixed-area rectangle abstraction); incoming spectral weights and two orthogonal directional mode couplings are specified explicitly. Resonant amplitudes obey `(diag(gamma+i(f_j-f))+i*kappa*offdiag) a=sqrt(2 gamma_external)*s`, with `gamma_external=.04`, `gamma_load=.04`, `gamma_intrinsic=.02`. Captured useful power is `sum 2 gamma_load |a_j|²`. This is not a 3D Maxwell eigenmode computation, measured external spectrum, rectifier or solar/atmospheric power budget.

Four **invented** incident spectral cases (normalised available incident power = 1):
| Incident spectrum | Optimising ratio | Gold relative to optimum |
| 1:phi two separately polarised tones | 1.618 | ~100% |
| 1:1.30 two tones | 1.30 | 39.4% |
| 1:1.90 two tones | 1.90 | 45.3% |
| .85 to 1.65 broadband equal-amplitude modal input | 1.00 | 86.3% |
The first case matches the golden ratio by source construction: NOT a claim Earth's spectrum naturally does that. A continuous-band receiver can favour other dimensions. Spectral data, field direction and effective antenna size are requisite physical inputs.

Fixed ratio=phi, for an incident two-tone 1:1.30 spectrum, +/-10% independent mode-frequency tuning increases normalized captured power to **0.633** (without tuning 0.252), approaching the theoretical matched result 0.64. The optimum hits imposed tuning limits and real loading cost is unmodelled. This illustrates how load/tuning can compensate mismatched physical geometry; no guarantee that megohm bleeder adjustment supplies these reactances.

## Coherent phase and circulation
With a coherent, single-frequency feed that overlaps both orthogonal modes, complex resonant response supplies nontrivial relative phase without an external quadrature feed. Local temporal circularity is Stokes-like `2 Im(conj(a_x)a_y)/( |a_x|²+|a_y|² )`, bounded [-1,1]. Under the illustrative common feed, ratio=1.3 produces ~-0.885, phi ~-0.587, square zero at a selected source frequency; real values vary with load and detuning. A rotating vector at one point is NOT automatically a spatial closed streamline or physical Maxwell surface current; previous stream-function synthetic counterexample remains not verified for a conductor.

Max useful extraction is finite: in the single-resonance matched mode `η=4 gamma_e gamma_l/(gamma_e+gamma_l+gamma_i)^2`, with gamma_e=.04,gamma_i=.02 it maximises at gamma_l=.06. Very weak load traps energy rather than delivering it; very large load overdamps the mode. No energy gain beyond incident source follows from resonant phase tug.

## Exact outstanding cut
- Preserve **two separate Circuit36927 candidate netlists** with a provenance-bearing transformation (ground return -> proposed midpoint/plate); NOT an equivalence until boundaries/returns established.
- Build full **Maxwell boundary-value** / characteristic-mode solution for an actually specified surface (material, plate/mesh, dimensions, substrate, feed and counterpoise, conductivity, radiation channel) and measured atmospheric/RF incident spectrum.
- Replace invented spectral weights with measured site/time-dependent Earth DC gradients, atmospheric electric flux, RF electromagnetic flux and, if desired, explicitly defined ionising cosmic-ray particle flux. Include source coherence: unrelated frequencies do not retain a stable phase relation unless an active synchronisation mechanism exists. Never count incoherent energy cross-terms as power gain.
- Fit nonlinear ZVS loading/resonant phase feedback separately from antenna modes, including measured switching, kilovolt shunts and all signed supply/ground work.
- Agda kernel check of PR #1482/#1487 remains pending. Local Python physics feasibility tests are not an experimental harvest receipt.
