# Filsinger: bounded candidate-converter optimisation (10 Nov 2026)

## Ownership and non-promotion
This adds *one* reusable numerical optimisation consumer to PR #1487, stacked on the existing component graph PR #1482. The independent conditional energy accounting is PR #1486 and Tesla/Schumann mode non-identifiability is PR #1464.

**Observed/narrated:** white 3.33uF capacitor; target ~1500V; one 15V display and ~6.7–7.3W reported; narrator identifies white capacitor hot side and Earth-negative connection; one activation event and sustained ~7.8kHz **acoustic** tone; visually toroidal windings, other high-voltage components, partially used bridge; unknown electrical connections beyond the narration.

**Assumed for an engineering best-case comparison, not measured:** electrical 7800Hz = acoustic frequency, 6.7W = real electric input, converter with independently adjustable tank capacitance, ideal available magnetic coupling and voltage gain, loaded Q, switch/rectifier, and fixed control overhead. The elevated atmospheric collector and net environmental energy are NOT assumed. Real isolation, insulation, Q, losses, and high-voltage measurement remain outside the model. Do not manufacture an actual wiring diagram from an ideal design witness.

## Objective and constraints
Find fastest conditional white-capacitor fill with 6.7W while tracking resource tradeoffs of higher loaded Q, higher voltage gain and larger inductance. No universal cheapest/optimal hardware without real parts, size, safety, losses or prices.

For candidate tank C, voltage transfer g, resonance f, peak output 1500V, loaded quality Q, budget P, control overhead P0, and post-tank charging efficiency eta:

```
L = 1/((2*pi*f)^2*C)
V_tank_peak = 1500/g
U_tank = 0.5*C*V_tank_peak^2
P_tank_loss = (2*pi*f/Q)*U_tank
P_to_white = eta*(P - P0 - P_tank_loss)
t_fill = (0.5*3.33e-6*1500^2) / P_to_white
```

Filter out P_to_white<=0. A gain > 1 in this abstract formula is a *voltage conversion ratio*, not a proof of physical step-up without power balance and appropriately designed transformers/rectifiers. These formulas use a nominal instantaneous tank energy and simplified loss/Q semantics.

## Local Python receipts
`/mnt/data/filsinger_design_optimisation.py` independently executed 20/20 unit tests and scanned 1,028 feasible of 1,152 enumerated candidates. 257 are nondominated under 4 minimisation coordinates (fill time, gain, Q, inductance). Its output includes `filsinger_optimisation_results.json`, `filsinger_optimisation_pareto.csv`, and `filsinger_optimisation_tradeoff.png`. A standard-library reimplementation is committed as `scripts/filsinger_bounded_design_optimisation.py`; this exact committed script has not been run through the GitHub connector and has no CI receipt.

Illustrative not-optimised performance: C_tank=100nF, gain=10, loaded Q=100, eta=75%, overhead=.5W yields L=4.1634mH, tank V_peak=150V, tank U=.001125J, tank dissipation=.55135W, remaining charge allocation=4.23649W, idealised initial fill=.88428s. No energy from Earth is required in this illustrative budget. Whether a real circuit can meet all assumed parameters at once requires validation.

Grid-fastest corner: C_tank=50nF, gain=20, Q=200, eta=90%, L=8.32686mH, dissipation=.03446W, fill=.67512s. This is **not** an optimal physical design: it sits at optimistic parameter boundaries, and no real gains, cores, switching loss, ratings or prices are admitted. Faster projected performance is not demonstrated higher environmental harvesting.

## Highest-alpha unpaid gates
P0 exact original same-device pin topology incl. bridge and return path; actual metered electrical input vs output; actual switching waveform vs microphone frequency; actual capacitive network and signed differential meter voltages.
P1 independently measured Q/frequency dependence, core nonlinearity/heat, magnetics and switching losses under calibrated HV load; realistic certified component parameter domain and prices.
P1 signed real environmental energy `integral v(t)i(t) dt` after all connected drive/storage/ground chemistry.
P2 only then a measured ELF field and transfer function into existing Tesla/Schumann PR #1464.
Verification: Agda kernel acceptance of stacked module remains pending; the independently authored local optimisation Python passed, while the exact committed copy has no runtime receipt.
