#!/usr/bin/env python3
"""Deterministic 2-D one-bounce geometry screening for spiral reflectors.

Standard-library-only. This is a synthetic equal-energy ray fixture, not
Maxwell/acoustic simulation, a measured Kozyrev enclosure or evidence of
non-EM torsion. Models a single specular reflection from 8-10 polygon panels.

The three candidate families are:
    Archimedean (k=0,c=0)
    Golden-indexed endpoint-normalised exponential (NOT a golden spiral)
    Corrected normalised logarithmic (free k,c)
The objective is explicitly synthetic and may change with source/target.
"""
import argparse
import json
import math

PI = math.pi
PHI = (1 + math.sqrt(5)) / 2


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1]


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def scale(c, v):
    return (c * v[0], c * v[1])


def shape(t, k, correction):
    # Normalise endpoints and avoid cancellation at k ~ 0.
    if abs(k) < 1e-12:
        fraction = t
    else:
        fraction = math.expm1(k * t) / math.expm1(k)
    return fraction + correction * math.sin(2 * PI * t)


def vertices(k, correction=0.0, *, panels=9, turns=1.5,
             inner_radius=0.75, outer_radius=1.55, handedness=1):
    if panels < 3 or panels > 64 or turns <= 0:
        raise ValueError('invalid panels or turns')
    if inner_radius <= 0 or outer_radius <= inner_radius:
        raise ValueError('invalid radii')
    if handedness not in (-1, 1):
        raise ValueError('handedness must be -1 or +1')
    t_vals = [i / panels for i in range(panels + 1)]
    f_vals = [shape(t, k, correction) for t in t_vals]
    if any(f_vals[i+1] <= f_vals[i] for i in range(panels)):
        return None  # monotonic widening is a hard admissibility condition
    rs = [inner_radius + (outer_radius - inner_radius) * f for f in f_vals]
    return [(r * math.cos(handedness * 2 * PI * turns * t),
             r * math.sin(handedness * 2 * PI * turns * t))
            for t, r in zip(t_vals, rs)]


def first_hit(origin, direction, points, *, epsilon=1e-9):
    nearest = None
    for a, b in zip(points, points[1:]):
        tangent = sub(b, a)
        den = cross(direction, tangent)
        if abs(den) < 1e-12:
            continue
        offset = sub(a, origin)
        ray_distance = cross(offset, tangent) / den
        wall_fraction = cross(offset, direction) / den
        if ray_distance > epsilon and -epsilon <= wall_fraction <= 1 + epsilon:
            if nearest is None or ray_distance < nearest[0]:
                nearest = (ray_distance, add(origin, scale(ray_distance, direction)), tangent)
    return nearest


def bounce(origin, direction, points, target=(0, 0), target_radius=0.10):
    hit = first_hit(origin, direction, points)
    if hit is None:
        return None
    _, impact, tangent = hit
    t2 = dot(tangent, tangent)
    if t2 == 0:
        raise ValueError('zero-length segment')
    out = sub(scale(2 * dot(direction, tangent) / t2, tangent), direction)
    wall_impulse = sub(direction, out)
    # Ray from impact must approach the target, after the bounce, not before.
    to_target = sub(target, impact)
    projected = dot(to_target, out)
    miss_sq = dot(to_target, to_target) - max(projected, 0.0)**2
    captured = projected > 1e-9 and miss_sq <= target_radius**2
    return {
        'capture': captured,
        'torque': cross(impact, wall_impulse),
        'energy_residual': dot(direction, direction) - dot(out, out),
        'momentum_residual': add(out, wall_impulse),
    }


def evaluate(points, *, samples=360, sources=((0.25, 0.0), (0.21, 0.10), (0.21, -0.10)),
             target=(0.0, 0.0), target_radius=0.1):
    if not points:
        return None
    lengths = [math.hypot(*sub(b, a)) for a, b in zip(points, points[1:])]
    hit_rates, wall_torques, reflections = [], [], []
    for source in sources:
        captured, torque, bounced = 0, 0.0, 0
        for i in range(samples):
            angle = 2 * PI * (i + 0.5) / samples
            direction = (math.cos(angle), math.sin(angle))
            result = bounce(source, direction, points, target, target_radius)
            if result is None:
                continue
            assert abs(result['energy_residual']) <= 1e-10
            assert abs(result['momentum_residual'][0] - direction[0]) <= 1e-10
            assert abs(result['momentum_residual'][1] - direction[1]) <= 1e-10
            bounced += 1
            captured += result['capture']
            torque += result['torque']
        hit_rates.append(captured / samples)
        wall_torques.append(torque / samples)
        reflections.append(bounced / samples)
    return {
        'capture_mean': sum(hit_rates) / len(hit_rates),
        'capture_worst': min(hit_rates),
        'capture_by_source': hit_rates,
        'wall_angular_impulse_mean': sum(wall_torques) / len(wall_torques),
        'reflected_fraction_mean': sum(reflections) / len(reflections),
        'length_m': sum(lengths),
        'panels': len(lengths),
        'panel_segment_lengths_m': lengths,
    }


def optimise(*, panels=9, turns=1.5, samples=360,
             inner_radius=0.75, outer_radius=1.55):
    spec = {'panels': panels, 'turns': turns, 'inner_radius': inner_radius,
            'outer_radius': outer_radius}
    def calc(label, k, c):
        pts = vertices(k, c, **spec)
        m = evaluate(pts, samples=samples)
        if m is None:
            return None
        return {'name': label, 'k': round(k, 9), 'correction': round(c, 9), **m}

    arch = calc('Archimedean', 0.0, 0.0)
    gold_k = math.log(PHI) * (turns * 4)  # nominal golden index ONLY: endpoint normalisation destroys true golden radius growth
    golden = calc('golden-indexed normalised exponential (not a golden spiral)', gold_k, 0.0)
    endpoint_log = calc('true endpoint-matched logarithmic spiral', math.log(outer_radius/inner_radius), 0.0)
    # Pure log + sinusoidal endpoint-fixed correction; constrain monotonic
    # progression, absolute path length and individual manufactured panels.
    candidates = []
    for k in (-4, -3, -2, -1, 0, 0.5, 1, 2, gold_k, 3, 4):
        for correction in (-0.08, -0.04, 0.0, 0.04, 0.08):
            result = calc('free log/correction', k, correction)
            if result is not None:
                candidates.append(result)
    # Avoid comparing wildly different sheet stock budgets. A 10% total
    # length upper bound is a screening constraint, not a fabricated patent spec.
    eligible = [x for x in candidates if x['length_m'] <= 1.10*arch['length_m']]
    if not eligible:
        raise ValueError('no valid length-constrained geometry')
    # Maximin capture rate across the three frozen point sources.
    # Tie-break by mean capture and shortest total sheet length.
    objective = lambda x: (x['capture_worst'], x['capture_mean'], -x['length_m'])
    winner = max(eligible, key=objective)
    golden_tuned = [x for x in eligible if abs(x['k'] - round(gold_k, 9)) < 1e-7]
    tuned = max(golden_tuned, key=objective) if golden_tuned else None
    return {
        'model': 'SYNTHETIC first-hit one-bounce 2D specular reflector only',
        'selected_objective': 'maximise worst-case one-bounce receiver hit fraction across three fixed sources',
        'constraints': '9 line segments by default; fixed radial endpoints/1.5 turn; widening profile; at most 110% Archimedean sheet perimeter',
        'source_points_m': [(0.25,0.0), (0.21,0.10), (0.21,-0.10)],
        'receiver_center_m': [0, 0], 'receiver_radius_m': 0.1,
        'rays_per_source': samples, 'coordinate_unit': 'metre',
        'reference_archimedean': arch,
        'reference_endpoint_matched_logarithmic': endpoint_log,
        'reference_golden_indexed_normalised': golden,
        'literal_golden_spiral_outer_radius_required_m': inner_radius * PHI ** (4 * turns),
        'literal_golden_spiral_admissible_with_fixed_outer_radius': abs(inner_radius * PHI**(4*turns) - outer_radius) < 1e-9,
        'golden_growth_correction_exponent_for_envelope': math.log(outer_radius/inner_radius) / (4*turns*math.log(PHI)),
        'best_golden_indexed_normalised_with_correction': tuned,
        'grid_optimum': winner,
        'admissible_grid_count': len(eligible),
        'not_real_apparatus_or_physical_wave_solution': True,
        'not_evidence_for_new_torsion': True,
        'sensitivity_to_frequency_material_emitter_receiver_open': True,
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--panels', type=int, choices=(8, 9, 10), default=9)
    p.add_argument('--turns', type=float, default=1.5)
    p.add_argument('--samples', type=int, default=360)
    args = p.parse_args()
    if args.samples < 32:
        p.error('at least 32 rays per source required')
    print(json.dumps(optimise(panels=args.panels, turns=args.turns,
                              samples=args.samples), indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
