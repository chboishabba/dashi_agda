#!/usr/bin/env python3
import argparse,json
from pathlib import Path

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--source-json',type=Path,required=True)
    p.add_argument('--output-json',type=Path,required=True)
    a=p.parse_args()
    src=json.loads(a.source_json.read_text())
    checks={
      'schema':src.get('schema')=='ns_compact_gamma_exact_cutset_audit.v1',
      'finite_authority':src.get('authority')=='finite_computational_audit_only',
      'no_promotions':all(src.get(k) is False for k in ('theorem_promoted','full_ns_promoted','clay_promoted')),
      'adjacent_unconditional_refuted':src['adjacent_shell']['unconditional_adjacent_contraction_empirically_refuted'] is True,
      'near_signed_refuted':src['near_triad']['signed_coercivity_empirically_refuted'] is True,
      'near_reversal_exact':src['near_triad']['max_sign_reversal_residual'] <= 1e-12,
      'far_low_budget':src['far_low']['fits_one_eighth_budget'] is True,
      'far_high_budget':src['far_high']['fits_one_eighth_budget'] is True,
      'scalar_positive':src['scalar_certificate']['remainder_positive'] is True,
      'coverage_obstruction':src['coverage_scaling']['finite_fixed_absolute_floor_route_refuted_for_scaling_class'] is True,
    }
    out={'schema':'check_ns_compact_gamma_exact_cutset_audit.v1','checks':checks,'error_count':sum(not v for v in checks.values()),'ok':all(checks.values())}
    a.output_json.parent.mkdir(parents=True,exist_ok=True)
    a.output_json.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
    raise SystemExit(0 if out['ok'] else 1)
if __name__=='__main__': main()
