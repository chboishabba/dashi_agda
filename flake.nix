{
  description = "dashi_agda — Monster group proofs with zkperf tracing";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    zkperf.url = "github:meta-introspector/zkperf";
    zkperf.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, flake-utils, zkperf }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        agdaWithStdlib = pkgs.agda.withPackages (p: [ p.standard-library ]);
        perf = pkgs.linuxPackages.perf;
        zkperf-parse = zkperf.packages.${system}.default;

        # Script: full perf record + script + annotate for one agda file
        agda-record = pkgs.writeShellScriptBin "agda-record" ''
          set -euo pipefail
          FILE="''${1:?Usage: agda-record <file.agda> [outdir]}"
          OUTDIR="''${2:-recordings}"
          BASE=$(basename "$FILE" .agda)
          mkdir -p "$OUTDIR"

          echo "=== Recording $FILE ==="

          # perf record: call-graph dwarf, full registers, multi-event
          ${perf}/bin/perf record \
            -o "$OUTDIR/$BASE.perf.data" \
            -g \
            --call-graph dwarf,65528 \
            --user-regs=AX,BX,CX,DX,SI,DI,BP,SP,IP,FLAGS,R8,R9,R10,R11,R12,R13,R14,R15 \
            -e cycles:u,instructions:u,cache-misses:u,branch-misses:u \
            -c 100 \
            -- ${agdaWithStdlib}/bin/agda "$FILE" 2>"$OUTDIR/$BASE.record.log" || true

          # perf report
          ${perf}/bin/perf report -i "$OUTDIR/$BASE.perf.data" --stdio \
            > "$OUTDIR/$BASE.report.txt" 2>&1 || true

          # perf script: full symbolic trace with registers
          ${perf}/bin/perf script -i "$OUTDIR/$BASE.perf.data" \
            -F comm,pid,tid,cpu,time,event,ip,sym,dso,symoff,srcline \
            > "$OUTDIR/$BASE.script.txt" 2>&1 || true

          # perf annotate: instruction-level hotspots
          ${perf}/bin/perf annotate -i "$OUTDIR/$BASE.perf.data" --stdio \
            > "$OUTDIR/$BASE.annotate.txt" 2>&1 || true

          # perf stat counters (separate run for clean numbers)
          ${perf}/bin/perf stat \
            -e cycles,instructions,cache-misses,cache-references,branch-misses,branches \
            -- ${agdaWithStdlib}/bin/agda "$FILE" 2>"$OUTDIR/$BASE.stat.txt" || true

          # Parse stat to witness JSON (stat file written by now)
          ${zkperf-parse}/bin/zkperf-parse "$OUTDIR/$BASE.stat.txt" "$FILE" \
            > "$OUTDIR/$BASE.witness.json" 2>/dev/null || true

          echo "=== $BASE recorded ==="
          ls -lh "$OUTDIR/$BASE".*
        '';

        # Script: batch record all .agda files
        agda-record-all = pkgs.writeShellScriptBin "agda-record-all" ''
          set -euo pipefail
          DIR="''${1:-.}"
          OUTDIR="''${2:-recordings}"
          mkdir -p "$OUTDIR"

          for f in "$DIR"/*.agda; do
            [ -f "$f" ] || continue
            ${agda-record}/bin/agda-record "$f" "$OUTDIR"
          done

          if [ -d "$DIR/Verification" ]; then
            for f in "$DIR"/Verification/*.agda; do
              [ -f "$f" ] || continue
              ${agda-record}/bin/agda-record "$f" "$OUTDIR"
            done
          fi

          # Combine witnesses
          cat "$OUTDIR"/*.witness.json > "$OUTDIR/all_witnesses.jsonl" 2>/dev/null || true
          ${zkperf-parse}/bin/zkperf-parse --combine < "$OUTDIR/all_witnesses.jsonl" \
            > "$OUTDIR/commitment.json" 2>/dev/null || true

          echo "=== All recorded ==="
          echo "Witnesses: $(wc -l < "$OUTDIR/all_witnesses.jsonl")"
          cat "$OUTDIR/commitment.json"
        '';

        checkAll = pkgs.runCommand "dashi-agda-check" {
          buildInputs = [ agdaWithStdlib ];
          src = ./.;
        } ''
          mkdir -p $out
          cd $src
          ok=0; fail=0
          for f in *.agda; do
            [ -f "$f" ] || continue
            if agda "$f" >> $out/check.log 2>&1; then
              ok=$((ok+1))
            else
              echo "FAIL: $f" >> $out/check.log
              fail=$((fail+1))
            fi
          done
          echo "$ok OK, $fail FAIL" | tee -a $out/check.log
        '';

      in {
        packages = {
          default = checkAll;
          check = checkAll;
          inherit agda-record agda-record-all;
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            agdaWithStdlib
            perf
            zkperf-parse
            agda-record
            agda-record-all
            pkgs.python3
          ];
          shellHook = ''
            echo "dashi_agda dev shell (with stdlib + zkperf)"
            echo "  agda MonsterGroups.agda              # check one proof"
            echo "  agda-record MonsterGroups.agda        # full perf record + symbols"
            echo "  agda-record-all . recordings/         # batch all proofs"
            echo "  nix build .#check                     # check all (sandboxed)"
          '';
        };
      }
    );
}
