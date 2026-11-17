{
  description = "dashi_agda — Monster group proofs with zkperf tracing";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    zkperf.url = "github:meta-introspector/zkperf";
    zkperf.inputs.nixpkgs.follows = "nixpkgs";
    dchottSrc = {
      url = "github:felixwellen/DCHoTT-Agda/ca8c755af0b26f8f50c5a60d3b7f9384a26f5d0e";
      flake = false;
    };
    cubicalSrc = {
      url = "github:agda/cubical/d0b9c7b0e9e4f816422c3447d7983b03274dd829";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, zkperf, dchottSrc, cubicalSrc }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        dchottPackageSrc = pkgs.runCommandLocal "dchott-agda-src" { } ''
          mkdir -p "$out/DCHoTT-Agda"
          cp -R ${dchottSrc}/. "$out/DCHoTT-Agda/"
          printf '%s\n' \
            'name: dchott-agda' \
            'include: DCHoTT-Agda' \
            > "$out/dchott-agda.agda-lib"
        '';
        dchottAgda = pkgs.agdaPackages.mkDerivation {
          pname = "dchott-agda";
          version = "ca8c755";
          src = dchottPackageSrc;
          libraryName = "dchott-agda";
          libraryFile = "dchott-agda.agda-lib";
          meta = {
            description = "Local Agda library wrapper for the DCHoTT-Agda submodule";
          };
          buildPhase = ''
            runHook preBuild
            agda -i DCHoTT-Agda DCHoTT-Agda/Im.agda
            agda -i DCHoTT-Agda DCHoTT-Agda/G-structure.agda
            runHook postBuild
          '';
          installPhase = ''
            runHook preInstall
            mkdir -p "$out"
            cp dchott-agda.agda-lib "$out/"
            cp -R DCHoTT-Agda "$out/"
            runHook postInstall
          '';
        };

        cubicalLocal = pkgs.agdaPackages.mkDerivation {
          pname = "cubical";
          version = "0.9-local";
          src = cubicalSrc;
          libraryName = "cubical-0.9";
          libraryFile = "cubical.agda-lib";
          meta = {
            description = "Local Agda Cubical library package from the cubical submodule";
          };
          nativeBuildInputs = [ pkgs.ghc pkgs.gnumake ];
          buildPhase = ''
            runHook preBuild
            make
            runHook postBuild
          '';
        };

        agdaWithDashiDeps = pkgs.agda.withPackages (p: [
          p.standard-library
          dchottAgda
          cubicalLocal
        ]);
        agdaArgs = "-i . -i DCHoTT-Agda -i cubical -l standard-library";
        perf = pkgs.perf;
        zkperfParse = zkperf.packages.${system}.default;

        dashiAgda = pkgs.agdaPackages.mkDerivation {
          pname = "dashi-agda";
          version = "local";
          src = ./.;
          libraryName = "dashi-agda";
          libraryFile = "dashi-agda.agda-lib";
          meta = {
            description = "DASHI Agda library with local DCHoTT and Cubical dependencies";
          };
          buildInputs = [
            pkgs.agdaPackages.standard-library
            dchottAgda
            cubicalLocal
          ];
          buildPhase = ''
            runHook preBuild
            cp -R ${dchottSrc}/. DCHoTT-Agda
            cp -R ${cubicalSrc}/. cubical
            rm -f dchott-agda.agda-lib
            agda ${agdaArgs} DASHI/Everything.agda
            runHook postBuild
          '';
        };

        authoritativeCheck = pkgs.runCommand "dashi-agda-authoritative-check" {
          buildInputs = [ agdaWithDashiDeps pkgs.glibcLocales ];
          src = ./.;
        } ''
          mkdir -p "$out"
          workdir="$TMPDIR/dashi-agda-authoritative"
          cp -R "$src" "$workdir"
          chmod -R u+w "$workdir"
          export HOME="$TMPDIR/home"
          mkdir -p "$HOME"
          export LOCALE_ARCHIVE="${pkgs.glibcLocales}/lib/locale/locale-archive"
          export LANG="C.UTF-8"
          export LC_ALL="C.UTF-8"
          cp -R ${dchottSrc}/. "$workdir/DCHoTT-Agda"
          cp -R ${cubicalSrc}/. "$workdir/cubical"
          cd "$workdir"
          rm -f dchott-agda.agda-lib
          agda ${agdaArgs} DASHI/Everything.agda \
            > "$out/check.log" 2>&1
          touch "$out/passed"
        '';

        mergeSmokeCheck = pkgs.runCommand "dashi-agda-merge-smoke" {
          buildInputs = [ agdaWithDashiDeps pkgs.bash pkgs.glibcLocales ];
          src = ./.;
        } ''
          mkdir -p "$out"
          workdir="$TMPDIR/dashi-agda-merge-smoke"
          cp -R "$src" "$workdir"
          chmod -R u+w "$workdir"
          export HOME="$TMPDIR/home"
          mkdir -p "$HOME"
          export LOCALE_ARCHIVE="${pkgs.glibcLocales}/lib/locale/locale-archive"
          export LANG="C.UTF-8"
          export LC_ALL="C.UTF-8"
          cd "$workdir"
          AGDA_BIN="${agdaWithDashiDeps}/bin/agda" \
          AGDA_ARGS="${agdaArgs}" \
            ${pkgs.bash}/bin/bash scripts/run_agda_merge_smoke.sh \
            > "$out/check.log" 2>&1
          touch "$out/passed"
        '';

        agdaRecord = pkgs.writeShellScriptBin "agda-record" ''
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
            -- ${agdaWithDashiDeps}/bin/agda ${agdaArgs} "$file" \
            2>"$outdir/$base.record.log" || true

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
            -- ${agdaWithDashiDeps}/bin/agda ${agdaArgs} "$file" \
            2>"$outdir/$base.stat.txt" || true

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
          default = dashiAgda;
          dashi-agda = dashiAgda;
          dchott-agda = dchottAgda;
          cubical = cubicalLocal;
          agda-with-dashi-deps = agdaWithDashiDeps;
          check = authoritativeCheck;
          merge-smoke = mergeSmokeCheck;
          inherit agdaRecord agdaRecordAll;
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            agdaWithDashiDeps
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
