{
  description = "dashi_agda local merge-prep nix/zkperf surface";

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
          cd "$workdir"
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
          file="''${1:?Usage: agda-record <file.agda> [outdir]}"
          outdir="''${2:-recordings}"
          base="$(basename "$file" .agda)"
          mkdir -p "$outdir"

          echo "=== Recording $file ==="

          ${perf}/bin/perf record \
            -o "$outdir/$base.perf.data" \
            -g \
            --call-graph dwarf,65528 \
            --user-regs=AX,BX,CX,DX,SI,DI,BP,SP,IP,FLAGS,R8,R9,R10,R11,R12,R13,R14,R15 \
            -e cycles:u,instructions:u,cache-misses:u,branch-misses:u \
            -c 100 \
            -- ${agdaWithDashiDeps}/bin/agda ${agdaArgs} "$file" \
            2>"$outdir/$base.record.log" || true

          ${perf}/bin/perf report -i "$outdir/$base.perf.data" --stdio \
            > "$outdir/$base.report.txt" 2>&1 || true

          ${perf}/bin/perf script -i "$outdir/$base.perf.data" \
            -F comm,pid,tid,cpu,time,event,ip,sym,dso,symoff,srcline \
            > "$outdir/$base.script.txt" 2>&1 || true

          ${perf}/bin/perf annotate -i "$outdir/$base.perf.data" --stdio \
            > "$outdir/$base.annotate.txt" 2>&1 || true

          ${perf}/bin/perf stat \
            -e cycles,instructions,cache-misses,cache-references,branch-misses,branches \
            -- ${agdaWithDashiDeps}/bin/agda ${agdaArgs} "$file" \
            2>"$outdir/$base.stat.txt" || true

          ${zkperfParse}/bin/zkperf-parse "$outdir/$base.stat.txt" "$file" \
            > "$outdir/$base.witness.json" 2>/dev/null || true

          echo "=== $base recorded ==="
          ls -lh "$outdir/$base".*
        '';

        agdaRecordAll = pkgs.writeShellScriptBin "agda-record-all" ''
          set -euo pipefail
          outdir="''${1:-recordings}"
          mkdir -p "$outdir"

          while IFS= read -r file; do
            [ -n "$file" ] || continue
            ${agdaRecord}/bin/agda-record "$file" "$outdir"
          done < <(${pkgs.bash}/bin/bash scripts/list_merge_agda_targets.sh record)

          mapfile -t witness_files < <(
            find "$outdir" -maxdepth 1 -type f -name '*.witness.json' | LC_ALL=C sort
          )

          if [ "''${#witness_files[@]}" -gt 0 ]; then
            cat "''${witness_files[@]}" > "$outdir/all_witnesses.jsonl"
            ${zkperfParse}/bin/zkperf-parse --combine < "$outdir/all_witnesses.jsonl" \
              > "$outdir/commitment.json" 2>/dev/null || true
          else
            : > "$outdir/all_witnesses.jsonl"
            printf '{}\n' > "$outdir/commitment.json"
          fi

          echo "=== All recorded ==="
          echo "Witnesses: $(wc -l < "$outdir/all_witnesses.jsonl")"
          cat "$outdir/commitment.json"
        '';
      in {
        checks = {
          authoritative = authoritativeCheck;
          merge-smoke = mergeSmokeCheck;
        };

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
            zkperfParse
            agdaRecord
            agdaRecordAll
            pkgs.bash
            pkgs.python3
          ];
          shellHook = ''
            echo "dashi_agda dev shell"
            echo "  nix build .#check        # authoritative DASHI/Everything check"
            echo "  nix build .#merge-smoke  # recursive merge-prep smoke check"
            echo "  agda-record <file.agda>"
            echo "  agda-record-all [outdir]"
          '';
        };
      }
    );
}
