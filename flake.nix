{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";
    shell-utils.url = "github:waltermoreira/shell-utils";
    lean-toolchain-nix.url = "github:provables/lean-toolchain-nix";
  };
  outputs = { self, nixpkgs, flake-utils, shell-utils, lean-toolchain-nix }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        shell = shell-utils.myShell.${system};
        lean-toolchain = lean-toolchain-nix.packages.${system}.lean-toolchain-4_20;

        genseqBin =
          let
            hashes = {
              "aarch64-darwin" = "sha256-0QMRET3AWUHwRVRD5UsoFnNfLi7I6guGfVIs2z0t/aA=";
              "aarch64-linux" = "sha256-i7mq9xycmjMdbmH3HocgehLx2xFOIA51ZFwApTd2LIw=";
              "x86_64-darwin" = "sha256-cTrmKhFCuERWN7FU2cRgsNyY7eCgafTlhmzcbhd+qLg=";
              "x86_64-linux" = "sha256-XV2lXQIdxV1qwUb4s7DHKBVYQeWtdSCrBT0DatNxhRk=";
            };
          in
          pkgs.stdenv.mkDerivation {
            __structuredAttrs = true;
            unsafeDiscardReferences.out = true;
            name = "genseqBin";
            nativeBuildInputs = [ pkgs.makeWrapper pkgs.cacert ];
            outputHashAlgo = "sha256";
            outputHashMode = "recursive";
            outputHash = hashes.${system};
            buildInputs = with pkgs; [
              lean-toolchain
              gnutar
              rsync
              git
              curl
              findutils
              gzip
            ];
            src = builtins.path {
              path = ./.;
              name = "genseq-src";
              filter = path: type: baseNameOf path != ".lake";
            };
            buildPhase = ''
              mkdir -p $out/{bin,lib/packages}
              export HOME=$(mktemp -d)
              lake exe cache get
              lake build genseq
              cp .lake/build/bin/genseq $out/bin/genseq
              rsync -a .lake/build/lib/lean $out/lib/
              rsync -a .lake/packages/ $out/lib/packages/
              find $out/lib -type f ! -name "*.olean" -delete
              find $out/lib -depth -type d -empty -delete
            '';
            dontFixup = true;
          };
        genseq = pkgs.stdenv.mkDerivation {
          name = "genseq";
          nativeBuildInputs = [ pkgs.makeWrapper ];
          buildInputs = [ lean-toolchain ];
          src = ./.;
          phases = [
            "buildPhase"
          ];
          buildPhase = ''
            mkdir -p $out/bin
            LEAN_PATH=$(
              echo -n "${genseqBin}/lib/lean"
              for f in $(ls ${genseqBin}/lib/packages/); do
                echo -n ":${genseqBin}/lib/packages/$f/.lake/build/lib/lean";
              done
            )
            makeWrapper ${genseqBin}/bin/genseq $out/bin/genseq \
              --set LEAN_PATH "$LEAN_PATH" \
              --set PATH "$PATH"
          '';
        };
        python = pkgs.python313.withPackages (ps: [ ps.supervisor ]);
        supervisedGenseq = pkgs.writeShellApplication {
          name = "genseq";
          runtimeInputs = [ python genseq pkgs.getopt pkgs.gnused ];
          text = ''
            args=$(getopt -o "vhp:s" -l "version,help,port:,supervise" -- "$@")
            eval set -- "$args"
            supervise=""
            port="8000"
            while true
            do
            case "$1" in
            -h|--help)
              ${genseq}/bin/genseq -h
              exit 0
              ;;
            -v|--version)
              ${genseq}/bin/genseq --version
              exit 0
              ;;
            -p|--port)
              shift
              port="$1"
              ;;
            -s|--supervise)
              supervise="1"
              ;;
            --)
              break
              ;;
            esac
            shift
            done
            if [ -z "$supervise" ]; then
              ${genseq}/bin/genseq -p "$port"
            else
              echo "Starting supervised 'genseq' on port $port" | \
                ${pkgs.boxes}/bin/boxes -d shell -p h2v1
              if supervisorctl status genseq >/dev/null 2>&1
              then
                echo "genseq already running"
                exit 0
              fi
              config=$(mktemp)
              sed "s/PORT/$port/" < ${./supervisord.conf.template} > "$config"
              supervisord -n -c "$config"
            fi
          '';
        };
      in
      {
        packages = {
          default = supervisedGenseq;
          genseq = supervisedGenseq;
        };

        devShell = shell {
          name = "gen-seq";
          buildInputs = with pkgs; [
            lean-toolchain
            elan
            go-task
            python
            findutils
            lsof
            supervisedGenseq
          ] ++ lib.optional stdenv.isDarwin apple-sdk_14;
        };
      }
    );
}
