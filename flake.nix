{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";
    shell-utils.url = "github:waltermoreira/shell-utils";
    lean-toolchain-nix.url = "github:provables/lean-toolchain-nix";
  };
  outputs = { nixpkgs, flake-utils, shell-utils, lean-toolchain-nix, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        shell = shell-utils.myShell.${system};
        lean-toolchain = lean-toolchain-nix.packages.${system}.lean-toolchain-4_20;

        genseqBin =
          let
            hashes = {
              "aarch64-darwin" = "sha256-plKbyDSOFpuVkukkIsJM8O75GKQoNe/JbAP4BaQLAYw=";
              "aarch64-linux" = "";
              "x86_64-darwin" = "";
              "x86_64-linux" = "sha256-rIUzbqp/k/sVJD/nqObSJZKKx9LE5CpifnBBlE1eJHc=";
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
              --set PATH "$PATH" \
              --set OEIS_CODOMAINS "${./keywords.json}"
          '';
        };
        python = pkgs.python313.withPackages (ps: [ ps.supervisor ps.ipython ]);
        
        sGenseq = pkgs.writeShellApplication {
          name = "sgenseq";
          runtimeInputs = with pkgs; [
            python
            genseq
            gnused
          ];
          text = ''
            supervisor=$(python -c 'import socket; s=socket.socket(); s.bind(("", 0)); print(s.getsockname()[1]); s.close()')
            port=$(python -c 'import socket; s=socket.socket(); s.bind(("", 0)); print(s.getsockname()[1]); s.close()')
            config=$(mktemp -d)
            printf "#!${pkgs.stdenv.shell}\n${python}/bin/supervisorctl -c %s \"\$@\"" \
              "$config/supervisor.conf" > "$config/supervisorctl"
            chmod +x "$config/supervisorctl"
            sed -e "s/PORT/$port/" -e "s/SUPERVISOR/$supervisor/" \
                < ${./supervisord.conf.template} > "$config/supervisor.conf"
            supervisord -c "$config/supervisor.conf"
            echo "$port $config/supervisorctl"
          '';
        };

        supervisedGenseq = pkgs.writeShellApplication {
          name = "genseq";
          runtimeInputs = with pkgs; [
            python
            genseq
            getopt
            gnused
            lsof
            netcat
          ];
          text = ''
            do_kill () {
              supervisorctl stop all
              supervisorctl shutdown
            }
            do_wait () {
              while true; do 
                if nc -z -w1 localhost "$1" >/dev/null 2>&1; then break; fi
                sleep 1
              done
            }
            args=$(getopt -o "vhp:swnk" -l "version,help,port:,supervise,wait,foreground,kill" -- "$@")
            eval set -- "$args"
            supervise=""
            foreground=""
            wait=""
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
            -n|--foreground)
              foreground="-n"
              ;;
            -k|--kill)
              do_kill
              exit 0
              ;;
            -w|--wait)
              wait="1"
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
              sed -e "s/PORT/$port/" -e "s/SUPERVISOR/9001/" \
                < ${./supervisord.conf.template} > "$config"
              supervisord $foreground -c "$config"
              if [[ ( -z "$foreground" ) && ( -n "$wait" ) ]]; then
                echo -n "Waiting for server to be responsive... "
                do_wait "$port"
                echo "done"
              fi
            fi
          '';
        };
      in
      {
        packages = {
          default = supervisedGenseq;
          genseq = supervisedGenseq;
          sgenseq = sGenseq;
        };

        devShell = shell {
          name = "gen-seq";
          buildInputs = with pkgs; [
            lean-toolchain
            elan
            go-task
            python
            uv
            findutils
            lsof
            supervisedGenseq
          ] ++ lib.optional stdenv.isDarwin apple-sdk_14;
        };
      }
    );
}
