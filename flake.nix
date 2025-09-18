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
              "x86_64-darwin" = "";
              "x86_64-linux" = "";
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
          name = "supervised-genseq";
          runtimeInputs = [ python genseq ];
          text = ''
            if supervisorctl status genseq >/dev/null 2>&1
            then
              echo "genseq already running"
              exit 0
            fi
            supervisord -n -c ${./supervisord.conf}
          '';
        };
      in
      {
        packages = {
          default = genseq;
          inherit genseq supervisedGenseq;
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
            genseq
            supervisedGenseq
          ] ++ lib.optional stdenv.isDarwin apple-sdk_14;
        };
      }
    );
}
