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

        syntheticPackages =
          let
            hashes = {
              aarch64-darwin = {
                "4.20.1" = "sha256-5usI8QrBf4oH9LmYp+7A+SPEQmqnCZdHXhHQncJ3Vfo=";
              };
              aarch64-linux = {
                "4.20.1" = "sha256-G24XlAh5wLS81WllDEclEJ2+oKVNIKryj16uFCiontk=";
              };
              x86_64-darwin = {
                "4.20.1" = "";
              };
              x86_64-linux = {
                "4.20.1" = "sha256-xA48B8hzaqHEhuUloeR8GLD45LUCY4tPXH5+NXfADi8=";
              };
            };
          in
          pkgs.stdenv.mkDerivation {
            name = "syntheticPackages-4_20";
            outputHashAlgo = "sha256";
            outputHashMode = "recursive";
            outputHash = hashes.${system}."4.20.1";
            nativeBuildInputs = with pkgs; [
              cacert
            ];
            buildInputs = with pkgs; [
              curl
              git
              gnutar
              yj
              jq
              httpie
            ];
            src = builtins.path {
              path = ./.;
              name = "syntheticPackages-src";
              filter = path: type: baseNameOf path != ".lake";
            };
            buildPhase = ''
              mkdir -p $out
              export HOME=$(mktemp -d)
              ${lean-toolchain}/bin/lake exe cache get
              TGTS=$(cat lakefile.toml | yj -tj | jq -r '(.lean_lib,.lean_exe)[].name')
              echo "Targets are $TGTS"
              for TGT in $TGTS; do
                echo "Start building target $TGT..."
                ${lean-toolchain}/bin/lake -v --log-level=trace build $TGT;
                echo "Finished target $TGT"
              done
              echo "Start tar process"
              GZIP=-n tar --sort=name \
                --mtime="UTC 1970-01-01" \
                --owner=0 --group=0 --numeric-owner --format=gnu \
                -zcf $out/dotLake.tgz .lake
            '';
          };

        syntheticPackagesLn = pkgs.stdenv.mkDerivation {
          name = "syntheticPackagesLn-4_20";
          buildInputs = [ syntheticPackages pkgs.gnutar ];
          src = builtins.path {
            path = ./.;
            name = "syntheticPackagesLn-src";
            filter = path: type: false;
          };
          buildPhase = ''
            mkdir -p $out
            tar zxf ${syntheticPackages}/dotLake.tgz -C $out
          '';
        };

        genseqBin = pkgs.stdenv.mkDerivation {
          name = "genseqBin";
          nativeBuildInputs = [ pkgs.makeWrapper ];
          buildInputs = with pkgs; [
            lean-toolchain
            syntheticPackagesLn
            gnutar
            rsync
            git
          ];
          src = builtins.path {
            path = ./.;
            name = "genseq-src";
            filter = path: type: baseNameOf path != ".lake";
          };
          buildPhase = ''
            mkdir -p $out/{bin,lib}
            printf '[safe]\n  directory = *\n' > $TMPDIR/.gitconfig
            cat $TMPDIR/.gitconfig
            export GIT_CONFIG_GLOBAL=$TMPDIR/.gitconfig
            mkdir -p .lake
            ln -s ${syntheticPackagesLn}/.lake/packages .lake/packages
            ${lean-toolchain}/bin/lake build genseq
            rsync -a .lake/build/lib/lean $out/lib/
            cp .lake/build/bin/genseq $out/bin/genseq
            wrapProgram $out/bin/genseq \
              --set PATH "$PATH"
          '';
        };
        genseq = pkgs.stdenv.mkDerivation {
          name = "genseq";
          nativeBuildInputs = [ pkgs.makeWrapper ];
          src = ./.;
          phases = [
            "buildPhase"
          ];
          buildPhase = ''
            mkdir -p $out/bin
            LEAN_PATH=$(
              echo -n "${genseqBin}/lib/lean"
              for f in $(ls ${syntheticPackagesLn}/.lake/packages/); do
                echo -n ":${syntheticPackagesLn}/.lake/packages/$f/.lake/build/lib/lean";
              done
            )
            makeWrapper ${genseqBin}/bin/genseq $out/bin/genseq --set LEAN_PATH "$LEAN_PATH"
          '';
        };
        python = pkgs.python313.withPackages (ps: [ ps.supervisor ]);
      in
      {
        packages.default = genseq;
        packages.syntheticPackages = syntheticPackages;
        packages.syntheticPackagesLn = syntheticPackagesLn;

        devShell = shell {
          name = "gen-seq";
          buildInputs = with pkgs; [
            lean-toolchain
            elan
            go-task
            python
            findutils
            lsof
          ] ++ lib.optional stdenv.isDarwin apple-sdk_14;
        };
      }
    );
}
