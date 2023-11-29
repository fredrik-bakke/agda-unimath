{
  description = "agda-unimath";

  inputs = {
    # Unstable is needed for Agda 2.6.4, latest stable 23.05 only has 2.6.3
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    # Nixpkgs with tested versions of mdbook crates;
    # may be removed once we backport new mdbook assets to our
    # modified versions
    nixpkgs-mdbook.url = "github:NixOS/nixpkgs?rev=7fdd1421774a52277fb56d64b26aaf7765e1b3fa";
    mdbook-catppuccin = {
      url = "github:catppuccin/mdBook/v1.2.0";
      inputs.nixpkgs.follows = "nixpkgs-mdbook";
    };
  };

  outputs = { self, nixpkgs, nixpkgs-mdbook, flake-utils, mdbook-catppuccin }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = nixpkgs.legacyPackages."${system}";
          pkgs-mdbook = nixpkgs-mdbook.legacyPackages."${system}";
          python = pkgs.python38.withPackages (p: with p; [
            # Keep in sync with scripts/requirements.txt
            # pre-commit <- not installed as a Python package but as a binary below
            requests
            tomli
          ]);

          agda-unimath-package = { lib, mkDerivation, time }: mkDerivation {
            pname = "agda-unimath";

            # For the version format of unreleased packages, see
            # https://nixos.org/manual/nixpkgs/stable/#sec-package-naming
            version = "unstable-2023-09-05";

            # We can reference the directory since we're using flakes,
            # which copies the version-tracked files into the nix store
            # before evaluation, # so we don't run into the issue with
            # non-reproducible source paths as outlined here:
            # https://nix.dev/recipes/best-practices#reproducible-source-paths
            src = ./.;

            nativeBuildInputs = [ time ];

            buildPhase = ''
              runHook preBuild
              make check
              runHook postBuild
            '';

            meta = with lib; {
              description = "Univalent mathematics in Agda";
              homepage = "https://github.com/UniMath/agda-unimath";
              license = licenses.mit;
              platforms = platforms.unix;
            };
          };
        in
        {
          packages.agda-unimath = pkgs.agdaPackages.callPackage agda-unimath-package { };
          packages.default = self.packages."${system}".agda-unimath;

          devShells.default = pkgs.mkShell {
            name = "agda-unimath";

            # Dependencies for building the library
            inputsFrom = [ self.packages."${system}".agda-unimath ];

            # Development tools
            packages = [
              # maintanance scripts
              python
              # pre-commit checks
              pkgs.pre-commit
            ] ++ (with pkgs-mdbook; [
              # working on the website
              mdbook
              mdbook-katex
              mdbook-pagetoc
              mdbook-linkcheck
              mdbook-catppuccin.packages."${system}".default
            ]);
          };
        });
}
