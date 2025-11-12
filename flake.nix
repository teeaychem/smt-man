{
    description = "smt-man flake";

    inputs = {
        nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    };

    outputs = { self,
                nixpkgs,
                ...
              }@inputs:

    let
    inherit (self) outputs;

    forAllSystems = nixpkgs.lib.genAttrs [
      "x86_64-linux"
      "aarch64-darwin"
    ];
  in {
    devShells = forAllSystems (
      system: let
        pkgs = nixpkgs.legacyPackages.${system};
      in {
        default = pkgs.mkShell {
          nativeBuildInputs = [
            pkgs.clang-tools
            pkgs.clang
            pkgs.cmake
            pkgs.libpng
            pkgs.sdl3
            pkgs.pkg-config
          ];
          buildInputs = [
            # Required by Criterion
            pkgs.boxfort.dev
            pkgs.libffi.dev
            pkgs.libgit2.dev
            pkgs.pcre2.dev
            pkgs.nanomsg
            pkgs.criterion.dev
          ];
        };
      }
    );
  };
}

