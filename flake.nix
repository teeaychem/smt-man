{
  description = "smt-man flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-25.05";
  };

  outputs =
    {
      self,
      nixpkgs,
      ...
    }@inputs:

    let
      inherit (self) outputs;

      forAllSystems = nixpkgs.lib.genAttrs [
        "x86_64-linux"
        "aarch64-darwin"
      ];
    in
    {
      devShells = forAllSystems (
        system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
          default = pkgs.mkShell {
            packages = [
              pkgs.clang-tools
              pkgs.clang
              pkgs.cmake
              pkgs.criterion
              pkgs.cvc5
              pkgs.doxygen
              pkgs.libpng
              pkgs.sdl3
              pkgs.pkg-config
              pkgs.z3
            ];
          };

          gcc = pkgs.mkShell.override { stdenv = pkgs.gccStdenv; } {
            packages = [
              pkgs.clang-tools
              pkgs.cmake
              pkgs.criterion
              pkgs.cvc5
              pkgs.gcc
              pkgs.doxygen
              pkgs.libpng
              pkgs.sdl3
              pkgs.pkg-config
              pkgs.z3
            ];
          };
        }
      );
    };
}
