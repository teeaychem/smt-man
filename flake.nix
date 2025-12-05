{
  description = "smt-man flake";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-25.11";
  };
  outputs =
    {
      self,
      nixpkgs,
    }:
    let
      lib = nixpkgs.lib;
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
    in
    {
      devShells = lib.genAttrs systems (
        system:
        let
          pkgs = import nixpkgs {
            inherit system;
          };
        in
        {
          default = pkgs.mkShell {
            buildInputs = [
              pkgs.criterion
              pkgs.doxygen
              pkgs.glib
              pkgs.libpng
              pkgs.sdl3
              pkgs.z3
            ];

            packages = [
              pkgs.clang-tools
              pkgs.cmake
              pkgs.pkg-config
            ];
          };
        }
      );
    };
}
