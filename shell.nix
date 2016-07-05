{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation {
  name = "inox-buildenv";

  buildInputs = with pkgs.haskellPackages; [
    BNFC
    alex
    happy
  ];

  shellHook = ''
    echo -e '\n\n\tBuild Inox with `make`\n\n'
  '';
}
