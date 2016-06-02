{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation {
  name = "inox-buildenv";

  buildInputs = with pkgs; [ haskellPackages.BNFC ];
}
