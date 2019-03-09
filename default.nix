let 
  pkgs = import <nixpkgs>{}; 
in 
{ stdenv ? pkgs.stdenv,
  coq ? pkgs.coq_8_8,
  gnumake ? pkgs.gnumake,
  coqPackages ? pkgs.coqPackages_8_8 }:
  #let
    #inherit (coqPackages) autosubst;
    #in
stdenv.mkDerivation rec {
  name = "Thesis";
  version = "0.0.1";
  src = ./.;
  buildInputs = [ coq coqPackages.mathcomp ];
  buildTools = [ gnumake ];
}
