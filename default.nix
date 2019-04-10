let 
  pkgs = import <nixpkgs>{}; 
in 
{ stdenv ? pkgs.stdenv,
  coq ? pkgs.coq_8_8,
  gnumake ? pkgs.gnumake,
  coqPackages ? pkgs.coqPackages_8_8,
  ncurses ? pkgs.ncurses,
  which ? pkgs.which,
  graphviz ? pkgs.graphviz,
  fetchFromGitHub ? pkgs.fetchFromGitHub,
}:
  #let
    #inherit (coqPackages) autosubst;
    #in

let
  mkChicken' = self: coq:
    let callPackage = pkgs.newScope self ; in rec {
      inherit callPackage coq;
      coqPackages = self;
      camlp5 = pkgs.ocamlPackages.camlp5_6_strict;
      mathcomp = callPackage ./mathcomp.nix { };
    };
  mkChicken = coq: let self = mkChicken' self coq; in self;
  lecoq = mkChicken coq;
  mathcomp = lecoq.mathcomp;
in
stdenv.mkDerivation rec {
  name = "Thesis";
  version = "0.0.1";
  src = ./.;
  buildInputs = [ coq mathcomp ];
  buildTools = [ gnumake ];
}
