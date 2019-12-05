let 
  pkgs = import <nixpkgs>{}; 
in 
{ stdenv ? pkgs.stdenv,
  coq ? pkgs.coq_8_9,
  gnumake ? pkgs.gnumake,
  coqPackages ? pkgs.coqPackages_8_9,
  mathcomp ? coqPackages.mathcomp,
  ncurses ? pkgs.ncurses,
  which ? pkgs.which,
  graphviz ? pkgs.graphviz,
}:

stdenv.mkDerivation rec {
  name = "Thesis";
  version = "0.0.1";
  src = ./.;
  buildInputs = [ coq mathcomp ];
  buildTools = [ gnumake ];
}
