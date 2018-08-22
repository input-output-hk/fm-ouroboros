{ nixpkgs ? import <nixpkgs> { }, ghc ? nixpkgs.ghc }:

with nixpkgs;

haskell.lib.buildStackProject {
    name = "Ouroboros";
    buildInputs = [ pkgconfig zlib ncurses5 cairo ];
    inherit ghc;
}
