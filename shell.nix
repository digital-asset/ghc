let
  nixpkgs = builtins.fetchTarball {
    url = https://github.com/NixOS/nixpkgs/archive/22dc22f8cedc58fcb11afe1acb08e9999e78be9c.tar.gz;
    sha256 = "0bkkc0054ayk41xhm3k39lgy9riljxk9l80p68afycadj0czvmwz";
  };
  pkgs = import nixpkgs {};
in
pkgs.mkShell {
  buildInputs = with pkgs; [
    autoconf
    automake
    cabal-install
    gmp
    git
    haskell.packages.ghc865Binary.ghc
    haskellPackages.alex
    haskellPackages.happy_1_19_12
    m4
    ncurses
    perl
    python3
  ];
}
