{ compiler ? "ghc865", nixpkgs ? (import nix/nixpkgs.nix { inherit compiler; })}:
nixpkgs.stdenv.mkDerivation {
  name = "agda-env";
  buildInputs = [
    (nixpkgs.haskell.packages.${compiler}.ghcWithPackages (pkgs: [ pkgs.ieee754 ]))
  ];
}
