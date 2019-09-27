{ compiler ? "ghc865", nixpkgs ? (import ./nixpkgs.nix { inherit compiler; }) }:
nixpkgs.haskell.packages.${compiler}.Agda
