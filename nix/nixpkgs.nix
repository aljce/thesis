{ compiler ? "ghc865" }:
with rec {
  fetchNixpkgs = import ./fetchNixpkgs.nix;
  nixpkgs = fetchNixpkgs {
    owner  = "NixOS";
    repo   = "nixpkgs";
    rev    = "56d94c8c69f8cac518027d191e2f8de678b56088"; # 19.03
    sha256 = "1c812ssgmnmh97sarmp8jcykk0g57m8rsbfjg9ql9996ig6crsmi";
  };
 overlay = import ./overlay.nix { inherit compiler; };
};
import nixpkgs {
  config = {
    allowUnfree = true;
  };
  overlays = [ overlay ];
}
