{ pkgs }:
self: super:
with pkgs.haskell.lib;
with {
  hackage = metadata: with { hackage-id = "${metadata.name}-${metadata.version}"; };
    self.callCabal2nix metadata.name (builtins.fetchTarball {
      url = "http://hackage.haskell.org/package/${hackage-id}/${hackage-id}.tar.gz";
      inherit (metadata) sha256;
    }) {};
  github  = metadata: self.callCabal2nix metadata.repo (pkgs.fetchFromGitHub metadata) {};
  local   = metadata: self.callCabal2nix metadata.name (pkgs.lib.cleanSource metadata.path) {};
};
{ Agda = dontHaddock (dontCheck (github {
    repo   = "agda";
    owner  = "agda";
    rev    = "48c9d8fe35adca8c2e309bf64e99b26b25a90169"; # 2.6.0.1
    sha256 = "0sj6m75ikdc4adbqm0ladis18l09q92jv3sbcv1r0w7ja2i6z5fh";
  }));
}
