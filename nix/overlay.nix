{ compiler }:
self: super:
with  {
  overlay = import ./overrides.nix { pkgs = super; };
};
{ haskell = super.haskell // {
    packages = super.haskell.packages // {
      ${compiler} = (super.haskell.packages.${compiler}.override {
        overrides = super.lib.composeExtensions
          (super.haskell.packageOverrides or (self: super: {}))
          overlay;
      });
    };
  };
}
