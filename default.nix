# default.nix
{ system ? builtins.currentSystem }:
(import ./reflex-platform { inherit system; }).project ({ pkgs, ... }: {
  useWarp = true;

  packages = {
    core = ./core;
    webui = ./webui;
  };

  shells = {
    ghc = ["core" "webui"];
    ghcjs = ["core" "webui"];
  };

  overrides = self: super: {
     bytes = pkgs.haskell.lib.dontCheck super.bytes;
     bound = pkgs.haskell.lib.dontCheck super.bound;
  };
})
