{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    devenv.url = "github:cachix/devenv";
		lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs = inputs@{ flake-parts, nixpkgs, devenv, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
			imports = [
        devenv.flakeModule
      ];

      systems = nixpkgs.lib.systems.flakeExposed;

      perSystem = { config, self', inputs', pkgs, system, ... }: 
			#TODO: remove or get lean4-nix working
        let
					pkgs = import nixpkgs {
						inherit system;
						overlays = [ (inputs.lean4-nix.readToolchainFile ./lean-toolchain) ];
					};
        in
        {
					devenv.shells.default = {
						languages.lean4 = {
							enable = true;
							package = pkgs.lean4;
						};

						enterShell = ''
						#TODO: have it build stuff
					lean --version
					'';
					};
				};
    };
}
