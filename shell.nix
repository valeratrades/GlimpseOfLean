{
  pkgs ? import <nixpkgs> { },
}:
pkgs.mkShellNoCC {
  shellHook = ''
		elan override set 4.13.0
  '';
}
