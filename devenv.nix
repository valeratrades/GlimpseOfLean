{ pkgs, lib, ... }:
let
  buildInputs = with pkgs; [
  #  libuv
		#openssl.dev
		#openssl
		#pkg-config
		#mold-wrapped
  #  zlib
  ];
in 
{
  env = { LD_LIBRARY_PATH = "${lib.makeLibraryPath buildInputs}"; };

  languages.lean4 = {
    enable = true;
  };
	stdenv = pkgs.stdenvAdapters.useMoldLinker pkgs.stdenv;

	enterShell = ''
	'';
}

