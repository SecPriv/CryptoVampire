{ stdenv, cryptovampire }:
stdenv.mkDerivation rec {
  name = "cryptovampire's documentation";
  src = cryptovampire.src;
  patches = [ "${src}/nix.patch" ];

  buildInputs = cryptovampire.buildInputs;
  nativeBuildInputs = cryptovampire.nativeBuildInputs;

  buildPhase = ''
    mkdir -p $out/target
    cargo doc --document-private-items --target-dir $out/target
  '';

  installPhase = ''
    mv $out/target/build/dir/doc $out/doc
  '';

  fixupPhase = ''
    rm -rf $out/target
  '';
}
