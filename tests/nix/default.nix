{ stdenv, vampire, z3, cvc5, cryptovampire, file, name }:
stdenv.mkDerivation {
  inherit name;
  src = ./.;
  doCheck = true;
  checkPhase = ''
    mkdir -p $out
    ${cryptovampire}/bin/cryptovampire '${file}' auto \
      --solver-file-debug $out \
      --vampire-location '${vampire}/bin/vampire' \
      --z3-location '${z3}/bin/z3' \
      --cvc5-location '${cvc5}/bin/cvc5'
  '';
}
