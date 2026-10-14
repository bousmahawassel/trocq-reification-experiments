{
  lib,
  rocqPackages,
  trocq,
  patat,
  coqutil,
}:

rocqPackages.mkRocqDerivation {
  pname = "impbootExp";
  version = "dev";

  src = ../.;

  propagatedBuildInputs = [
    rocqPackages.stdlib
    trocq
    patat
    coqutil
  ];

  opam-name = "impbootExp";

}
