{
  lib,
  rocqPackages,
  fetchFromGitHub
}:
rocqPackages.mkRocqDerivation rec {
  pname = "coqutil";
  version = "dev";

  src = fetchFromGitHub {
    owner = "mit-plv";
    repo = pname;
    rev = "2cf510214b6d56a3065b092789b0c8455ae2c263";
    hash = "sha256-iB69Mkz+kyci7QCL2yF8GLNhUszZrkmLYBrQoPxobG4=";
  };

  propagatedBuildInputs = [
    rocqPackages.stdlib
    rocqPackages.coq
    rocqPackages.rocq-core.ocamlPackages.ocaml
  ];

  opam-name = "coq-coqutil";
  useCoq = true;
}
