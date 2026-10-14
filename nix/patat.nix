{
  lib,
  rocqPackages,
  fetchFromGitHub
}:
rocqPackages.mkRocqDerivation rec {
  pname = "patat";
  version = "dev";

  src = fetchFromGitHub {
    owner = "kacperFKorban";
    repo = pname;
    rev = "7c14e71c67e915539b94b7c3248c3e0e7980c712";
    hash = "sha256-XMfK5vSKPLnOhrNcB1NbG2HVjo1XqaSwfDgjONzw+WI=";
  };

  opam-name = pname;
  useDune = true;
}
