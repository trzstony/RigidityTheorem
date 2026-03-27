#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "$0")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
blueprint_dir="$repo_root/RigidityTheorem/blueprint"
blueprint_src_dir="$blueprint_dir/src"
blueprint_web_dir="$blueprint_dir/web"
blueprint_print_dir="$blueprint_dir/print"
lean_decls_file="$blueprint_dir/lean_decls"

build_pdf() {
  mkdir -p "$blueprint_print_dir"
  (
    cd "$blueprint_src_dir"
    latexmk -output-directory=../print print.tex
  )
}

build_web() {
  mkdir -p "$blueprint_web_dir"
  (
    cd "$blueprint_src_dir"
    plastex -c plastex.cfg web.tex
  )
}

serve_web() {
  if [ ! -d "$blueprint_web_dir" ]; then
    echo "Blueprint web output not found at $blueprint_web_dir" >&2
    echo "Run '$0 build-web' first." >&2
    exit 1
  fi
  (
    cd "$blueprint_web_dir"
    python3 -m http.server 8000
  )
}

check_decls() {
  if [ ! -f "$lean_decls_file" ]; then
    echo "Blueprint declaration list not found at $lean_decls_file" >&2
    echo "Run '$0 build-web' first so plasTeX can generate it." >&2
    exit 1
  fi
  (
    cd "$repo_root"
    lake build
    lake exe checkdecls RigidityTheorem/blueprint/lean_decls
  )
}

if [ "${#}" -lt 1 ]; then
  echo "Usage: $0 {build-pdf|build-web|serve|checkdecls|all}" >&2
  exit 1
fi

case "$1" in
  build-pdf)
    build_pdf
    ;;
  build-web)
    build_web
    ;;
  serve)
    serve_web
    ;;
  checkdecls)
    check_decls
    ;;
  all)
    build_pdf
    build_web
    check_decls
    ;;
  *)
    echo "Unknown command: $1" >&2
    echo "Usage: $0 {build-pdf|build-web|serve|checkdecls|all}" >&2
    exit 1
    ;;
esac
