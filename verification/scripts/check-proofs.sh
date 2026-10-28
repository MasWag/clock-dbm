#!/usr/bin/env bash
# Usage: check-proofs.sh [verif-dir]   (see check-proofs.py)
here="$(cd "$(dirname "$0")" && pwd)"
exec python3 -I "$here/check-proofs.py" "${1:-verif}"
