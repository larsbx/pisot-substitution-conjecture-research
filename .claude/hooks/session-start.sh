#!/bin/bash
# Provision a Claude Code on the web container for the repository gates:
# Python oracles and pytest (as CI does), and the pinned Mojo toolchain.
set -euo pipefail

[ "${CLAUDE_CODE_REMOTE:-}" = "true" ] || exit 0
cd "$CLAUDE_PROJECT_DIR"

python3 -m pip install -q -e '.[dev]'

PIXI_BIN="$HOME/.pixi/bin"
command -v "$PIXI_BIN/pixi" >/dev/null 2>&1 ||
    curl --retry 5 --retry-all-errors --retry-delay 3 -fsSL https://pixi.sh/install.sh | bash
(cd mojo && "$PIXI_BIN/pixi" install)

# The pip-installed pytest (with pypdf) must shadow any preinstalled tool copy.
echo "export PATH=\"$(python3 -c 'import sysconfig; print(sysconfig.get_path("scripts"))'):$PIXI_BIN:\$PATH\"" >> "$CLAUDE_ENV_FILE"
